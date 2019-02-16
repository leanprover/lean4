// Lean compiler output
// Module: init.lean.parser.command
// Imports: init.lean.parser.declaration
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
obj* l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_combinators_any__of___at_lean_parser_command_universe_parser___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_section_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_variables_parser___closed__1;
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6___closed__1;
obj* l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_check_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_check_parser(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_reserve__mixfix_parser_lean_parser_has__tokens;
obj* l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_command_init__quot_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_variables;
obj* l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__1(obj*);
obj* l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__1(obj*);
obj* l_list_map___main___rarg(obj*, obj*);
obj* l_lean_parser_command_omit_has__view_x_27;
obj* l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_namespace_parser___closed__1;
obj* l_lean_parser_command_check_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_omit_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_set__option_parser___closed__1;
extern obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_command_init__quot_has__view_x_27;
obj* l_reader__t_orelse___at_lean_parser_command__parser_run___spec__4(obj*);
obj* l_lean_parser_term_bracketed__binders_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_attribute_has__view;
extern obj* l_lean_parser_combinators_many___rarg___closed__1;
obj* l_lean_parser_command_open__spec_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_end_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_universes;
obj* l_lean_parser_command_open_has__view_x_27___lambda__1(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__5;
obj* l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_universe_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_open_parser___closed__1;
obj* l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_export_has__view;
obj* l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_init__quot_has__view;
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_rec__t_run___at_lean_parser_command__parser_run___spec__9(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_open_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_variable;
obj* l_lean_parser_command_variables_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_open;
obj* l_lean_parser_string__lit_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_combinators_sep__by1_tokens___rarg(obj*, obj*);
extern obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
extern obj* l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_list_cons_tokens___rarg(obj*, obj*);
obj* l_lean_parser_command_set__option_parser(obj*, obj*, obj*, obj*);
obj* l_reader__t_orelse___at_lean_parser_command__parser_run___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_namespace_parser_lean_parser_has__tokens;
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
extern obj* l_lean_parser_command__parser__m_monad__except___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_open__spec_parser_lean_parser_has__view;
obj* l_lean_parser_command_universes_has__view;
obj* l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_open__spec_as_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_attribute_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_bool__option__value_has__view_x_27;
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_command_include_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_open_has__view;
obj* l_lean_parser_command_init__quot_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_open__spec_renaming_item_has__view_x_27;
obj* l_lean_parser_command_open__spec_only;
obj* l_lean_parser_command_check_parser_lean_parser_has__view;
obj* l_lean_parser_command_export_has__view_x_27;
obj* l_lean_parser_command_open__spec_as_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_set__option;
obj* l_string_quote(obj*);
obj* l_lean_parser_command_attribute_has__view_x_27;
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_command__parser_run___spec__10(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_variable_has__view;
obj* l_lean_parser_command_universes_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_universe_has__view_x_27;
obj* l_lean_parser_command_end_parser___closed__1;
extern obj* l_lean_parser_command__parser__m_monad___closed__1;
obj* l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_command_parser_lean_parser_has__view;
obj* l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_open__spec_as;
obj* l_lean_parser_command_init__quot_parser___closed__1;
extern obj* l_lean_parser_string__lit_has__view;
obj* l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_open__spec_as_has__view_x_27;
obj* l_lean_parser_command_open__spec_renaming_has__view_x_27;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__8(obj*);
obj* l_lean_parser_command_universe_has__view;
extern obj* l_lean_parser_term_binder_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_set__option_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_open__spec_has__view_x_27;
obj* l_lean_parser_command_open__spec_only_has__view_x_27;
obj* l_lean_parser_command_variable_has__view_x_27___lambda__1(obj*);
extern obj* l_lean_parser_command_notation_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_include_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_omit_parser___closed__1;
obj* l_lean_parser_command__parser_run___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_universe_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_include;
obj* l_lean_parser_command_parser___rarg___closed__1;
obj* l_lean_parser_command_section_has__view_x_27;
extern obj* l_lean_parser_term_binder__content_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command__parser__m_alternative___closed__1;
obj* l_lean_parser_command_open__spec_only_has__view;
obj* l_lean_parser_command_section_parser___closed__1;
obj* l_lean_parser_command_open__spec_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_variables_has__view;
obj* l_lean_parser_combinators_label_view___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_include_parser(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_number_parser___at_lean_parser_command_notation__spec_precedence__lit_parser_lean_parser_has__tokens___spec__1___rarg___closed__1;
obj* l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(obj*);
obj* l_lean_parser_command_option__value_has__view_x_27;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__4___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_set__option_parser_lean_parser_has__view;
obj* l_lean_parser_command_mixfix_parser(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
extern obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_command_universes_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_include_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_end_has__view_x_27___lambda__2(obj*);
obj* l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_parser_command_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_section_has__view;
obj* l_list_join___main___rarg(obj*);
obj* l_lean_parser_command_namespace_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_end_has__view_x_27;
extern obj* l_lean_parser_number_has__view;
obj* l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
obj* l_lean_parser_command_open_has__view_x_27;
obj* l_lean_parser_command_universes_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_section_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_option__value_has__view_x_27___lambda__2(obj*);
obj* l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_open__spec_renaming_item_has__view;
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_lean_parser_command_parser_lean_parser_has__tokens;
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_parser_command_option__value_has__view;
extern obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_parser_combinators_many1_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_binder_has__view;
obj* l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_open_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_variables_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_end_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_open__spec_only_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_namespace_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_check_parser___closed__1;
obj* l_lean_parser_symbol_tokens___rarg(obj*, obj*);
extern obj* l_lean_parser_term_bracketed__binders_has__view;
obj* l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__4(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_parser_command_open__spec_renaming_item;
obj* l_lean_parser_command_open__spec_renaming_has__view;
extern obj* l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
obj* l___private_init_lean_parser_combinators_3__sep__by_view__aux___main___at_lean_parser_command_attribute_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_command_check_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_open__spec;
obj* l_lean_parser_command_check_has__view_x_27;
obj* l_lean_parser_command_bool__option__value_has__view;
obj* l_lean_parser_command_attribute;
obj* l_lean_parser_term_binder_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__3(obj*);
obj* l_lean_parser_command__parser_run(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_universe_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_open__spec_hiding_has__view;
obj* l_lean_parser_command_variable_has__view_x_27;
obj* l_lean_parser_command_option__value_has__view_x_27___lambda__1(obj*);
extern obj* l_lean_parser_finish__comment__block___closed__2;
obj* l_lean_parser_command_end_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_universe_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_open__spec_renaming;
obj* l_lean_parser_command_open__spec_has__view;
extern obj* l_string_join___closed__1;
obj* l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_command_include_has__view_x_27___lambda__1(obj*);
obj* l_reader__t_orelse___at_lean_parser_command_universe_parser___spec__2(obj*);
extern obj* l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
obj* l_lean_parser_command_check_has__view;
obj* l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_open__spec_as_has__view;
obj* l_lean_parser_command_universe_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_command_open__spec_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_reserve__mixfix_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_export_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_parser_number_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_open__spec_only_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_end;
obj* l_lean_parser_command_variable_parser___closed__1;
obj* l_lean_parser_command_set__option_has__view_x_27;
obj* l_lean_parser_command_option__value;
obj* l_lean_parser_command_include_parser___closed__1;
obj* l_lean_parser_command_bool__option__value;
obj* l_lean_parser_combinators_recurse_view___rarg(obj*, obj*);
obj* l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_omit_has__view;
obj* l_lean_parser_command_variable_parser_lean_parser_has__tokens;
obj* l_lean_parser_token(obj*, obj*, obj*);
obj* l_lean_parser_command_attribute_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_set__option_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_open_has__view_x_27___lambda__2___closed__1;
extern obj* l_lean_parser_term_parser_lean_parser_has__tokens___closed__1;
obj* l_lean_parser_command_omit_has__view_x_27___lambda__2(obj*);
extern obj* l_lean_parser_term_bracketed__binders_parser_lean_parser_has__tokens;
obj* l_lean_parser_symbol__or__ident___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_attribute_parser_lean_parser_has__view;
obj* l_lean_parser_term_parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_variable_has__view_x_27___lambda__2(obj*);
extern obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__3(obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_namespace_has__view;
extern obj* l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
obj* l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_substring_to__string(obj*);
obj* l_lean_parser_try__view___at_lean_parser_string__lit_parser___spec__1(obj*);
obj* l_lean_parser_command_namespace_has__view_x_27___lambda__1(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_parser_command_bool__option__value_has__view_x_27___lambda__2(obj*);
obj* l_reader__t_lift___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__8___rarg(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_lean_parser_command_namespace_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_section;
extern obj* l_lean_parser_command_attr__instance_has__view;
obj* l_lean_parser_command_open__spec_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_export_parser___closed__1;
obj* l_lean_parser_string__lit_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_export_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_variable_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_universe;
obj* l_lean_parser_combinators_any__of___at_lean_parser_command__parser_run___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_section_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_attribute_has__view_x_27___lambda__1___closed__1;
namespace lean {
obj* string_iterator_remaining(obj*);
}
obj* l_lean_parser_command_include_has__view_x_27;
obj* l_lean_parser_command_section_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_open__spec_hiding_has__view_x_27;
obj* l_lean_parser_command_attribute_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_open__spec_parser___closed__1;
obj* l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_builtin__command__parsers;
obj* l_string_trim(obj*);
extern obj* l_lean_parser_command_declaration_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_attr__instance_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_notation_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_set__option_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_term__parser_run(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_mixfix_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
obj* l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_variables_has__view_x_27;
obj* l_lean_parser_command_end_has__view;
obj* l_lean_parser_command_universes_has__view_x_27;
extern obj* l_lean_parser_command__parser__m_lean_parser_monad__rec___closed__1;
obj* l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
extern obj* l_lean_parser_string__lit_parser___at_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens___spec__1___rarg___closed__1;
obj* l_lean_parser_command_open__spec_hiding;
obj* l_lean_parser_command_parser(obj*);
extern obj* l_lean_parser_command_attr__instance_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_init__quot;
obj* l_lean_parser_command_open__spec_as_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_variables_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_declaration_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_reserve__notation_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_export_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_init__quot_parser_lean_parser_has__view;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__8___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_init__quot_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_namespace_has__view_x_27;
obj* l_lean_parser_command_parser___rarg(obj*, obj*, obj*);
obj* l_lean_parser_command_include_has__view;
obj* l_lean_parser_command_namespace;
obj* l_lean_parser_command_open__spec_only_has__view_x_27___lambda__1___closed__1;
obj* l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_command_attribute_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_omit_parser_lean_parser_has__tokens;
extern obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_command_variables_has__view_x_27___lambda__1(obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
extern obj* l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_command_omit;
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_parser_command_omit_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_universe_parser___closed__1;
obj* l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_omit_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_attribute_parser___closed__1;
extern obj* l_lean_parser_combinators_any__of___rarg___closed__1;
obj* l_lean_parser_command_section_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_command_open_has__view_x_27___lambda__2(obj*);
obj* l_list_foldl___main___at_lean_parser_command_universe_parser___spec__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_command_end_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__1___closed__1;
obj* l_list_map___main___at_lean_parser_command__parser_run___spec__1(obj*, obj*);
obj* l_lean_parser_command_check;
obj* l_list_foldl___main___at_lean_parser_command__parser_run___spec__5(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parser__core__t___at_lean_parser_command__parser_run___spec__7;
extern obj* l_lean_parser_command_reserve__notation_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_export_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_export;
obj* l_reader__t_orelse___at_lean_parser_command_universe_parser___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_command_set__option_has__view;
extern obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
obj* l_lean_parser_rec__t_recurse___at_lean_parser_command_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_4 = lean::apply_3(x_1, x_0, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_10);
x_12 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_5);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_7);
return x_13;
}
}
obj* _init_l_lean_parser_command_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; 
x_0 = lean::box(0);
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_command_parser_lean_parser_has__view___spec__1), 4, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__8___rarg), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_lean_parser_command__parser__m_lean_parser_monad__rec___closed__1;
lean::inc(x_4);
x_6 = l_lean_parser_combinators_recurse_view___rarg(x_0, x_4);
x_7 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_8 = l_lean_parser_command__parser__m_alternative___closed__1;
x_9 = lean::mk_string("command");
lean::inc(x_8);
lean::inc(x_7);
x_12 = l_lean_parser_combinators_label_view___rarg(x_7, x_8, x_3, x_9, x_6);
return x_12;
}
}
obj* _init_l_lean_parser_command_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_lean_parser_tokens___rarg(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("command");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_command_parser___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_3 = lean::box(0);
x_4 = l_lean_parser_rec__t_recurse___at_lean_parser_command_parser_lean_parser_has__view___spec__1(x_3, x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
x_10 = l_lean_parser_command_parser___rarg___closed__1;
lean::inc(x_10);
x_12 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_5, x_10);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_7);
return x_13;
}
}
obj* l_lean_parser_command_parser(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_parser___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_lean_parser_command_open__spec_as() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("open_spec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("as");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_lean_parser_command_open__spec_as_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_14; obj* x_16; 
lean::dec(x_0);
x_14 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
switch (lean::obj_tag(x_17)) {
case 1:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_20);
return x_23;
}
default:
{
obj* x_25; obj* x_27; 
lean::dec(x_17);
x_25 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_5);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
}
}
}
}
}
}
obj* l_lean_parser_command_open__spec_as_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_open__spec_as_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
}
lbl_21:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_29; obj* x_31; 
lean::dec(x_1);
x_29 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_20);
lean::cnstr_set(x_31, 1, x_29);
return x_31;
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
lean::dec(x_1);
switch (lean::obj_tag(x_32)) {
case 1:
{
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
lean::dec(x_32);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_20);
lean::cnstr_set(x_38, 1, x_35);
return x_38;
}
default:
{
obj* x_40; obj* x_42; 
lean::dec(x_32);
x_40 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_20);
lean::cnstr_set(x_42, 1, x_40);
return x_42;
}
}
}
}
}
}
}
obj* l_lean_parser_command_open__spec_as_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_3);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_10);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_lean_parser_command_open__spec_as;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
}
obj* _init_l_lean_parser_command_open__spec_as_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_as_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_as_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_open__spec_as_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_open__spec_as_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_open__spec_only() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("open_spec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("only");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
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
x_8 = l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__1(x_5);
switch (lean::obj_tag(x_3)) {
case 1:
{
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
default:
{
obj* x_14; obj* x_16; 
lean::dec(x_3);
x_14 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_14);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_lean_parser_command_open__spec_only_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_13 = x_0;
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::dec(x_0);
x_13 = x_19;
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_22; 
switch (lean::obj_tag(x_14)) {
case 1:
{
obj* x_24; 
x_24 = lean::cnstr_get(x_14, 0);
lean::inc(x_24);
lean::dec(x_14);
x_22 = x_24;
goto lbl_23;
}
default:
{
obj* x_28; 
lean::dec(x_14);
x_28 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_28);
x_22 = x_28;
goto lbl_23;
}
}
lbl_23:
{
obj* x_30; obj* x_31; 
if (lean::obj_tag(x_13) == 0)
{
obj* x_33; 
x_33 = lean::box(3);
x_30 = x_13;
x_31 = x_33;
goto lbl_32;
}
else
{
obj* x_34; obj* x_36; 
x_34 = lean::cnstr_get(x_13, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_13, 1);
lean::inc(x_36);
lean::dec(x_13);
x_30 = x_36;
x_31 = x_34;
goto lbl_32;
}
lbl_32:
{
obj* x_39; 
x_39 = l_lean_parser_syntax_as__node___main(x_31);
if (lean::obj_tag(x_39) == 0)
{
lean::dec(x_39);
if (lean::obj_tag(x_30) == 0)
{
obj* x_42; obj* x_43; obj* x_45; 
lean::dec(x_30);
x_42 = lean::box(0);
x_43 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_45, 0, x_5);
lean::cnstr_set(x_45, 1, x_22);
lean::cnstr_set(x_45, 2, x_43);
lean::cnstr_set(x_45, 3, x_42);
return x_45;
}
else
{
obj* x_46; 
x_46 = lean::cnstr_get(x_30, 0);
lean::inc(x_46);
lean::dec(x_30);
switch (lean::obj_tag(x_46)) {
case 0:
{
obj* x_49; obj* x_52; obj* x_53; obj* x_55; 
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
lean::dec(x_46);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_49);
x_53 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_53);
x_55 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_55, 0, x_5);
lean::cnstr_set(x_55, 1, x_22);
lean::cnstr_set(x_55, 2, x_53);
lean::cnstr_set(x_55, 3, x_52);
return x_55;
}
default:
{
obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_46);
x_57 = lean::box(0);
x_58 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_60, 0, x_5);
lean::cnstr_set(x_60, 1, x_22);
lean::cnstr_set(x_60, 2, x_58);
lean::cnstr_set(x_60, 3, x_57);
return x_60;
}
}
}
}
else
{
obj* x_61; obj* x_63; obj* x_64; obj* x_67; 
x_61 = lean::cnstr_get(x_39, 0);
lean::inc(x_61);
if (lean::is_shared(x_39)) {
 lean::dec(x_39);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_39, 0);
 x_63 = x_39;
}
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__1(x_64);
if (lean::obj_tag(x_30) == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_63);
lean::dec(x_30);
x_70 = lean::box(0);
x_71 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_71, 0, x_5);
lean::cnstr_set(x_71, 1, x_22);
lean::cnstr_set(x_71, 2, x_67);
lean::cnstr_set(x_71, 3, x_70);
return x_71;
}
else
{
obj* x_72; 
x_72 = lean::cnstr_get(x_30, 0);
lean::inc(x_72);
lean::dec(x_30);
switch (lean::obj_tag(x_72)) {
case 0:
{
obj* x_75; obj* x_78; obj* x_79; 
x_75 = lean::cnstr_get(x_72, 0);
lean::inc(x_75);
lean::dec(x_72);
if (lean::is_scalar(x_63)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_63;
}
lean::cnstr_set(x_78, 0, x_75);
x_79 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_79, 0, x_5);
lean::cnstr_set(x_79, 1, x_22);
lean::cnstr_set(x_79, 2, x_67);
lean::cnstr_set(x_79, 3, x_78);
return x_79;
}
default:
{
obj* x_82; obj* x_83; 
lean::dec(x_63);
lean::dec(x_72);
x_82 = lean::box(0);
x_83 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_83, 0, x_5);
lean::cnstr_set(x_83, 1, x_22);
lean::cnstr_set(x_83, 2, x_67);
lean::cnstr_set(x_83, 3, x_82);
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
obj* l_lean_parser_command_open__spec_only_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_open__spec_only_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
else
{
obj* x_20; obj* x_22; obj* x_25; 
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_25 = l_lean_parser_syntax_as__node___main(x_20);
if (lean::obj_tag(x_25) == 0)
{
lean::dec(x_25);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; 
x_27 = lean::box(3);
x_1 = x_22;
x_2 = x_27;
goto lbl_3;
}
else
{
obj* x_28; obj* x_30; 
x_28 = lean::cnstr_get(x_22, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_22, 1);
lean::inc(x_30);
lean::dec(x_22);
x_1 = x_30;
x_2 = x_28;
goto lbl_3;
}
}
else
{
obj* x_33; obj* x_36; obj* x_39; 
x_33 = lean::cnstr_get(x_25, 0);
lean::inc(x_33);
lean::dec(x_25);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_list_append___rarg(x_36, x_22);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; 
x_40 = lean::box(3);
x_1 = x_39;
x_2 = x_40;
goto lbl_3;
}
else
{
obj* x_41; obj* x_43; 
x_41 = lean::cnstr_get(x_39, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_39, 1);
lean::inc(x_43);
lean::dec(x_39);
x_1 = x_43;
x_2 = x_41;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_46; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_48; obj* x_51; 
x_48 = lean::cnstr_get(x_2, 0);
lean::inc(x_48);
lean::dec(x_2);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_48);
x_46 = x_51;
goto lbl_47;
}
default:
{
obj* x_53; 
lean::dec(x_2);
x_53 = lean::box(0);
x_46 = x_53;
goto lbl_47;
}
}
lbl_47:
{
obj* x_54; obj* x_55; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_57; 
x_57 = lean::box(3);
x_54 = x_1;
x_55 = x_57;
goto lbl_56;
}
else
{
obj* x_58; obj* x_60; 
x_58 = lean::cnstr_get(x_1, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_1, 1);
lean::inc(x_60);
lean::dec(x_1);
x_54 = x_60;
x_55 = x_58;
goto lbl_56;
}
lbl_56:
{
obj* x_63; 
switch (lean::obj_tag(x_55)) {
case 1:
{
obj* x_65; 
x_65 = lean::cnstr_get(x_55, 0);
lean::inc(x_65);
lean::dec(x_55);
x_63 = x_65;
goto lbl_64;
}
default:
{
obj* x_69; 
lean::dec(x_55);
x_69 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_69);
x_63 = x_69;
goto lbl_64;
}
}
lbl_64:
{
obj* x_71; obj* x_72; 
if (lean::obj_tag(x_54) == 0)
{
obj* x_74; 
x_74 = lean::box(3);
x_71 = x_54;
x_72 = x_74;
goto lbl_73;
}
else
{
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_54, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_54, 1);
lean::inc(x_77);
lean::dec(x_54);
x_71 = x_77;
x_72 = x_75;
goto lbl_73;
}
lbl_73:
{
obj* x_80; 
x_80 = l_lean_parser_syntax_as__node___main(x_72);
if (lean::obj_tag(x_80) == 0)
{
lean::dec(x_80);
if (lean::obj_tag(x_71) == 0)
{
obj* x_83; obj* x_84; obj* x_86; 
lean::dec(x_71);
x_83 = lean::box(0);
x_84 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_84);
x_86 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_86, 0, x_46);
lean::cnstr_set(x_86, 1, x_63);
lean::cnstr_set(x_86, 2, x_84);
lean::cnstr_set(x_86, 3, x_83);
return x_86;
}
else
{
obj* x_87; 
x_87 = lean::cnstr_get(x_71, 0);
lean::inc(x_87);
lean::dec(x_71);
switch (lean::obj_tag(x_87)) {
case 0:
{
obj* x_90; obj* x_93; obj* x_94; obj* x_96; 
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
lean::dec(x_87);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_90);
x_94 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_94);
x_96 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_96, 0, x_46);
lean::cnstr_set(x_96, 1, x_63);
lean::cnstr_set(x_96, 2, x_94);
lean::cnstr_set(x_96, 3, x_93);
return x_96;
}
default:
{
obj* x_98; obj* x_99; obj* x_101; 
lean::dec(x_87);
x_98 = lean::box(0);
x_99 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_99);
x_101 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_101, 0, x_46);
lean::cnstr_set(x_101, 1, x_63);
lean::cnstr_set(x_101, 2, x_99);
lean::cnstr_set(x_101, 3, x_98);
return x_101;
}
}
}
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_108; 
x_102 = lean::cnstr_get(x_80, 0);
lean::inc(x_102);
if (lean::is_shared(x_80)) {
 lean::dec(x_80);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_80, 0);
 x_104 = x_80;
}
x_105 = lean::cnstr_get(x_102, 1);
lean::inc(x_105);
lean::dec(x_102);
x_108 = l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__1(x_105);
if (lean::obj_tag(x_71) == 0)
{
obj* x_111; obj* x_112; 
lean::dec(x_71);
lean::dec(x_104);
x_111 = lean::box(0);
x_112 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_112, 0, x_46);
lean::cnstr_set(x_112, 1, x_63);
lean::cnstr_set(x_112, 2, x_108);
lean::cnstr_set(x_112, 3, x_111);
return x_112;
}
else
{
obj* x_113; 
x_113 = lean::cnstr_get(x_71, 0);
lean::inc(x_113);
lean::dec(x_71);
switch (lean::obj_tag(x_113)) {
case 0:
{
obj* x_116; obj* x_119; obj* x_120; 
x_116 = lean::cnstr_get(x_113, 0);
lean::inc(x_116);
lean::dec(x_113);
if (lean::is_scalar(x_104)) {
 x_119 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_119 = x_104;
}
lean::cnstr_set(x_119, 0, x_116);
x_120 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_120, 0, x_46);
lean::cnstr_set(x_120, 1, x_63);
lean::cnstr_set(x_120, 2, x_108);
lean::cnstr_set(x_120, 3, x_119);
return x_120;
}
default:
{
obj* x_123; obj* x_124; 
lean::dec(x_113);
lean::dec(x_104);
x_123 = lean::box(0);
x_124 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_124, 0, x_46);
lean::cnstr_set(x_124, 1, x_63);
lean::cnstr_set(x_124, 2, x_108);
lean::cnstr_set(x_124, 3, x_123);
return x_124;
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
obj* l_lean_parser_command_open__spec_only_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_10);
x_12 = l_option_map___rarg(x_10, x_1);
x_13 = lean::box(3);
lean::inc(x_13);
x_15 = l_option_get__or__else___main___rarg(x_12, x_13);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_3);
x_17 = lean::box(0);
lean::inc(x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_parser_no__kind;
lean::inc(x_21);
x_23 = l_lean_parser_syntax_mk__node(x_21, x_20);
x_24 = l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__2(x_5);
lean::inc(x_21);
x_26 = l_lean_parser_syntax_mk__node(x_21, x_24);
lean::inc(x_10);
x_28 = l_option_map___rarg(x_10, x_7);
x_29 = l_option_get__or__else___main___rarg(x_28, x_13);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_17);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_26);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_23);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_lean_parser_command_open__spec_only;
lean::inc(x_33);
x_35 = l_lean_parser_syntax_mk__node(x_33, x_32);
return x_35;
}
}
obj* _init_l_lean_parser_command_open__spec_only_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_only_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_only_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_open__spec_only_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_open__spec_only_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_open__spec_renaming_item() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("open_spec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("renaming");
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean::mk_string("item");
x_12 = lean_name_mk_string(x_10, x_11);
return x_12;
}
}
obj* _init_l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_7; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_5 = x_7;
goto lbl_6;
}
default:
{
obj* x_11; 
lean::dec(x_1);
x_11 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_11);
x_5 = x_11;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_13 = x_0;
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::dec(x_0);
x_13 = x_19;
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_22; 
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_14, 0);
lean::inc(x_24);
lean::dec(x_14);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
x_22 = x_27;
goto lbl_23;
}
default:
{
obj* x_29; 
lean::dec(x_14);
x_29 = lean::box(0);
x_22 = x_29;
goto lbl_23;
}
}
lbl_23:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_31; obj* x_33; 
lean::dec(x_13);
x_31 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_31);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_5);
lean::cnstr_set(x_33, 1, x_22);
lean::cnstr_set(x_33, 2, x_31);
return x_33;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_13, 0);
lean::inc(x_34);
lean::dec(x_13);
switch (lean::obj_tag(x_34)) {
case 1:
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
lean::dec(x_34);
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_5);
lean::cnstr_set(x_40, 1, x_22);
lean::cnstr_set(x_40, 2, x_37);
return x_40;
}
default:
{
obj* x_42; obj* x_44; 
lean::dec(x_34);
x_42 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_42);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_5);
lean::cnstr_set(x_44, 1, x_22);
lean::cnstr_set(x_44, 2, x_42);
return x_44;
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_22; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_20 = x_22;
goto lbl_21;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_26);
x_20 = x_26;
goto lbl_21;
}
}
lbl_21:
{
obj* x_28; obj* x_29; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_31; 
x_31 = lean::box(3);
x_28 = x_1;
x_29 = x_31;
goto lbl_30;
}
else
{
obj* x_32; obj* x_34; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_1, 1);
lean::inc(x_34);
lean::dec(x_1);
x_28 = x_34;
x_29 = x_32;
goto lbl_30;
}
lbl_30:
{
obj* x_37; 
switch (lean::obj_tag(x_29)) {
case 0:
{
obj* x_39; obj* x_42; 
x_39 = lean::cnstr_get(x_29, 0);
lean::inc(x_39);
lean::dec(x_29);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
x_37 = x_42;
goto lbl_38;
}
default:
{
obj* x_44; 
lean::dec(x_29);
x_44 = lean::box(0);
x_37 = x_44;
goto lbl_38;
}
}
lbl_38:
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_46; obj* x_48; 
lean::dec(x_28);
x_46 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_46);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_20);
lean::cnstr_set(x_48, 1, x_37);
lean::cnstr_set(x_48, 2, x_46);
return x_48;
}
else
{
obj* x_49; 
x_49 = lean::cnstr_get(x_28, 0);
lean::inc(x_49);
lean::dec(x_28);
switch (lean::obj_tag(x_49)) {
case 1:
{
obj* x_52; obj* x_55; 
x_52 = lean::cnstr_get(x_49, 0);
lean::inc(x_52);
lean::dec(x_49);
x_55 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_55, 0, x_20);
lean::cnstr_set(x_55, 1, x_37);
lean::cnstr_set(x_55, 2, x_52);
return x_55;
}
default:
{
obj* x_57; obj* x_59; 
lean::dec(x_49);
x_57 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_20);
lean::cnstr_set(x_59, 1, x_37);
lean::cnstr_set(x_59, 2, x_57);
return x_59;
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_1);
x_9 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_9);
x_11 = l_option_map___rarg(x_9, x_3);
x_12 = lean::box(3);
x_13 = l_option_get__or__else___main___rarg(x_11, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_5);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_8);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_lean_parser_command_open__spec_renaming_item;
lean::inc(x_19);
x_21 = l_lean_parser_syntax_mk__node(x_19, x_18);
return x_21;
}
}
obj* _init_l_lean_parser_command_open__spec_renaming_item_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_open__spec_renaming_item_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_open__spec_renaming_item_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_open__spec_renaming() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("open_spec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("renaming");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_lean_parser_command_open__spec_renaming_item_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_open__spec_renaming_item_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_13 = x_0;
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::dec(x_0);
x_13 = x_19;
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_22; 
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_14, 0);
lean::inc(x_24);
lean::dec(x_14);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
x_22 = x_27;
goto lbl_23;
}
default:
{
obj* x_29; 
lean::dec(x_14);
x_29 = lean::box(0);
x_22 = x_29;
goto lbl_23;
}
}
lbl_23:
{
obj* x_30; obj* x_31; 
if (lean::obj_tag(x_13) == 0)
{
obj* x_33; 
x_33 = lean::box(3);
x_30 = x_13;
x_31 = x_33;
goto lbl_32;
}
else
{
obj* x_34; obj* x_36; 
x_34 = lean::cnstr_get(x_13, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_13, 1);
lean::inc(x_36);
lean::dec(x_13);
x_30 = x_36;
x_31 = x_34;
goto lbl_32;
}
lbl_32:
{
obj* x_39; 
x_39 = l_lean_parser_syntax_as__node___main(x_31);
if (lean::obj_tag(x_39) == 0)
{
lean::dec(x_39);
if (lean::obj_tag(x_30) == 0)
{
obj* x_42; obj* x_43; obj* x_45; 
lean::dec(x_30);
x_42 = lean::box(0);
x_43 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_45, 0, x_5);
lean::cnstr_set(x_45, 1, x_22);
lean::cnstr_set(x_45, 2, x_43);
lean::cnstr_set(x_45, 3, x_42);
return x_45;
}
else
{
obj* x_46; 
x_46 = lean::cnstr_get(x_30, 0);
lean::inc(x_46);
lean::dec(x_30);
switch (lean::obj_tag(x_46)) {
case 0:
{
obj* x_49; obj* x_52; obj* x_53; obj* x_55; 
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
lean::dec(x_46);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_49);
x_53 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_53);
x_55 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_55, 0, x_5);
lean::cnstr_set(x_55, 1, x_22);
lean::cnstr_set(x_55, 2, x_53);
lean::cnstr_set(x_55, 3, x_52);
return x_55;
}
default:
{
obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_46);
x_57 = lean::box(0);
x_58 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_60, 0, x_5);
lean::cnstr_set(x_60, 1, x_22);
lean::cnstr_set(x_60, 2, x_58);
lean::cnstr_set(x_60, 3, x_57);
return x_60;
}
}
}
}
else
{
obj* x_61; obj* x_63; obj* x_64; obj* x_67; obj* x_69; 
x_61 = lean::cnstr_get(x_39, 0);
lean::inc(x_61);
if (lean::is_shared(x_39)) {
 lean::dec(x_39);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_39, 0);
 x_63 = x_39;
}
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__2;
lean::inc(x_67);
x_69 = l_list_map___main___rarg(x_67, x_64);
if (lean::obj_tag(x_30) == 0)
{
obj* x_72; obj* x_73; 
lean::dec(x_63);
lean::dec(x_30);
x_72 = lean::box(0);
x_73 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_73, 0, x_5);
lean::cnstr_set(x_73, 1, x_22);
lean::cnstr_set(x_73, 2, x_69);
lean::cnstr_set(x_73, 3, x_72);
return x_73;
}
else
{
obj* x_74; 
x_74 = lean::cnstr_get(x_30, 0);
lean::inc(x_74);
lean::dec(x_30);
switch (lean::obj_tag(x_74)) {
case 0:
{
obj* x_77; obj* x_80; obj* x_81; 
x_77 = lean::cnstr_get(x_74, 0);
lean::inc(x_77);
lean::dec(x_74);
if (lean::is_scalar(x_63)) {
 x_80 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_80 = x_63;
}
lean::cnstr_set(x_80, 0, x_77);
x_81 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_81, 0, x_5);
lean::cnstr_set(x_81, 1, x_22);
lean::cnstr_set(x_81, 2, x_69);
lean::cnstr_set(x_81, 3, x_80);
return x_81;
}
default:
{
obj* x_84; obj* x_85; 
lean::dec(x_63);
lean::dec(x_74);
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_85, 0, x_5);
lean::cnstr_set(x_85, 1, x_22);
lean::cnstr_set(x_85, 2, x_69);
lean::cnstr_set(x_85, 3, x_84);
return x_85;
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
obj* l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__3;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
else
{
obj* x_20; obj* x_22; obj* x_25; 
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_25 = l_lean_parser_syntax_as__node___main(x_20);
if (lean::obj_tag(x_25) == 0)
{
lean::dec(x_25);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; 
x_27 = lean::box(3);
x_1 = x_22;
x_2 = x_27;
goto lbl_3;
}
else
{
obj* x_28; obj* x_30; 
x_28 = lean::cnstr_get(x_22, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_22, 1);
lean::inc(x_30);
lean::dec(x_22);
x_1 = x_30;
x_2 = x_28;
goto lbl_3;
}
}
else
{
obj* x_33; obj* x_36; obj* x_39; 
x_33 = lean::cnstr_get(x_25, 0);
lean::inc(x_33);
lean::dec(x_25);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_list_append___rarg(x_36, x_22);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; 
x_40 = lean::box(3);
x_1 = x_39;
x_2 = x_40;
goto lbl_3;
}
else
{
obj* x_41; obj* x_43; 
x_41 = lean::cnstr_get(x_39, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_39, 1);
lean::inc(x_43);
lean::dec(x_39);
x_1 = x_43;
x_2 = x_41;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_46; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_48; obj* x_51; 
x_48 = lean::cnstr_get(x_2, 0);
lean::inc(x_48);
lean::dec(x_2);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_48);
x_46 = x_51;
goto lbl_47;
}
default:
{
obj* x_53; 
lean::dec(x_2);
x_53 = lean::box(0);
x_46 = x_53;
goto lbl_47;
}
}
lbl_47:
{
obj* x_54; obj* x_55; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_57; 
x_57 = lean::box(3);
x_54 = x_1;
x_55 = x_57;
goto lbl_56;
}
else
{
obj* x_58; obj* x_60; 
x_58 = lean::cnstr_get(x_1, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_1, 1);
lean::inc(x_60);
lean::dec(x_1);
x_54 = x_60;
x_55 = x_58;
goto lbl_56;
}
lbl_56:
{
obj* x_63; 
switch (lean::obj_tag(x_55)) {
case 0:
{
obj* x_65; obj* x_68; 
x_65 = lean::cnstr_get(x_55, 0);
lean::inc(x_65);
lean::dec(x_55);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_65);
x_63 = x_68;
goto lbl_64;
}
default:
{
obj* x_70; 
lean::dec(x_55);
x_70 = lean::box(0);
x_63 = x_70;
goto lbl_64;
}
}
lbl_64:
{
obj* x_71; obj* x_72; 
if (lean::obj_tag(x_54) == 0)
{
obj* x_74; 
x_74 = lean::box(3);
x_71 = x_54;
x_72 = x_74;
goto lbl_73;
}
else
{
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_54, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_54, 1);
lean::inc(x_77);
lean::dec(x_54);
x_71 = x_77;
x_72 = x_75;
goto lbl_73;
}
lbl_73:
{
obj* x_80; 
x_80 = l_lean_parser_syntax_as__node___main(x_72);
if (lean::obj_tag(x_80) == 0)
{
lean::dec(x_80);
if (lean::obj_tag(x_71) == 0)
{
obj* x_83; obj* x_84; obj* x_86; 
lean::dec(x_71);
x_83 = lean::box(0);
x_84 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_84);
x_86 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_86, 0, x_46);
lean::cnstr_set(x_86, 1, x_63);
lean::cnstr_set(x_86, 2, x_84);
lean::cnstr_set(x_86, 3, x_83);
return x_86;
}
else
{
obj* x_87; 
x_87 = lean::cnstr_get(x_71, 0);
lean::inc(x_87);
lean::dec(x_71);
switch (lean::obj_tag(x_87)) {
case 0:
{
obj* x_90; obj* x_93; obj* x_94; obj* x_96; 
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
lean::dec(x_87);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_90);
x_94 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_94);
x_96 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_96, 0, x_46);
lean::cnstr_set(x_96, 1, x_63);
lean::cnstr_set(x_96, 2, x_94);
lean::cnstr_set(x_96, 3, x_93);
return x_96;
}
default:
{
obj* x_98; obj* x_99; obj* x_101; 
lean::dec(x_87);
x_98 = lean::box(0);
x_99 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_99);
x_101 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_101, 0, x_46);
lean::cnstr_set(x_101, 1, x_63);
lean::cnstr_set(x_101, 2, x_99);
lean::cnstr_set(x_101, 3, x_98);
return x_101;
}
}
}
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_108; obj* x_110; 
x_102 = lean::cnstr_get(x_80, 0);
lean::inc(x_102);
if (lean::is_shared(x_80)) {
 lean::dec(x_80);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_80, 0);
 x_104 = x_80;
}
x_105 = lean::cnstr_get(x_102, 1);
lean::inc(x_105);
lean::dec(x_102);
x_108 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__2;
lean::inc(x_108);
x_110 = l_list_map___main___rarg(x_108, x_105);
if (lean::obj_tag(x_71) == 0)
{
obj* x_113; obj* x_114; 
lean::dec(x_71);
lean::dec(x_104);
x_113 = lean::box(0);
x_114 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_114, 0, x_46);
lean::cnstr_set(x_114, 1, x_63);
lean::cnstr_set(x_114, 2, x_110);
lean::cnstr_set(x_114, 3, x_113);
return x_114;
}
else
{
obj* x_115; 
x_115 = lean::cnstr_get(x_71, 0);
lean::inc(x_115);
lean::dec(x_71);
switch (lean::obj_tag(x_115)) {
case 0:
{
obj* x_118; obj* x_121; obj* x_122; 
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
lean::dec(x_115);
if (lean::is_scalar(x_104)) {
 x_121 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_121 = x_104;
}
lean::cnstr_set(x_121, 0, x_118);
x_122 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_122, 0, x_46);
lean::cnstr_set(x_122, 1, x_63);
lean::cnstr_set(x_122, 2, x_110);
lean::cnstr_set(x_122, 3, x_121);
return x_122;
}
default:
{
obj* x_125; obj* x_126; 
lean::dec(x_104);
lean::dec(x_115);
x_125 = lean::box(0);
x_126 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_126, 0, x_46);
lean::cnstr_set(x_126, 1, x_63);
lean::cnstr_set(x_126, 2, x_110);
lean::cnstr_set(x_126, 3, x_125);
return x_126;
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
obj* _init_l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_open__spec_renaming_item_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_40; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_10);
x_12 = l_option_map___rarg(x_10, x_1);
x_13 = lean::box(3);
lean::inc(x_13);
x_15 = l_option_get__or__else___main___rarg(x_12, x_13);
lean::inc(x_10);
x_17 = l_option_map___rarg(x_10, x_3);
lean::inc(x_13);
x_19 = l_option_get__or__else___main___rarg(x_17, x_13);
x_20 = lean::box(0);
lean::inc(x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_20);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_15);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_lean_parser_no__kind;
lean::inc(x_24);
x_26 = l_lean_parser_syntax_mk__node(x_24, x_23);
x_27 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__2___closed__1;
lean::inc(x_27);
x_29 = l_list_map___main___rarg(x_27, x_5);
lean::inc(x_24);
x_31 = l_lean_parser_syntax_mk__node(x_24, x_29);
lean::inc(x_10);
x_33 = l_option_map___rarg(x_10, x_7);
x_34 = l_option_get__or__else___main___rarg(x_33, x_13);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_20);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_31);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_26);
lean::cnstr_set(x_37, 1, x_36);
x_38 = l_lean_parser_command_open__spec_renaming;
lean::inc(x_38);
x_40 = l_lean_parser_syntax_mk__node(x_38, x_37);
return x_40;
}
}
obj* _init_l_lean_parser_command_open__spec_renaming_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_open__spec_renaming_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_open__spec_renaming_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_open__spec_hiding() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("open_spec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("hiding");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
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
x_8 = l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__1(x_5);
switch (lean::obj_tag(x_3)) {
case 1:
{
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
default:
{
obj* x_14; obj* x_16; 
lean::dec(x_3);
x_14 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_14);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_13 = x_0;
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::dec(x_0);
x_13 = x_19;
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_22; 
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_14, 0);
lean::inc(x_24);
lean::dec(x_14);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
x_22 = x_27;
goto lbl_23;
}
default:
{
obj* x_29; 
lean::dec(x_14);
x_29 = lean::box(0);
x_22 = x_29;
goto lbl_23;
}
}
lbl_23:
{
obj* x_30; obj* x_31; 
if (lean::obj_tag(x_13) == 0)
{
obj* x_33; 
x_33 = lean::box(3);
x_30 = x_13;
x_31 = x_33;
goto lbl_32;
}
else
{
obj* x_34; obj* x_36; 
x_34 = lean::cnstr_get(x_13, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_13, 1);
lean::inc(x_36);
lean::dec(x_13);
x_30 = x_36;
x_31 = x_34;
goto lbl_32;
}
lbl_32:
{
obj* x_39; 
x_39 = l_lean_parser_syntax_as__node___main(x_31);
if (lean::obj_tag(x_39) == 0)
{
lean::dec(x_39);
if (lean::obj_tag(x_30) == 0)
{
obj* x_42; obj* x_43; obj* x_45; 
lean::dec(x_30);
x_42 = lean::box(0);
x_43 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_45, 0, x_5);
lean::cnstr_set(x_45, 1, x_22);
lean::cnstr_set(x_45, 2, x_43);
lean::cnstr_set(x_45, 3, x_42);
return x_45;
}
else
{
obj* x_46; 
x_46 = lean::cnstr_get(x_30, 0);
lean::inc(x_46);
lean::dec(x_30);
switch (lean::obj_tag(x_46)) {
case 0:
{
obj* x_49; obj* x_52; obj* x_53; obj* x_55; 
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
lean::dec(x_46);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_49);
x_53 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_53);
x_55 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_55, 0, x_5);
lean::cnstr_set(x_55, 1, x_22);
lean::cnstr_set(x_55, 2, x_53);
lean::cnstr_set(x_55, 3, x_52);
return x_55;
}
default:
{
obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_46);
x_57 = lean::box(0);
x_58 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_60, 0, x_5);
lean::cnstr_set(x_60, 1, x_22);
lean::cnstr_set(x_60, 2, x_58);
lean::cnstr_set(x_60, 3, x_57);
return x_60;
}
}
}
}
else
{
obj* x_61; obj* x_63; obj* x_64; obj* x_67; 
x_61 = lean::cnstr_get(x_39, 0);
lean::inc(x_61);
if (lean::is_shared(x_39)) {
 lean::dec(x_39);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_39, 0);
 x_63 = x_39;
}
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__1(x_64);
if (lean::obj_tag(x_30) == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_63);
lean::dec(x_30);
x_70 = lean::box(0);
x_71 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_71, 0, x_5);
lean::cnstr_set(x_71, 1, x_22);
lean::cnstr_set(x_71, 2, x_67);
lean::cnstr_set(x_71, 3, x_70);
return x_71;
}
else
{
obj* x_72; 
x_72 = lean::cnstr_get(x_30, 0);
lean::inc(x_72);
lean::dec(x_30);
switch (lean::obj_tag(x_72)) {
case 0:
{
obj* x_75; obj* x_78; obj* x_79; 
x_75 = lean::cnstr_get(x_72, 0);
lean::inc(x_75);
lean::dec(x_72);
if (lean::is_scalar(x_63)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_63;
}
lean::cnstr_set(x_78, 0, x_75);
x_79 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_79, 0, x_5);
lean::cnstr_set(x_79, 1, x_22);
lean::cnstr_set(x_79, 2, x_67);
lean::cnstr_set(x_79, 3, x_78);
return x_79;
}
default:
{
obj* x_82; obj* x_83; 
lean::dec(x_63);
lean::dec(x_72);
x_82 = lean::box(0);
x_83 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_83, 0, x_5);
lean::cnstr_set(x_83, 1, x_22);
lean::cnstr_set(x_83, 2, x_67);
lean::cnstr_set(x_83, 3, x_82);
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
obj* l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
}
lbl_21:
{
obj* x_28; obj* x_29; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_31; 
x_31 = lean::box(3);
x_28 = x_1;
x_29 = x_31;
goto lbl_30;
}
else
{
obj* x_32; obj* x_34; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_1, 1);
lean::inc(x_34);
lean::dec(x_1);
x_28 = x_34;
x_29 = x_32;
goto lbl_30;
}
lbl_30:
{
obj* x_37; 
switch (lean::obj_tag(x_29)) {
case 0:
{
obj* x_39; obj* x_42; 
x_39 = lean::cnstr_get(x_29, 0);
lean::inc(x_39);
lean::dec(x_29);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
x_37 = x_42;
goto lbl_38;
}
default:
{
obj* x_44; 
lean::dec(x_29);
x_44 = lean::box(0);
x_37 = x_44;
goto lbl_38;
}
}
lbl_38:
{
obj* x_45; obj* x_46; 
if (lean::obj_tag(x_28) == 0)
{
obj* x_48; 
x_48 = lean::box(3);
x_45 = x_28;
x_46 = x_48;
goto lbl_47;
}
else
{
obj* x_49; obj* x_51; 
x_49 = lean::cnstr_get(x_28, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_28, 1);
lean::inc(x_51);
lean::dec(x_28);
x_45 = x_51;
x_46 = x_49;
goto lbl_47;
}
lbl_47:
{
obj* x_54; 
x_54 = l_lean_parser_syntax_as__node___main(x_46);
if (lean::obj_tag(x_54) == 0)
{
lean::dec(x_54);
if (lean::obj_tag(x_45) == 0)
{
obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_45);
x_57 = lean::box(0);
x_58 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_60, 0, x_20);
lean::cnstr_set(x_60, 1, x_37);
lean::cnstr_set(x_60, 2, x_58);
lean::cnstr_set(x_60, 3, x_57);
return x_60;
}
else
{
obj* x_61; 
x_61 = lean::cnstr_get(x_45, 0);
lean::inc(x_61);
lean::dec(x_45);
switch (lean::obj_tag(x_61)) {
case 0:
{
obj* x_64; obj* x_67; obj* x_68; obj* x_70; 
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
lean::dec(x_61);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_64);
x_68 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_68);
x_70 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_70, 0, x_20);
lean::cnstr_set(x_70, 1, x_37);
lean::cnstr_set(x_70, 2, x_68);
lean::cnstr_set(x_70, 3, x_67);
return x_70;
}
default:
{
obj* x_72; obj* x_73; obj* x_75; 
lean::dec(x_61);
x_72 = lean::box(0);
x_73 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_73);
x_75 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_75, 0, x_20);
lean::cnstr_set(x_75, 1, x_37);
lean::cnstr_set(x_75, 2, x_73);
lean::cnstr_set(x_75, 3, x_72);
return x_75;
}
}
}
}
else
{
obj* x_76; obj* x_78; obj* x_79; obj* x_82; 
x_76 = lean::cnstr_get(x_54, 0);
lean::inc(x_76);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_78 = x_54;
}
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__1(x_79);
if (lean::obj_tag(x_45) == 0)
{
obj* x_85; obj* x_86; 
lean::dec(x_45);
lean::dec(x_78);
x_85 = lean::box(0);
x_86 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_86, 0, x_20);
lean::cnstr_set(x_86, 1, x_37);
lean::cnstr_set(x_86, 2, x_82);
lean::cnstr_set(x_86, 3, x_85);
return x_86;
}
else
{
obj* x_87; 
x_87 = lean::cnstr_get(x_45, 0);
lean::inc(x_87);
lean::dec(x_45);
switch (lean::obj_tag(x_87)) {
case 0:
{
obj* x_90; obj* x_93; obj* x_94; 
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
lean::dec(x_87);
if (lean::is_scalar(x_78)) {
 x_93 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_93 = x_78;
}
lean::cnstr_set(x_93, 0, x_90);
x_94 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_94, 0, x_20);
lean::cnstr_set(x_94, 1, x_37);
lean::cnstr_set(x_94, 2, x_82);
lean::cnstr_set(x_94, 3, x_93);
return x_94;
}
default:
{
obj* x_97; obj* x_98; 
lean::dec(x_87);
lean::dec(x_78);
x_97 = lean::box(0);
x_98 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_98, 0, x_20);
lean::cnstr_set(x_98, 1, x_37);
lean::cnstr_set(x_98, 2, x_82);
lean::cnstr_set(x_98, 3, x_97);
return x_98;
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
obj* l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_10);
x_12 = l_option_map___rarg(x_10, x_1);
x_13 = lean::box(3);
lean::inc(x_13);
x_15 = l_option_get__or__else___main___rarg(x_12, x_13);
lean::inc(x_10);
x_17 = l_option_map___rarg(x_10, x_3);
lean::inc(x_13);
x_19 = l_option_get__or__else___main___rarg(x_17, x_13);
x_20 = l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__2(x_5);
x_21 = l_lean_parser_no__kind;
lean::inc(x_21);
x_23 = l_lean_parser_syntax_mk__node(x_21, x_20);
lean::inc(x_10);
x_25 = l_option_map___rarg(x_10, x_7);
x_26 = l_option_get__or__else___main___rarg(x_25, x_13);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_23);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_19);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_15);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_lean_parser_command_open__spec_hiding;
lean::inc(x_32);
x_34 = l_lean_parser_syntax_mk__node(x_32, x_31);
return x_34;
}
}
obj* _init_l_lean_parser_command_open__spec_hiding_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_open__spec_hiding_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_open__spec_hiding_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_open__spec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("open_spec");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_open__spec_hiding_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_open__spec_renaming_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_open__spec_only_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_open__spec_as_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_7; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_5 = x_7;
goto lbl_6;
}
default:
{
obj* x_11; 
lean::dec(x_1);
x_11 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_11);
x_5 = x_11;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_13 = x_0;
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::dec(x_0);
x_13 = x_19;
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_22; obj* x_24; 
x_24 = l_lean_parser_syntax_as__node___main(x_14);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; 
lean::dec(x_24);
x_26 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_26);
x_22 = x_26;
goto lbl_23;
}
else
{
obj* x_28; obj* x_30; obj* x_31; 
x_28 = lean::cnstr_get(x_24, 0);
lean::inc(x_28);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_30 = x_24;
}
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
if (lean::obj_tag(x_31) == 0)
{
obj* x_36; 
lean::dec(x_30);
lean::dec(x_31);
x_36 = lean::box(0);
x_22 = x_36;
goto lbl_23;
}
else
{
obj* x_37; obj* x_39; 
x_37 = lean::cnstr_get(x_31, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_31, 1);
lean::inc(x_39);
lean::dec(x_31);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_39);
x_43 = l_lean_parser_command_open__spec_as_has__view;
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::apply_1(x_44, x_37);
if (lean::is_scalar(x_30)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_30;
}
lean::cnstr_set(x_47, 0, x_46);
x_22 = x_47;
goto lbl_23;
}
else
{
obj* x_51; 
lean::dec(x_30);
lean::dec(x_37);
lean::dec(x_39);
x_51 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_51);
x_22 = x_51;
goto lbl_23;
}
}
}
lbl_23:
{
obj* x_53; obj* x_54; 
if (lean::obj_tag(x_13) == 0)
{
obj* x_56; 
x_56 = lean::box(3);
x_53 = x_13;
x_54 = x_56;
goto lbl_55;
}
else
{
obj* x_57; obj* x_59; 
x_57 = lean::cnstr_get(x_13, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_13, 1);
lean::inc(x_59);
lean::dec(x_13);
x_53 = x_59;
x_54 = x_57;
goto lbl_55;
}
lbl_55:
{
obj* x_62; obj* x_64; 
x_64 = l_lean_parser_syntax_as__node___main(x_54);
if (lean::obj_tag(x_64) == 0)
{
obj* x_66; 
lean::dec(x_64);
x_66 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3;
lean::inc(x_66);
x_62 = x_66;
goto lbl_63;
}
else
{
obj* x_68; obj* x_70; obj* x_71; 
x_68 = lean::cnstr_get(x_64, 0);
lean::inc(x_68);
if (lean::is_shared(x_64)) {
 lean::dec(x_64);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_64, 0);
 x_70 = x_64;
}
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
if (lean::obj_tag(x_71) == 0)
{
obj* x_76; 
lean::dec(x_70);
lean::dec(x_71);
x_76 = lean::box(0);
x_62 = x_76;
goto lbl_63;
}
else
{
obj* x_77; obj* x_79; 
x_77 = lean::cnstr_get(x_71, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_71, 1);
lean::inc(x_79);
lean::dec(x_71);
if (lean::obj_tag(x_79) == 0)
{
obj* x_83; obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_79);
x_83 = l_lean_parser_command_open__spec_only_has__view;
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::apply_1(x_84, x_77);
if (lean::is_scalar(x_70)) {
 x_87 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_87 = x_70;
}
lean::cnstr_set(x_87, 0, x_86);
x_62 = x_87;
goto lbl_63;
}
else
{
obj* x_91; 
lean::dec(x_70);
lean::dec(x_77);
lean::dec(x_79);
x_91 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3;
lean::inc(x_91);
x_62 = x_91;
goto lbl_63;
}
}
}
lbl_63:
{
obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_99; 
if (lean::obj_tag(x_53) == 0)
{
obj* x_101; 
x_101 = lean::box(3);
x_98 = x_53;
x_99 = x_101;
goto lbl_100;
}
else
{
obj* x_102; obj* x_104; 
x_102 = lean::cnstr_get(x_53, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_53, 1);
lean::inc(x_104);
lean::dec(x_53);
x_98 = x_104;
x_99 = x_102;
goto lbl_100;
}
lbl_94:
{
obj* x_107; obj* x_108; 
x_107 = lean::box(3);
x_108 = l_lean_parser_syntax_as__node___main(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_110; obj* x_112; 
lean::dec(x_108);
x_110 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_110);
x_112 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_112, 0, x_5);
lean::cnstr_set(x_112, 1, x_22);
lean::cnstr_set(x_112, 2, x_62);
lean::cnstr_set(x_112, 3, x_93);
lean::cnstr_set(x_112, 4, x_110);
return x_112;
}
else
{
obj* x_113; obj* x_115; obj* x_116; 
x_113 = lean::cnstr_get(x_108, 0);
lean::inc(x_113);
if (lean::is_shared(x_108)) {
 lean::dec(x_108);
 x_115 = lean::box(0);
} else {
 lean::cnstr_release(x_108, 0);
 x_115 = x_108;
}
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
lean::dec(x_113);
if (lean::obj_tag(x_116) == 0)
{
obj* x_121; obj* x_122; 
lean::dec(x_115);
lean::dec(x_116);
x_121 = lean::box(0);
x_122 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_122, 0, x_5);
lean::cnstr_set(x_122, 1, x_22);
lean::cnstr_set(x_122, 2, x_62);
lean::cnstr_set(x_122, 3, x_93);
lean::cnstr_set(x_122, 4, x_121);
return x_122;
}
else
{
obj* x_123; obj* x_125; 
x_123 = lean::cnstr_get(x_116, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_116, 1);
lean::inc(x_125);
lean::dec(x_116);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_130; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_125);
x_129 = l_lean_parser_command_open__spec_hiding_has__view;
x_130 = lean::cnstr_get(x_129, 0);
lean::inc(x_130);
x_132 = lean::apply_1(x_130, x_123);
if (lean::is_scalar(x_115)) {
 x_133 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_133 = x_115;
}
lean::cnstr_set(x_133, 0, x_132);
x_134 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_134, 0, x_5);
lean::cnstr_set(x_134, 1, x_22);
lean::cnstr_set(x_134, 2, x_62);
lean::cnstr_set(x_134, 3, x_93);
lean::cnstr_set(x_134, 4, x_133);
return x_134;
}
else
{
obj* x_138; obj* x_140; 
lean::dec(x_125);
lean::dec(x_115);
lean::dec(x_123);
x_138 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_138);
x_140 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_140, 0, x_5);
lean::cnstr_set(x_140, 1, x_22);
lean::cnstr_set(x_140, 2, x_62);
lean::cnstr_set(x_140, 3, x_93);
lean::cnstr_set(x_140, 4, x_138);
return x_140;
}
}
}
}
lbl_97:
{
obj* x_141; 
x_141 = l_lean_parser_syntax_as__node___main(x_96);
if (lean::obj_tag(x_141) == 0)
{
obj* x_143; obj* x_145; 
lean::dec(x_141);
x_143 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_143);
x_145 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_145, 0, x_5);
lean::cnstr_set(x_145, 1, x_22);
lean::cnstr_set(x_145, 2, x_62);
lean::cnstr_set(x_145, 3, x_95);
lean::cnstr_set(x_145, 4, x_143);
return x_145;
}
else
{
obj* x_146; obj* x_148; obj* x_149; 
x_146 = lean::cnstr_get(x_141, 0);
lean::inc(x_146);
if (lean::is_shared(x_141)) {
 lean::dec(x_141);
 x_148 = lean::box(0);
} else {
 lean::cnstr_release(x_141, 0);
 x_148 = x_141;
}
x_149 = lean::cnstr_get(x_146, 1);
lean::inc(x_149);
lean::dec(x_146);
if (lean::obj_tag(x_149) == 0)
{
obj* x_154; obj* x_155; 
lean::dec(x_149);
lean::dec(x_148);
x_154 = lean::box(0);
x_155 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_155, 0, x_5);
lean::cnstr_set(x_155, 1, x_22);
lean::cnstr_set(x_155, 2, x_62);
lean::cnstr_set(x_155, 3, x_95);
lean::cnstr_set(x_155, 4, x_154);
return x_155;
}
else
{
obj* x_156; obj* x_158; 
x_156 = lean::cnstr_get(x_149, 0);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_149, 1);
lean::inc(x_158);
lean::dec(x_149);
if (lean::obj_tag(x_158) == 0)
{
obj* x_162; obj* x_163; obj* x_165; obj* x_166; obj* x_167; 
lean::dec(x_158);
x_162 = l_lean_parser_command_open__spec_hiding_has__view;
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
x_165 = lean::apply_1(x_163, x_156);
if (lean::is_scalar(x_148)) {
 x_166 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_166 = x_148;
}
lean::cnstr_set(x_166, 0, x_165);
x_167 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_167, 0, x_5);
lean::cnstr_set(x_167, 1, x_22);
lean::cnstr_set(x_167, 2, x_62);
lean::cnstr_set(x_167, 3, x_95);
lean::cnstr_set(x_167, 4, x_166);
return x_167;
}
else
{
obj* x_171; obj* x_173; 
lean::dec(x_158);
lean::dec(x_156);
lean::dec(x_148);
x_171 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_171);
x_173 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_173, 0, x_5);
lean::cnstr_set(x_173, 1, x_22);
lean::cnstr_set(x_173, 2, x_62);
lean::cnstr_set(x_173, 3, x_95);
lean::cnstr_set(x_173, 4, x_171);
return x_173;
}
}
}
}
lbl_100:
{
obj* x_174; 
x_174 = l_lean_parser_syntax_as__node___main(x_99);
if (lean::obj_tag(x_174) == 0)
{
lean::dec(x_174);
if (lean::obj_tag(x_98) == 0)
{
obj* x_177; 
lean::dec(x_98);
x_177 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_177);
x_93 = x_177;
goto lbl_94;
}
else
{
obj* x_179; obj* x_182; 
x_179 = lean::cnstr_get(x_98, 0);
lean::inc(x_179);
lean::dec(x_98);
x_182 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_182);
x_95 = x_182;
x_96 = x_179;
goto lbl_97;
}
}
else
{
obj* x_184; obj* x_186; obj* x_187; 
x_184 = lean::cnstr_get(x_174, 0);
lean::inc(x_184);
if (lean::is_shared(x_174)) {
 lean::dec(x_174);
 x_186 = lean::box(0);
} else {
 lean::cnstr_release(x_174, 0);
 x_186 = x_174;
}
x_187 = lean::cnstr_get(x_184, 1);
lean::inc(x_187);
lean::dec(x_184);
if (lean::obj_tag(x_187) == 0)
{
obj* x_192; 
lean::dec(x_186);
lean::dec(x_187);
x_192 = lean::box(0);
if (lean::obj_tag(x_98) == 0)
{
lean::dec(x_98);
x_93 = x_192;
goto lbl_94;
}
else
{
obj* x_194; 
x_194 = lean::cnstr_get(x_98, 0);
lean::inc(x_194);
lean::dec(x_98);
x_95 = x_192;
x_96 = x_194;
goto lbl_97;
}
}
else
{
obj* x_197; obj* x_199; 
x_197 = lean::cnstr_get(x_187, 0);
lean::inc(x_197);
x_199 = lean::cnstr_get(x_187, 1);
lean::inc(x_199);
lean::dec(x_187);
if (lean::obj_tag(x_199) == 0)
{
obj* x_203; obj* x_204; obj* x_206; obj* x_207; 
lean::dec(x_199);
x_203 = l_lean_parser_command_open__spec_renaming_has__view;
x_204 = lean::cnstr_get(x_203, 0);
lean::inc(x_204);
x_206 = lean::apply_1(x_204, x_197);
if (lean::is_scalar(x_186)) {
 x_207 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_207 = x_186;
}
lean::cnstr_set(x_207, 0, x_206);
if (lean::obj_tag(x_98) == 0)
{
lean::dec(x_98);
x_93 = x_207;
goto lbl_94;
}
else
{
obj* x_209; 
x_209 = lean::cnstr_get(x_98, 0);
lean::inc(x_209);
lean::dec(x_98);
x_95 = x_207;
x_96 = x_209;
goto lbl_97;
}
}
else
{
lean::dec(x_197);
lean::dec(x_199);
lean::dec(x_186);
if (lean::obj_tag(x_98) == 0)
{
obj* x_216; 
lean::dec(x_98);
x_216 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_216);
x_93 = x_216;
goto lbl_94;
}
else
{
obj* x_218; obj* x_221; 
x_218 = lean::cnstr_get(x_98, 0);
lean::inc(x_218);
lean::dec(x_98);
x_221 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_221);
x_95 = x_221;
x_96 = x_218;
goto lbl_97;
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
obj* l_lean_parser_command_open__spec_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__5;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_22; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_20 = x_22;
goto lbl_21;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_26);
x_20 = x_26;
goto lbl_21;
}
}
lbl_21:
{
obj* x_28; obj* x_29; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_31; 
x_31 = lean::box(3);
x_28 = x_1;
x_29 = x_31;
goto lbl_30;
}
else
{
obj* x_32; obj* x_34; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_1, 1);
lean::inc(x_34);
lean::dec(x_1);
x_28 = x_34;
x_29 = x_32;
goto lbl_30;
}
lbl_30:
{
obj* x_37; obj* x_39; 
x_39 = l_lean_parser_syntax_as__node___main(x_29);
if (lean::obj_tag(x_39) == 0)
{
obj* x_41; 
lean::dec(x_39);
x_41 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_41);
x_37 = x_41;
goto lbl_38;
}
else
{
obj* x_43; obj* x_45; obj* x_46; 
x_43 = lean::cnstr_get(x_39, 0);
lean::inc(x_43);
if (lean::is_shared(x_39)) {
 lean::dec(x_39);
 x_45 = lean::box(0);
} else {
 lean::cnstr_release(x_39, 0);
 x_45 = x_39;
}
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
if (lean::obj_tag(x_46) == 0)
{
obj* x_51; 
lean::dec(x_45);
lean::dec(x_46);
x_51 = lean::box(0);
x_37 = x_51;
goto lbl_38;
}
else
{
obj* x_52; obj* x_54; 
x_52 = lean::cnstr_get(x_46, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_46, 1);
lean::inc(x_54);
lean::dec(x_46);
if (lean::obj_tag(x_54) == 0)
{
obj* x_58; obj* x_59; obj* x_61; obj* x_62; 
lean::dec(x_54);
x_58 = l_lean_parser_command_open__spec_as_has__view;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::apply_1(x_59, x_52);
if (lean::is_scalar(x_45)) {
 x_62 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_62 = x_45;
}
lean::cnstr_set(x_62, 0, x_61);
x_37 = x_62;
goto lbl_38;
}
else
{
obj* x_66; 
lean::dec(x_54);
lean::dec(x_52);
lean::dec(x_45);
x_66 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_66);
x_37 = x_66;
goto lbl_38;
}
}
}
lbl_38:
{
obj* x_68; obj* x_69; 
if (lean::obj_tag(x_28) == 0)
{
obj* x_71; 
x_71 = lean::box(3);
x_68 = x_28;
x_69 = x_71;
goto lbl_70;
}
else
{
obj* x_72; obj* x_74; 
x_72 = lean::cnstr_get(x_28, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_28, 1);
lean::inc(x_74);
lean::dec(x_28);
x_68 = x_74;
x_69 = x_72;
goto lbl_70;
}
lbl_70:
{
obj* x_77; obj* x_79; 
x_79 = l_lean_parser_syntax_as__node___main(x_69);
if (lean::obj_tag(x_79) == 0)
{
obj* x_81; 
lean::dec(x_79);
x_81 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3;
lean::inc(x_81);
x_77 = x_81;
goto lbl_78;
}
else
{
obj* x_83; obj* x_85; obj* x_86; 
x_83 = lean::cnstr_get(x_79, 0);
lean::inc(x_83);
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_85 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 x_85 = x_79;
}
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
lean::dec(x_83);
if (lean::obj_tag(x_86) == 0)
{
obj* x_91; 
lean::dec(x_86);
lean::dec(x_85);
x_91 = lean::box(0);
x_77 = x_91;
goto lbl_78;
}
else
{
obj* x_92; obj* x_94; 
x_92 = lean::cnstr_get(x_86, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_86, 1);
lean::inc(x_94);
lean::dec(x_86);
if (lean::obj_tag(x_94) == 0)
{
obj* x_98; obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_94);
x_98 = l_lean_parser_command_open__spec_only_has__view;
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_101 = lean::apply_1(x_99, x_92);
if (lean::is_scalar(x_85)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_85;
}
lean::cnstr_set(x_102, 0, x_101);
x_77 = x_102;
goto lbl_78;
}
else
{
obj* x_106; 
lean::dec(x_85);
lean::dec(x_92);
lean::dec(x_94);
x_106 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3;
lean::inc(x_106);
x_77 = x_106;
goto lbl_78;
}
}
}
lbl_78:
{
obj* x_108; obj* x_110; obj* x_111; obj* x_113; obj* x_114; 
if (lean::obj_tag(x_68) == 0)
{
obj* x_116; 
x_116 = lean::box(3);
x_113 = x_68;
x_114 = x_116;
goto lbl_115;
}
else
{
obj* x_117; obj* x_119; 
x_117 = lean::cnstr_get(x_68, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_68, 1);
lean::inc(x_119);
lean::dec(x_68);
x_113 = x_119;
x_114 = x_117;
goto lbl_115;
}
lbl_109:
{
obj* x_122; obj* x_123; 
x_122 = lean::box(3);
x_123 = l_lean_parser_syntax_as__node___main(x_122);
if (lean::obj_tag(x_123) == 0)
{
obj* x_125; obj* x_127; 
lean::dec(x_123);
x_125 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_125);
x_127 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_127, 0, x_20);
lean::cnstr_set(x_127, 1, x_37);
lean::cnstr_set(x_127, 2, x_77);
lean::cnstr_set(x_127, 3, x_108);
lean::cnstr_set(x_127, 4, x_125);
return x_127;
}
else
{
obj* x_128; obj* x_130; obj* x_131; 
x_128 = lean::cnstr_get(x_123, 0);
lean::inc(x_128);
if (lean::is_shared(x_123)) {
 lean::dec(x_123);
 x_130 = lean::box(0);
} else {
 lean::cnstr_release(x_123, 0);
 x_130 = x_123;
}
x_131 = lean::cnstr_get(x_128, 1);
lean::inc(x_131);
lean::dec(x_128);
if (lean::obj_tag(x_131) == 0)
{
obj* x_136; obj* x_137; 
lean::dec(x_131);
lean::dec(x_130);
x_136 = lean::box(0);
x_137 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_137, 0, x_20);
lean::cnstr_set(x_137, 1, x_37);
lean::cnstr_set(x_137, 2, x_77);
lean::cnstr_set(x_137, 3, x_108);
lean::cnstr_set(x_137, 4, x_136);
return x_137;
}
else
{
obj* x_138; obj* x_140; 
x_138 = lean::cnstr_get(x_131, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_131, 1);
lean::inc(x_140);
lean::dec(x_131);
if (lean::obj_tag(x_140) == 0)
{
obj* x_144; obj* x_145; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_140);
x_144 = l_lean_parser_command_open__spec_hiding_has__view;
x_145 = lean::cnstr_get(x_144, 0);
lean::inc(x_145);
x_147 = lean::apply_1(x_145, x_138);
if (lean::is_scalar(x_130)) {
 x_148 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_148 = x_130;
}
lean::cnstr_set(x_148, 0, x_147);
x_149 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_149, 0, x_20);
lean::cnstr_set(x_149, 1, x_37);
lean::cnstr_set(x_149, 2, x_77);
lean::cnstr_set(x_149, 3, x_108);
lean::cnstr_set(x_149, 4, x_148);
return x_149;
}
else
{
obj* x_153; obj* x_155; 
lean::dec(x_138);
lean::dec(x_140);
lean::dec(x_130);
x_153 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_153);
x_155 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_155, 0, x_20);
lean::cnstr_set(x_155, 1, x_37);
lean::cnstr_set(x_155, 2, x_77);
lean::cnstr_set(x_155, 3, x_108);
lean::cnstr_set(x_155, 4, x_153);
return x_155;
}
}
}
}
lbl_112:
{
obj* x_156; 
x_156 = l_lean_parser_syntax_as__node___main(x_111);
if (lean::obj_tag(x_156) == 0)
{
obj* x_158; obj* x_160; 
lean::dec(x_156);
x_158 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_158);
x_160 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_160, 0, x_20);
lean::cnstr_set(x_160, 1, x_37);
lean::cnstr_set(x_160, 2, x_77);
lean::cnstr_set(x_160, 3, x_110);
lean::cnstr_set(x_160, 4, x_158);
return x_160;
}
else
{
obj* x_161; obj* x_163; obj* x_164; 
x_161 = lean::cnstr_get(x_156, 0);
lean::inc(x_161);
if (lean::is_shared(x_156)) {
 lean::dec(x_156);
 x_163 = lean::box(0);
} else {
 lean::cnstr_release(x_156, 0);
 x_163 = x_156;
}
x_164 = lean::cnstr_get(x_161, 1);
lean::inc(x_164);
lean::dec(x_161);
if (lean::obj_tag(x_164) == 0)
{
obj* x_169; obj* x_170; 
lean::dec(x_164);
lean::dec(x_163);
x_169 = lean::box(0);
x_170 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_170, 0, x_20);
lean::cnstr_set(x_170, 1, x_37);
lean::cnstr_set(x_170, 2, x_77);
lean::cnstr_set(x_170, 3, x_110);
lean::cnstr_set(x_170, 4, x_169);
return x_170;
}
else
{
obj* x_171; obj* x_173; 
x_171 = lean::cnstr_get(x_164, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_164, 1);
lean::inc(x_173);
lean::dec(x_164);
if (lean::obj_tag(x_173) == 0)
{
obj* x_177; obj* x_178; obj* x_180; obj* x_181; obj* x_182; 
lean::dec(x_173);
x_177 = l_lean_parser_command_open__spec_hiding_has__view;
x_178 = lean::cnstr_get(x_177, 0);
lean::inc(x_178);
x_180 = lean::apply_1(x_178, x_171);
if (lean::is_scalar(x_163)) {
 x_181 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_181 = x_163;
}
lean::cnstr_set(x_181, 0, x_180);
x_182 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_182, 0, x_20);
lean::cnstr_set(x_182, 1, x_37);
lean::cnstr_set(x_182, 2, x_77);
lean::cnstr_set(x_182, 3, x_110);
lean::cnstr_set(x_182, 4, x_181);
return x_182;
}
else
{
obj* x_186; obj* x_188; 
lean::dec(x_163);
lean::dec(x_173);
lean::dec(x_171);
x_186 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_186);
x_188 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_188, 0, x_20);
lean::cnstr_set(x_188, 1, x_37);
lean::cnstr_set(x_188, 2, x_77);
lean::cnstr_set(x_188, 3, x_110);
lean::cnstr_set(x_188, 4, x_186);
return x_188;
}
}
}
}
lbl_115:
{
obj* x_189; 
x_189 = l_lean_parser_syntax_as__node___main(x_114);
if (lean::obj_tag(x_189) == 0)
{
lean::dec(x_189);
if (lean::obj_tag(x_113) == 0)
{
obj* x_192; 
lean::dec(x_113);
x_192 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_192);
x_108 = x_192;
goto lbl_109;
}
else
{
obj* x_194; obj* x_197; 
x_194 = lean::cnstr_get(x_113, 0);
lean::inc(x_194);
lean::dec(x_113);
x_197 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_197);
x_110 = x_197;
x_111 = x_194;
goto lbl_112;
}
}
else
{
obj* x_199; obj* x_201; obj* x_202; 
x_199 = lean::cnstr_get(x_189, 0);
lean::inc(x_199);
if (lean::is_shared(x_189)) {
 lean::dec(x_189);
 x_201 = lean::box(0);
} else {
 lean::cnstr_release(x_189, 0);
 x_201 = x_189;
}
x_202 = lean::cnstr_get(x_199, 1);
lean::inc(x_202);
lean::dec(x_199);
if (lean::obj_tag(x_202) == 0)
{
obj* x_207; 
lean::dec(x_201);
lean::dec(x_202);
x_207 = lean::box(0);
if (lean::obj_tag(x_113) == 0)
{
lean::dec(x_113);
x_108 = x_207;
goto lbl_109;
}
else
{
obj* x_209; 
x_209 = lean::cnstr_get(x_113, 0);
lean::inc(x_209);
lean::dec(x_113);
x_110 = x_207;
x_111 = x_209;
goto lbl_112;
}
}
else
{
obj* x_212; obj* x_214; 
x_212 = lean::cnstr_get(x_202, 0);
lean::inc(x_212);
x_214 = lean::cnstr_get(x_202, 1);
lean::inc(x_214);
lean::dec(x_202);
if (lean::obj_tag(x_214) == 0)
{
obj* x_218; obj* x_219; obj* x_221; obj* x_222; 
lean::dec(x_214);
x_218 = l_lean_parser_command_open__spec_renaming_has__view;
x_219 = lean::cnstr_get(x_218, 0);
lean::inc(x_219);
x_221 = lean::apply_1(x_219, x_212);
if (lean::is_scalar(x_201)) {
 x_222 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_222 = x_201;
}
lean::cnstr_set(x_222, 0, x_221);
if (lean::obj_tag(x_113) == 0)
{
lean::dec(x_113);
x_108 = x_222;
goto lbl_109;
}
else
{
obj* x_224; 
x_224 = lean::cnstr_get(x_113, 0);
lean::inc(x_224);
lean::dec(x_113);
x_110 = x_222;
x_111 = x_224;
goto lbl_112;
}
}
else
{
lean::dec(x_214);
lean::dec(x_201);
lean::dec(x_212);
if (lean::obj_tag(x_113) == 0)
{
obj* x_231; 
lean::dec(x_113);
x_231 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_231);
x_108 = x_231;
goto lbl_109;
}
else
{
obj* x_233; obj* x_236; 
x_233 = lean::cnstr_get(x_113, 0);
lean::inc(x_233);
lean::dec(x_113);
x_236 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_236);
x_110 = x_236;
x_111 = x_233;
goto lbl_112;
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
obj* l_lean_parser_command_open__spec_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
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
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_1);
x_13 = lean::box(0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_17; 
lean::dec(x_3);
x_17 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_17);
x_14 = x_17;
goto lbl_15;
}
else
{
obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_30; 
x_19 = lean::cnstr_get(x_3, 0);
lean::inc(x_19);
lean::dec(x_3);
x_22 = l_lean_parser_command_open__spec_as_has__view;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
x_25 = lean::apply_1(x_23, x_19);
lean::inc(x_13);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_13);
x_28 = l_lean_parser_no__kind;
lean::inc(x_28);
x_30 = l_lean_parser_syntax_mk__node(x_28, x_27);
x_14 = x_30;
goto lbl_15;
}
lbl_15:
{
obj* x_31; obj* x_33; obj* x_34; 
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_38; 
lean::dec(x_7);
x_38 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_38);
x_31 = x_38;
goto lbl_32;
}
else
{
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_7, 0);
lean::inc(x_40);
lean::dec(x_7);
x_43 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_43);
x_33 = x_43;
x_34 = x_40;
goto lbl_35;
}
}
else
{
obj* x_45; obj* x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_54; obj* x_56; 
x_45 = lean::cnstr_get(x_5, 0);
lean::inc(x_45);
lean::dec(x_5);
x_48 = l_lean_parser_command_open__spec_only_has__view;
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
x_51 = lean::apply_1(x_49, x_45);
lean::inc(x_13);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_13);
x_54 = l_lean_parser_no__kind;
lean::inc(x_54);
x_56 = l_lean_parser_syntax_mk__node(x_54, x_53);
if (lean::obj_tag(x_7) == 0)
{
lean::dec(x_7);
x_31 = x_56;
goto lbl_32;
}
else
{
obj* x_58; 
x_58 = lean::cnstr_get(x_7, 0);
lean::inc(x_58);
lean::dec(x_7);
x_33 = x_56;
x_34 = x_58;
goto lbl_35;
}
}
lbl_32:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; 
lean::dec(x_9);
lean::dec(x_13);
x_63 = l_lean_parser_term_binder__content_has__view_x_27___lambda__2___closed__2;
lean::inc(x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_31);
lean::cnstr_set(x_65, 1, x_63);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_14);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_12);
lean::cnstr_set(x_67, 1, x_66);
x_68 = l_lean_parser_command_open__spec;
lean::inc(x_68);
x_70 = l_lean_parser_syntax_mk__node(x_68, x_67);
return x_70;
}
else
{
obj* x_71; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_92; 
x_71 = lean::cnstr_get(x_9, 0);
lean::inc(x_71);
lean::dec(x_9);
x_74 = l_lean_parser_command_open__spec_hiding_has__view;
x_75 = lean::cnstr_get(x_74, 1);
lean::inc(x_75);
x_77 = lean::apply_1(x_75, x_71);
lean::inc(x_13);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_13);
x_80 = l_lean_parser_no__kind;
lean::inc(x_80);
x_82 = l_lean_parser_syntax_mk__node(x_80, x_79);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_13);
x_84 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_83);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_31);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_14);
lean::cnstr_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_12);
lean::cnstr_set(x_89, 1, x_88);
x_90 = l_lean_parser_command_open__spec;
lean::inc(x_90);
x_92 = l_lean_parser_syntax_mk__node(x_90, x_89);
return x_92;
}
}
lbl_35:
{
obj* x_93; obj* x_94; obj* x_96; obj* x_98; obj* x_99; obj* x_101; 
x_93 = l_lean_parser_command_open__spec_renaming_has__view;
x_94 = lean::cnstr_get(x_93, 1);
lean::inc(x_94);
x_96 = lean::apply_1(x_94, x_34);
lean::inc(x_13);
x_98 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_98, 0, x_96);
lean::cnstr_set(x_98, 1, x_13);
x_99 = l_lean_parser_no__kind;
lean::inc(x_99);
x_101 = l_lean_parser_syntax_mk__node(x_99, x_98);
if (lean::obj_tag(x_9) == 0)
{
obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_112; 
lean::dec(x_9);
lean::dec(x_13);
x_104 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_104);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_101);
lean::cnstr_set(x_106, 1, x_104);
x_107 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_107, 0, x_33);
lean::cnstr_set(x_107, 1, x_106);
x_108 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_108, 0, x_14);
lean::cnstr_set(x_108, 1, x_107);
x_109 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_109, 0, x_12);
lean::cnstr_set(x_109, 1, x_108);
x_110 = l_lean_parser_command_open__spec;
lean::inc(x_110);
x_112 = l_lean_parser_syntax_mk__node(x_110, x_109);
return x_112;
}
else
{
obj* x_113; obj* x_116; obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_131; 
x_113 = lean::cnstr_get(x_9, 0);
lean::inc(x_113);
lean::dec(x_9);
x_116 = l_lean_parser_command_open__spec_hiding_has__view;
x_117 = lean::cnstr_get(x_116, 1);
lean::inc(x_117);
x_119 = lean::apply_1(x_117, x_113);
lean::inc(x_13);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set(x_121, 1, x_13);
lean::inc(x_99);
x_123 = l_lean_parser_syntax_mk__node(x_99, x_121);
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_13);
x_125 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_125, 0, x_101);
lean::cnstr_set(x_125, 1, x_124);
x_126 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_126, 0, x_33);
lean::cnstr_set(x_126, 1, x_125);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_14);
lean::cnstr_set(x_127, 1, x_126);
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_12);
lean::cnstr_set(x_128, 1, x_127);
x_129 = l_lean_parser_command_open__spec;
lean::inc(x_129);
x_131 = l_lean_parser_syntax_mk__node(x_129, x_128);
return x_131;
}
}
}
}
}
obj* _init_l_lean_parser_command_open__spec_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_open__spec_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_open__spec_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_open__spec_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_110; obj* x_115; 
x_0 = lean::mk_string("as");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::box(0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
lean::inc(x_7);
lean::inc(x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_7);
lean::inc(x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_lean_parser_command_open__spec_as;
lean::inc(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_17, 0, x_16);
x_18 = lean::mk_string("(");
x_19 = l_string_trim(x_18);
lean::inc(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_21, 0, x_19);
lean::inc(x_4);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_23, 0, x_19);
lean::closure_set(x_23, 1, x_4);
lean::closure_set(x_23, 2, x_21);
lean::inc(x_11);
lean::inc(x_23);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_11);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_27, 0, x_26);
lean::inc(x_8);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__2), 5, 1);
lean::closure_set(x_29, 0, x_8);
x_30 = lean::mk_string(")");
x_31 = l_string_trim(x_30);
lean::inc(x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_33, 0, x_31);
lean::inc(x_4);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_35, 0, x_31);
lean::closure_set(x_35, 1, x_4);
lean::closure_set(x_35, 2, x_33);
lean::inc(x_7);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_7);
lean::inc(x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_29);
lean::cnstr_set(x_39, 1, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_27);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_lean_parser_command_open__spec_only;
lean::inc(x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_43, 0, x_41);
lean::closure_set(x_43, 1, x_40);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_44, 0, x_43);
x_45 = lean::mk_string("renaming");
x_46 = l_string_trim(x_45);
lean::inc(x_46);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_48, 0, x_46);
lean::inc(x_4);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_50, 0, x_46);
lean::closure_set(x_50, 1, x_4);
lean::closure_set(x_50, 2, x_48);
lean::inc(x_7);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_7);
lean::inc(x_23);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_23);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_55, 0, x_54);
x_56 = lean::mk_string("->");
x_57 = l_string_trim(x_56);
lean::inc(x_57);
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_59, 0, x_57);
lean::inc(x_4);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_61, 0, x_57);
lean::closure_set(x_61, 1, x_4);
lean::closure_set(x_61, 2, x_59);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_11);
lean::inc(x_8);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_8);
lean::cnstr_set(x_64, 1, x_62);
x_65 = l_lean_parser_command_open__spec_renaming_item;
lean::inc(x_65);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_67, 0, x_65);
lean::closure_set(x_67, 1, x_64);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_68, 0, x_67);
lean::inc(x_37);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_37);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_55);
lean::cnstr_set(x_71, 1, x_70);
x_72 = l_lean_parser_command_open__spec_renaming;
lean::inc(x_72);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_74, 0, x_72);
lean::closure_set(x_74, 1, x_71);
x_75 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_75, 0, x_74);
x_76 = lean::mk_string("hiding");
x_77 = l_string_trim(x_76);
lean::inc(x_77);
x_79 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_79, 0, x_77);
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_80, 0, x_77);
lean::closure_set(x_80, 1, x_4);
lean::closure_set(x_80, 2, x_79);
lean::inc(x_8);
x_82 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_82, 0, x_8);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_37);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_23);
lean::cnstr_set(x_85, 1, x_84);
x_86 = l_lean_parser_command_open__spec_hiding;
lean::inc(x_86);
x_88 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_88, 0, x_86);
lean::closure_set(x_88, 1, x_85);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_89, 0, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_7);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_75);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_44);
lean::cnstr_set(x_92, 1, x_91);
x_93 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_93, 0, x_17);
lean::cnstr_set(x_93, 1, x_92);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_8);
lean::cnstr_set(x_94, 1, x_93);
x_95 = l_lean_parser_command_open__spec;
lean::inc(x_94);
lean::inc(x_95);
x_98 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_98, 0, x_95);
lean::closure_set(x_98, 1, x_94);
x_99 = l_lean_parser_command__parser__m_monad___closed__1;
x_100 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_101 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_102 = l_lean_parser_command__parser__m_alternative___closed__1;
x_103 = l_lean_parser_command_open__spec_has__view;
lean::inc(x_103);
lean::inc(x_95);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::inc(x_99);
x_110 = l_lean_parser_combinators_node_view___rarg(x_99, x_100, x_101, x_102, x_95, x_94, x_103);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::inc(x_99);
x_115 = l_lean_parser_combinators_many1_view___rarg(x_99, x_100, x_101, x_102, x_98, x_110);
return x_115;
}
}
obj* _init_l_lean_parser_command_open__spec_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_0 = lean::box(0);
x_1 = lean::mk_string("as");
x_2 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_4 = l_lean_parser_symbol_tokens___rarg(x_1, x_2);
lean::inc(x_0);
lean::inc(x_0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
lean::inc(x_7);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_4, x_7);
x_10 = l_lean_parser_tokens___rarg(x_9);
x_11 = l_lean_parser_tokens___rarg(x_10);
x_12 = lean::mk_string("(");
lean::inc(x_2);
x_14 = l_lean_parser_symbol_tokens___rarg(x_12, x_2);
lean::inc(x_7);
lean::inc(x_14);
x_17 = l_lean_parser_list_cons_tokens___rarg(x_14, x_7);
x_18 = l_lean_parser_tokens___rarg(x_17);
x_19 = l_lean_parser_tokens___rarg(x_18);
lean::inc(x_0);
x_21 = l_lean_parser_tokens___rarg(x_0);
x_22 = lean::mk_string(")");
lean::inc(x_2);
x_24 = l_lean_parser_symbol_tokens___rarg(x_22, x_2);
lean::inc(x_0);
x_26 = l_lean_parser_list_cons_tokens___rarg(x_24, x_0);
lean::inc(x_26);
x_28 = l_lean_parser_list_cons_tokens___rarg(x_21, x_26);
lean::inc(x_28);
x_30 = l_lean_parser_list_cons_tokens___rarg(x_19, x_28);
x_31 = l_lean_parser_tokens___rarg(x_30);
x_32 = l_lean_parser_tokens___rarg(x_31);
x_33 = lean::mk_string("renaming");
lean::inc(x_2);
x_35 = l_lean_parser_symbol_tokens___rarg(x_33, x_2);
lean::inc(x_0);
x_37 = l_lean_parser_list_cons_tokens___rarg(x_35, x_0);
lean::inc(x_14);
x_39 = l_lean_parser_list_cons_tokens___rarg(x_14, x_37);
x_40 = l_lean_parser_tokens___rarg(x_39);
x_41 = l_lean_parser_tokens___rarg(x_40);
x_42 = lean::mk_string("->");
lean::inc(x_2);
x_44 = l_lean_parser_symbol_tokens___rarg(x_42, x_2);
x_45 = l_lean_parser_list_cons_tokens___rarg(x_44, x_7);
lean::inc(x_0);
x_47 = l_lean_parser_list_cons_tokens___rarg(x_0, x_45);
x_48 = l_lean_parser_tokens___rarg(x_47);
x_49 = l_lean_parser_tokens___rarg(x_48);
x_50 = l_lean_parser_list_cons_tokens___rarg(x_49, x_26);
x_51 = l_lean_parser_list_cons_tokens___rarg(x_41, x_50);
x_52 = l_lean_parser_tokens___rarg(x_51);
x_53 = l_lean_parser_tokens___rarg(x_52);
x_54 = lean::mk_string("hiding");
x_55 = l_lean_parser_symbol_tokens___rarg(x_54, x_2);
x_56 = l_lean_parser_list_cons_tokens___rarg(x_55, x_28);
x_57 = l_lean_parser_list_cons_tokens___rarg(x_14, x_56);
x_58 = l_lean_parser_tokens___rarg(x_57);
x_59 = l_lean_parser_tokens___rarg(x_58);
lean::inc(x_0);
x_61 = l_lean_parser_list_cons_tokens___rarg(x_59, x_0);
x_62 = l_lean_parser_list_cons_tokens___rarg(x_53, x_61);
x_63 = l_lean_parser_list_cons_tokens___rarg(x_32, x_62);
x_64 = l_lean_parser_list_cons_tokens___rarg(x_11, x_63);
x_65 = l_lean_parser_list_cons_tokens___rarg(x_0, x_64);
x_66 = l_lean_parser_tokens___rarg(x_65);
x_67 = l_lean_parser_tokens___rarg(x_66);
return x_67;
}
}
obj* _init_l_lean_parser_command_open__spec_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_97; 
x_0 = lean::mk_string("as");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::box(0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
lean::inc(x_7);
lean::inc(x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_7);
lean::inc(x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_lean_parser_command_open__spec_as;
lean::inc(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_17, 0, x_16);
x_18 = lean::mk_string("(");
x_19 = l_string_trim(x_18);
lean::inc(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_21, 0, x_19);
lean::inc(x_4);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_23, 0, x_19);
lean::closure_set(x_23, 1, x_4);
lean::closure_set(x_23, 2, x_21);
lean::inc(x_11);
lean::inc(x_23);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_11);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_27, 0, x_26);
lean::inc(x_8);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__2), 5, 1);
lean::closure_set(x_29, 0, x_8);
x_30 = lean::mk_string(")");
x_31 = l_string_trim(x_30);
lean::inc(x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_33, 0, x_31);
lean::inc(x_4);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_35, 0, x_31);
lean::closure_set(x_35, 1, x_4);
lean::closure_set(x_35, 2, x_33);
lean::inc(x_7);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_7);
lean::inc(x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_29);
lean::cnstr_set(x_39, 1, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_27);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_lean_parser_command_open__spec_only;
lean::inc(x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_43, 0, x_41);
lean::closure_set(x_43, 1, x_40);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_44, 0, x_43);
x_45 = lean::mk_string("renaming");
x_46 = l_string_trim(x_45);
lean::inc(x_46);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_48, 0, x_46);
lean::inc(x_4);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_50, 0, x_46);
lean::closure_set(x_50, 1, x_4);
lean::closure_set(x_50, 2, x_48);
lean::inc(x_7);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_7);
lean::inc(x_23);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_23);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_55, 0, x_54);
x_56 = lean::mk_string("->");
x_57 = l_string_trim(x_56);
lean::inc(x_57);
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_59, 0, x_57);
lean::inc(x_4);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_61, 0, x_57);
lean::closure_set(x_61, 1, x_4);
lean::closure_set(x_61, 2, x_59);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_11);
lean::inc(x_8);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_8);
lean::cnstr_set(x_64, 1, x_62);
x_65 = l_lean_parser_command_open__spec_renaming_item;
lean::inc(x_65);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_67, 0, x_65);
lean::closure_set(x_67, 1, x_64);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_68, 0, x_67);
lean::inc(x_37);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_37);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_55);
lean::cnstr_set(x_71, 1, x_70);
x_72 = l_lean_parser_command_open__spec_renaming;
lean::inc(x_72);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_74, 0, x_72);
lean::closure_set(x_74, 1, x_71);
x_75 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_75, 0, x_74);
x_76 = lean::mk_string("hiding");
x_77 = l_string_trim(x_76);
lean::inc(x_77);
x_79 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_79, 0, x_77);
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_80, 0, x_77);
lean::closure_set(x_80, 1, x_4);
lean::closure_set(x_80, 2, x_79);
lean::inc(x_8);
x_82 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_82, 0, x_8);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_37);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_23);
lean::cnstr_set(x_85, 1, x_84);
x_86 = l_lean_parser_command_open__spec_hiding;
lean::inc(x_86);
x_88 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_88, 0, x_86);
lean::closure_set(x_88, 1, x_85);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_89, 0, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_7);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_75);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_44);
lean::cnstr_set(x_92, 1, x_91);
x_93 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_93, 0, x_17);
lean::cnstr_set(x_93, 1, x_92);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_8);
lean::cnstr_set(x_94, 1, x_93);
x_95 = l_lean_parser_command_open__spec;
lean::inc(x_95);
x_97 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_97, 0, x_95);
lean::closure_set(x_97, 1, x_94);
return x_97;
}
}
obj* l_lean_parser_command_open__spec_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; 
x_4 = l_lean_parser_command_open__spec_parser___closed__1;
lean::inc(x_4);
x_6 = l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3(x_4, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_lean_parser_command_open() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("open");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_lean_parser_command_open__spec_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_open__spec_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_2; 
x_2 = lean::box(0);
x_0 = x_2;
goto lbl_1;
lbl_1:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = l_lean_parser_syntax_as__node___main(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; 
lean::dec(x_4);
x_6 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_15; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_15);
x_17 = l_list_map___main___rarg(x_15, x_12);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
obj* l_lean_parser_command_open_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_6; 
x_6 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; 
lean::dec(x_6);
x_8 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3;
lean::inc(x_8);
return x_8;
}
else
{
obj* x_10; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_12 = x_6;
}
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_18; 
lean::dec(x_13);
x_18 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3;
lean::inc(x_18);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
lean::dec(x_13);
x_23 = lean::box(0);
x_3 = x_23;
x_4 = x_20;
goto lbl_5;
}
}
else
{
obj* x_24; obj* x_26; 
x_24 = lean::cnstr_get(x_13, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_13, 1);
lean::inc(x_26);
lean::dec(x_13);
switch (lean::obj_tag(x_24)) {
case 0:
{
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_24, 0);
lean::inc(x_29);
lean::dec(x_24);
if (lean::is_scalar(x_12)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_12;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::obj_tag(x_26) == 0)
{
lean::dec(x_26);
x_1 = x_32;
goto lbl_2;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_26, 0);
lean::inc(x_34);
lean::dec(x_26);
x_3 = x_32;
x_4 = x_34;
goto lbl_5;
}
}
default:
{
lean::dec(x_24);
lean::dec(x_12);
if (lean::obj_tag(x_26) == 0)
{
obj* x_40; 
lean::dec(x_26);
x_40 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3;
lean::inc(x_40);
return x_40;
}
else
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_26, 0);
lean::inc(x_42);
lean::dec(x_26);
x_45 = lean::box(0);
x_3 = x_45;
x_4 = x_42;
goto lbl_5;
}
}
}
}
}
lbl_2:
{
obj* x_46; obj* x_47; 
x_46 = lean::box(3);
x_47 = l_lean_parser_syntax_as__node___main(x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_49; obj* x_51; 
lean::dec(x_47);
x_49 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_1);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_55; obj* x_58; obj* x_60; obj* x_61; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
lean::dec(x_47);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_58 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_58);
x_60 = l_list_map___main___rarg(x_58, x_55);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_1);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
}
lbl_5:
{
obj* x_62; 
x_62 = l_lean_parser_syntax_as__node___main(x_4);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; 
lean::dec(x_62);
x_64 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_3);
lean::cnstr_set(x_66, 1, x_64);
return x_66;
}
else
{
obj* x_67; obj* x_70; obj* x_73; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_62, 0);
lean::inc(x_67);
lean::dec(x_62);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_73);
x_75 = l_list_map___main___rarg(x_73, x_70);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_3);
lean::cnstr_set(x_76, 1, x_75);
return x_76;
}
}
}
}
obj* _init_l_lean_parser_command_open_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_open__spec_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* l_lean_parser_command_open_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_lean_parser_command_open_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = l_list_map___main___rarg(x_11, x_3);
x_14 = l_lean_parser_no__kind;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_10);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_lean_parser_command_open;
lean::inc(x_20);
x_22 = l_lean_parser_syntax_mk__node(x_20, x_19);
return x_22;
}
}
obj* _init_l_lean_parser_command_open_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_open_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_open_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_open_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::mk_string("open");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_command_open__spec_parser_lean_parser_has__tokens;
lean::inc(x_4);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_4, x_3);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_2, x_6);
x_8 = l_lean_parser_tokens___rarg(x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_open_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::mk_string("open");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_parser), 4, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_lean_parser_command_open_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_open;
x_5 = l_lean_parser_command_open_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_export() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("export");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_2; 
x_2 = lean::box(0);
x_0 = x_2;
goto lbl_1;
lbl_1:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = l_lean_parser_syntax_as__node___main(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; 
lean::dec(x_4);
x_6 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_15; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_15);
x_17 = l_list_map___main___rarg(x_15, x_12);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
obj* l_lean_parser_command_export_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_6; 
x_6 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; 
lean::dec(x_6);
x_8 = l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1;
lean::inc(x_8);
return x_8;
}
else
{
obj* x_10; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_12 = x_6;
}
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_18; 
lean::dec(x_13);
x_18 = l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1;
lean::inc(x_18);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
lean::dec(x_13);
x_23 = lean::box(0);
x_3 = x_23;
x_4 = x_20;
goto lbl_5;
}
}
else
{
obj* x_24; obj* x_26; 
x_24 = lean::cnstr_get(x_13, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_13, 1);
lean::inc(x_26);
lean::dec(x_13);
switch (lean::obj_tag(x_24)) {
case 0:
{
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_24, 0);
lean::inc(x_29);
lean::dec(x_24);
if (lean::is_scalar(x_12)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_12;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::obj_tag(x_26) == 0)
{
lean::dec(x_26);
x_1 = x_32;
goto lbl_2;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_26, 0);
lean::inc(x_34);
lean::dec(x_26);
x_3 = x_32;
x_4 = x_34;
goto lbl_5;
}
}
default:
{
lean::dec(x_24);
lean::dec(x_12);
if (lean::obj_tag(x_26) == 0)
{
obj* x_40; 
lean::dec(x_26);
x_40 = l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1;
lean::inc(x_40);
return x_40;
}
else
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_26, 0);
lean::inc(x_42);
lean::dec(x_26);
x_45 = lean::box(0);
x_3 = x_45;
x_4 = x_42;
goto lbl_5;
}
}
}
}
}
lbl_2:
{
obj* x_46; obj* x_47; 
x_46 = lean::box(3);
x_47 = l_lean_parser_syntax_as__node___main(x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_49; obj* x_51; 
lean::dec(x_47);
x_49 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_1);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_55; obj* x_58; obj* x_60; obj* x_61; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
lean::dec(x_47);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_58 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_58);
x_60 = l_list_map___main___rarg(x_58, x_55);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_1);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
}
lbl_5:
{
obj* x_62; 
x_62 = l_lean_parser_syntax_as__node___main(x_4);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; 
lean::dec(x_62);
x_64 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_3);
lean::cnstr_set(x_66, 1, x_64);
return x_66;
}
else
{
obj* x_67; obj* x_70; obj* x_73; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_62, 0);
lean::inc(x_67);
lean::dec(x_62);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_73);
x_75 = l_list_map___main___rarg(x_73, x_70);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_3);
lean::cnstr_set(x_76, 1, x_75);
return x_76;
}
}
}
}
obj* l_lean_parser_command_export_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_lean_parser_command_open_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = l_list_map___main___rarg(x_11, x_3);
x_14 = l_lean_parser_no__kind;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_10);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_lean_parser_command_export;
lean::inc(x_20);
x_22 = l_lean_parser_syntax_mk__node(x_20, x_19);
return x_22;
}
}
obj* _init_l_lean_parser_command_export_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_export_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_export_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_export_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_export_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_export_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::mk_string("export");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_command_open__spec_parser_lean_parser_has__tokens;
lean::inc(x_4);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_4, x_3);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_2, x_6);
x_8 = l_lean_parser_tokens___rarg(x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_export_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::mk_string("export");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open__spec_parser), 4, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_lean_parser_command_export_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_export;
x_5 = l_lean_parser_command_export_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_section() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("section");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_section_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
lean::dec(x_0);
x_16 = lean::box(3);
x_13 = x_16;
goto lbl_14;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_13 = x_17;
goto lbl_14;
}
lbl_14:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_13);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_24; 
lean::dec(x_20);
x_22 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_22);
return x_24;
}
else
{
obj* x_25; obj* x_27; obj* x_28; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_27 = x_20;
}
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_28) == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_27);
lean::dec(x_28);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_5);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_37; 
x_35 = lean::cnstr_get(x_28, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_28, 1);
lean::inc(x_37);
lean::dec(x_28);
if (lean::obj_tag(x_37) == 0)
{
lean::dec(x_37);
switch (lean::obj_tag(x_35)) {
case 1:
{
obj* x_41; obj* x_44; obj* x_45; 
x_41 = lean::cnstr_get(x_35, 0);
lean::inc(x_41);
lean::dec(x_35);
if (lean::is_scalar(x_27)) {
 x_44 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_44 = x_27;
}
lean::cnstr_set(x_44, 0, x_41);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_5);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
default:
{
obj* x_48; obj* x_50; 
lean::dec(x_27);
lean::dec(x_35);
x_48 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_48);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_5);
lean::cnstr_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
obj* x_54; obj* x_56; 
lean::dec(x_37);
lean::dec(x_27);
lean::dec(x_35);
x_54 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_54);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_5);
lean::cnstr_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_section_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_section_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
}
lbl_21:
{
obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_31; 
lean::dec(x_1);
x_31 = lean::box(3);
x_28 = x_31;
goto lbl_29;
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
lean::dec(x_1);
x_28 = x_32;
goto lbl_29;
}
lbl_29:
{
obj* x_35; 
x_35 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; obj* x_39; 
lean::dec(x_35);
x_37 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_20);
lean::cnstr_set(x_39, 1, x_37);
return x_39;
}
else
{
obj* x_40; obj* x_42; obj* x_43; 
x_40 = lean::cnstr_get(x_35, 0);
lean::inc(x_40);
if (lean::is_shared(x_35)) {
 lean::dec(x_35);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_35, 0);
 x_42 = x_35;
}
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_48; obj* x_49; 
lean::dec(x_43);
lean::dec(x_42);
x_48 = lean::box(0);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_20);
lean::cnstr_set(x_49, 1, x_48);
return x_49;
}
else
{
obj* x_50; obj* x_52; 
x_50 = lean::cnstr_get(x_43, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_43, 1);
lean::inc(x_52);
lean::dec(x_43);
if (lean::obj_tag(x_52) == 0)
{
lean::dec(x_52);
switch (lean::obj_tag(x_50)) {
case 1:
{
obj* x_56; obj* x_59; obj* x_60; 
x_56 = lean::cnstr_get(x_50, 0);
lean::inc(x_56);
lean::dec(x_50);
if (lean::is_scalar(x_42)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_42;
}
lean::cnstr_set(x_59, 0, x_56);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_20);
lean::cnstr_set(x_60, 1, x_59);
return x_60;
}
default:
{
obj* x_63; obj* x_65; 
lean::dec(x_50);
lean::dec(x_42);
x_63 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_20);
lean::cnstr_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
obj* x_69; obj* x_71; 
lean::dec(x_50);
lean::dec(x_42);
lean::dec(x_52);
x_69 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_20);
lean::cnstr_set(x_71, 1, x_69);
return x_71;
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_section_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
if (lean::obj_tag(x_3) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; 
lean::dec(x_3);
x_12 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_10);
lean::cnstr_set(x_14, 1, x_12);
x_15 = l_lean_parser_command_section;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; 
x_18 = lean::cnstr_get(x_3, 0);
lean::inc(x_18);
lean::dec(x_3);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_18);
lean::inc(x_21);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_21);
x_25 = l_lean_parser_no__kind;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_21);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_10);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_command_section;
lean::inc(x_30);
x_32 = l_lean_parser_syntax_mk__node(x_30, x_29);
return x_32;
}
}
}
obj* _init_l_lean_parser_command_section_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_section_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_section_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_section_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_section_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_section_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::mk_string("section");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_5, x_3);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_2, x_6);
x_8 = l_lean_parser_tokens___rarg(x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_section_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("section");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_lean_parser_command_section_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_section;
x_5 = l_lean_parser_command_section_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_namespace() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("namespace");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_namespace_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_14; obj* x_16; 
lean::dec(x_0);
x_14 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
switch (lean::obj_tag(x_17)) {
case 1:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_20);
return x_23;
}
default:
{
obj* x_25; obj* x_27; 
lean::dec(x_17);
x_25 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_5);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
}
}
}
}
}
}
obj* l_lean_parser_command_namespace_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_namespace_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
}
lbl_21:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_29; obj* x_31; 
lean::dec(x_1);
x_29 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_20);
lean::cnstr_set(x_31, 1, x_29);
return x_31;
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
lean::dec(x_1);
switch (lean::obj_tag(x_32)) {
case 1:
{
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
lean::dec(x_32);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_20);
lean::cnstr_set(x_38, 1, x_35);
return x_38;
}
default:
{
obj* x_40; obj* x_42; 
lean::dec(x_32);
x_40 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_20);
lean::cnstr_set(x_42, 1, x_40);
return x_42;
}
}
}
}
}
}
}
obj* l_lean_parser_command_namespace_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_3);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_10);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_lean_parser_command_namespace;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
}
obj* _init_l_lean_parser_command_namespace_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_namespace_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_namespace_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_namespace_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_namespace_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_namespace_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::mk_string("namespace");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
lean::inc(x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_3, x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_2, x_5);
x_7 = l_lean_parser_tokens___rarg(x_6);
return x_7;
}
}
obj* _init_l_lean_parser_command_namespace_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::mk_string("namespace");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_lean_parser_command_namespace_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_namespace;
x_5 = l_lean_parser_command_namespace_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_variable() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("variable");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_term_binder_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = l_lean_parser_term_binder_has__view;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_2, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_5);
if (lean::obj_tag(x_0) == 0)
{
obj* x_10; obj* x_12; 
lean::dec(x_0);
x_10 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__1;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_lean_parser_term_binder_has__view;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::apply_1(x_17, x_13);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
default:
{
lean::dec(x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_23; 
lean::dec(x_0);
x_23 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__2;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
lean::dec(x_0);
x_28 = lean::box(0);
x_29 = l_lean_parser_term_binder_has__view;
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::apply_1(x_30, x_25);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_28);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
obj* l_lean_parser_command_variable_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__3;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
if (lean::obj_tag(x_1) == 0)
{
obj* x_25; obj* x_27; 
lean::dec(x_1);
x_25 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
else
{
obj* x_28; obj* x_31; obj* x_32; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
x_31 = l_lean_parser_term_binder_has__view;
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::apply_1(x_32, x_28);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_23);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
default:
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_38; 
lean::dec(x_1);
x_38 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__2;
lean::inc(x_38);
return x_38;
}
else
{
obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
lean::dec(x_1);
x_43 = lean::box(0);
x_44 = l_lean_parser_term_binder_has__view;
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_47 = lean::apply_1(x_45, x_40);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_43);
lean::cnstr_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
obj* l_lean_parser_command_variable_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_lean_parser_term_binder_has__view;
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
x_14 = lean::apply_1(x_12, x_3);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_command_variable;
lean::inc(x_18);
x_20 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_20;
}
}
obj* _init_l_lean_parser_command_variable_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_variable_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_variable_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_variable_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_variable_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_variable_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::mk_string("variable");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = l_lean_parser_term_binder_parser_lean_parser_has__tokens;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_2, x_7);
x_9 = l_lean_parser_tokens___rarg(x_8);
return x_9;
}
}
obj* _init_l_lean_parser_command_variable_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("variable");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_binder_parser), 5, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_lean_parser_command_variable_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_variable;
x_5 = l_lean_parser_command_variable_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_variables() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("variables");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = l_lean_parser_term_bracketed__binders_has__view;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_2, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_5);
if (lean::obj_tag(x_0) == 0)
{
obj* x_10; obj* x_12; 
lean::dec(x_0);
x_10 = l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__2;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_lean_parser_term_bracketed__binders_has__view;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::apply_1(x_17, x_13);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
default:
{
lean::dec(x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_23; 
lean::dec(x_0);
x_23 = l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__1;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
lean::dec(x_0);
x_28 = lean::box(0);
x_29 = l_lean_parser_term_bracketed__binders_has__view;
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::apply_1(x_30, x_25);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_28);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
obj* l_lean_parser_command_variables_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__2;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
if (lean::obj_tag(x_1) == 0)
{
obj* x_25; obj* x_27; 
lean::dec(x_1);
x_25 = l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__2;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
else
{
obj* x_28; obj* x_31; obj* x_32; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
x_31 = l_lean_parser_term_bracketed__binders_has__view;
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::apply_1(x_32, x_28);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_23);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
default:
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_38; 
lean::dec(x_1);
x_38 = l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__1;
lean::inc(x_38);
return x_38;
}
else
{
obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
lean::dec(x_1);
x_43 = lean::box(0);
x_44 = l_lean_parser_term_bracketed__binders_has__view;
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_47 = lean::apply_1(x_45, x_40);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_43);
lean::cnstr_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
obj* l_lean_parser_command_variables_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_lean_parser_term_bracketed__binders_has__view;
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
x_14 = lean::apply_1(x_12, x_3);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_command_variables;
lean::inc(x_18);
x_20 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_20;
}
}
obj* _init_l_lean_parser_command_variables_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_variables_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_variables_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_variables_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_variables_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_variables_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::mk_string("variables");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = l_lean_parser_term_bracketed__binders_parser_lean_parser_has__tokens;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_2, x_7);
x_9 = l_lean_parser_tokens___rarg(x_8);
return x_9;
}
}
obj* _init_l_lean_parser_command_variables_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("variables");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_bracketed__binders_parser), 5, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_lean_parser_command_variables_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_variables;
x_5 = l_lean_parser_command_variables_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_include() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("include");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
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
x_8 = l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__1(x_5);
switch (lean::obj_tag(x_3)) {
case 1:
{
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
default:
{
obj* x_14; obj* x_16; 
lean::dec(x_3);
x_14 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_14);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_lean_parser_command_include_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
lean::dec(x_0);
x_16 = lean::box(3);
x_13 = x_16;
goto lbl_14;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_13 = x_17;
goto lbl_14;
}
lbl_14:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_13);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_24; 
lean::dec(x_20);
x_22 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_22);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
lean::dec(x_20);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__1(x_28);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
obj* l_lean_parser_command_include_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_include_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
}
lbl_21:
{
obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_31; 
lean::dec(x_1);
x_31 = lean::box(3);
x_28 = x_31;
goto lbl_29;
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
lean::dec(x_1);
x_28 = x_32;
goto lbl_29;
}
lbl_29:
{
obj* x_35; 
x_35 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; obj* x_39; 
lean::dec(x_35);
x_37 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_20);
lean::cnstr_set(x_39, 1, x_37);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_46; obj* x_47; 
x_40 = lean::cnstr_get(x_35, 0);
lean::inc(x_40);
lean::dec(x_35);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__1(x_43);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
obj* l_lean_parser_command_include_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__2(x_3);
x_12 = l_lean_parser_no__kind;
lean::inc(x_12);
x_14 = l_lean_parser_syntax_mk__node(x_12, x_11);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_command_include;
lean::inc(x_18);
x_20 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_20;
}
}
obj* _init_l_lean_parser_command_include_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_include_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_include_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_include_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_include_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_include_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::mk_string("include ");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_5, x_3);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_2, x_6);
x_8 = l_lean_parser_tokens___rarg(x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_include_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("include ");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_lean_parser_command_include_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_include;
x_5 = l_lean_parser_command_include_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_omit() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("omit");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
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
x_8 = l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__1(x_5);
switch (lean::obj_tag(x_3)) {
case 1:
{
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
default:
{
obj* x_14; obj* x_16; 
lean::dec(x_3);
x_14 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_14);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_lean_parser_command_omit_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
lean::dec(x_0);
x_16 = lean::box(3);
x_13 = x_16;
goto lbl_14;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_13 = x_17;
goto lbl_14;
}
lbl_14:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_13);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_24; 
lean::dec(x_20);
x_22 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_22);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
lean::dec(x_20);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__1(x_28);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
obj* l_lean_parser_command_omit_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_omit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
}
lbl_21:
{
obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_31; 
lean::dec(x_1);
x_31 = lean::box(3);
x_28 = x_31;
goto lbl_29;
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
lean::dec(x_1);
x_28 = x_32;
goto lbl_29;
}
lbl_29:
{
obj* x_35; 
x_35 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; obj* x_39; 
lean::dec(x_35);
x_37 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_20);
lean::cnstr_set(x_39, 1, x_37);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_46; obj* x_47; 
x_40 = lean::cnstr_get(x_35, 0);
lean::inc(x_40);
lean::dec(x_35);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__1(x_43);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
obj* l_lean_parser_command_omit_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__2(x_3);
x_12 = l_lean_parser_no__kind;
lean::inc(x_12);
x_14 = l_lean_parser_syntax_mk__node(x_12, x_11);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_command_omit;
lean::inc(x_18);
x_20 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_20;
}
}
obj* _init_l_lean_parser_command_omit_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_omit_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_omit_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_omit_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_omit_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_omit_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::mk_string("omit ");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_5, x_3);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_2, x_6);
x_8 = l_lean_parser_tokens___rarg(x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_omit_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("omit ");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_lean_parser_command_omit_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_omit;
x_5 = l_lean_parser_command_omit_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_end() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("end");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_end_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
lean::dec(x_0);
x_16 = lean::box(3);
x_13 = x_16;
goto lbl_14;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_13 = x_17;
goto lbl_14;
}
lbl_14:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_13);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_24; 
lean::dec(x_20);
x_22 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_22);
return x_24;
}
else
{
obj* x_25; obj* x_27; obj* x_28; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_27 = x_20;
}
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_28) == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_27);
lean::dec(x_28);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_5);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_37; 
x_35 = lean::cnstr_get(x_28, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_28, 1);
lean::inc(x_37);
lean::dec(x_28);
if (lean::obj_tag(x_37) == 0)
{
lean::dec(x_37);
switch (lean::obj_tag(x_35)) {
case 1:
{
obj* x_41; obj* x_44; obj* x_45; 
x_41 = lean::cnstr_get(x_35, 0);
lean::inc(x_41);
lean::dec(x_35);
if (lean::is_scalar(x_27)) {
 x_44 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_44 = x_27;
}
lean::cnstr_set(x_44, 0, x_41);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_5);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
default:
{
obj* x_48; obj* x_50; 
lean::dec(x_27);
lean::dec(x_35);
x_48 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_48);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_5);
lean::cnstr_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
obj* x_54; obj* x_56; 
lean::dec(x_37);
lean::dec(x_27);
lean::dec(x_35);
x_54 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_54);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_5);
lean::cnstr_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_end_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_end_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
}
lbl_21:
{
obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_31; 
lean::dec(x_1);
x_31 = lean::box(3);
x_28 = x_31;
goto lbl_29;
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
lean::dec(x_1);
x_28 = x_32;
goto lbl_29;
}
lbl_29:
{
obj* x_35; 
x_35 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; obj* x_39; 
lean::dec(x_35);
x_37 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_20);
lean::cnstr_set(x_39, 1, x_37);
return x_39;
}
else
{
obj* x_40; obj* x_42; obj* x_43; 
x_40 = lean::cnstr_get(x_35, 0);
lean::inc(x_40);
if (lean::is_shared(x_35)) {
 lean::dec(x_35);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_35, 0);
 x_42 = x_35;
}
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_48; obj* x_49; 
lean::dec(x_43);
lean::dec(x_42);
x_48 = lean::box(0);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_20);
lean::cnstr_set(x_49, 1, x_48);
return x_49;
}
else
{
obj* x_50; obj* x_52; 
x_50 = lean::cnstr_get(x_43, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_43, 1);
lean::inc(x_52);
lean::dec(x_43);
if (lean::obj_tag(x_52) == 0)
{
lean::dec(x_52);
switch (lean::obj_tag(x_50)) {
case 1:
{
obj* x_56; obj* x_59; obj* x_60; 
x_56 = lean::cnstr_get(x_50, 0);
lean::inc(x_56);
lean::dec(x_50);
if (lean::is_scalar(x_42)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_42;
}
lean::cnstr_set(x_59, 0, x_56);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_20);
lean::cnstr_set(x_60, 1, x_59);
return x_60;
}
default:
{
obj* x_63; obj* x_65; 
lean::dec(x_50);
lean::dec(x_42);
x_63 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_20);
lean::cnstr_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
obj* x_69; obj* x_71; 
lean::dec(x_50);
lean::dec(x_42);
lean::dec(x_52);
x_69 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_20);
lean::cnstr_set(x_71, 1, x_69);
return x_71;
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_end_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
if (lean::obj_tag(x_3) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; 
lean::dec(x_3);
x_12 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_10);
lean::cnstr_set(x_14, 1, x_12);
x_15 = l_lean_parser_command_end;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; 
x_18 = lean::cnstr_get(x_3, 0);
lean::inc(x_18);
lean::dec(x_3);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_18);
lean::inc(x_21);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_21);
x_25 = l_lean_parser_no__kind;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_21);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_10);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_command_end;
lean::inc(x_30);
x_32 = l_lean_parser_syntax_mk__node(x_30, x_29);
return x_32;
}
}
}
obj* _init_l_lean_parser_command_end_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_end_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_end_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_end_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_end_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_end_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::mk_string("end");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_5, x_3);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_2, x_6);
x_8 = l_lean_parser_tokens___rarg(x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_end_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("end");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_lean_parser_command_end_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_end;
x_5 = l_lean_parser_command_end_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_universes() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("universes");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
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
x_8 = l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__1(x_5);
switch (lean::obj_tag(x_3)) {
case 1:
{
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
default:
{
obj* x_14; obj* x_16; 
lean::dec(x_3);
x_14 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_14);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_lean_parser_command_universes_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
lean::dec(x_0);
x_16 = lean::box(3);
x_13 = x_16;
goto lbl_14;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_13 = x_17;
goto lbl_14;
}
lbl_14:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_13);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_24; 
lean::dec(x_20);
x_22 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_22);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
lean::dec(x_20);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__1(x_28);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
obj* l_lean_parser_command_universes_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_universes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
}
lbl_21:
{
obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_31; 
lean::dec(x_1);
x_31 = lean::box(3);
x_28 = x_31;
goto lbl_29;
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
lean::dec(x_1);
x_28 = x_32;
goto lbl_29;
}
lbl_29:
{
obj* x_35; 
x_35 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; obj* x_39; 
lean::dec(x_35);
x_37 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_20);
lean::cnstr_set(x_39, 1, x_37);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_46; obj* x_47; 
x_40 = lean::cnstr_get(x_35, 0);
lean::inc(x_40);
lean::dec(x_35);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__1(x_43);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
obj* l_lean_parser_command_universes_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__2(x_3);
x_12 = l_lean_parser_no__kind;
lean::inc(x_12);
x_14 = l_lean_parser_syntax_mk__node(x_12, x_11);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_command_universes;
lean::inc(x_18);
x_20 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_20;
}
}
obj* _init_l_lean_parser_command_universes_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_universes_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_universes_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_universes_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_universes_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_universe() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("universe");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_universe_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_14; obj* x_16; 
lean::dec(x_0);
x_14 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
switch (lean::obj_tag(x_17)) {
case 1:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_20);
return x_23;
}
default:
{
obj* x_25; obj* x_27; 
lean::dec(x_17);
x_25 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_5);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
}
}
}
}
}
}
obj* l_lean_parser_command_universe_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_universe_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
}
lbl_21:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_29; obj* x_31; 
lean::dec(x_1);
x_29 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_20);
lean::cnstr_set(x_31, 1, x_29);
return x_31;
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
lean::dec(x_1);
switch (lean::obj_tag(x_32)) {
case 1:
{
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
lean::dec(x_32);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_20);
lean::cnstr_set(x_38, 1, x_35);
return x_38;
}
default:
{
obj* x_40; obj* x_42; 
lean::dec(x_32);
x_40 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_20);
lean::cnstr_set(x_42, 1, x_40);
return x_42;
}
}
}
}
}
}
}
obj* l_lean_parser_command_universe_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_3);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_10);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_lean_parser_command_universe;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
}
obj* _init_l_lean_parser_command_universe_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_universe_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_universe_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_universe_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_universe_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_universe_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_0 = lean::mk_string("universes");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = lean::box(0);
lean::inc(x_4);
x_6 = l_lean_parser_tokens___rarg(x_4);
lean::inc(x_4);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_6, x_4);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_3, x_8);
x_10 = l_lean_parser_tokens___rarg(x_9);
x_11 = lean::mk_string("universe");
x_12 = l_lean_parser_symbol_tokens___rarg(x_11, x_1);
lean::inc(x_4);
lean::inc(x_4);
x_15 = l_lean_parser_list_cons_tokens___rarg(x_4, x_4);
x_16 = l_lean_parser_list_cons_tokens___rarg(x_12, x_15);
x_17 = l_lean_parser_tokens___rarg(x_16);
x_18 = l_lean_parser_list_cons_tokens___rarg(x_17, x_4);
x_19 = l_lean_parser_list_cons_tokens___rarg(x_10, x_18);
x_20 = l_lean_parser_tokens___rarg(x_19);
return x_20;
}
}
obj* l_reader__t_orelse___at_lean_parser_command_universe_parser___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_9 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_14 = x_9;
}
if (lean::obj_tag(x_10) == 0)
{
obj* x_19; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_10);
lean::cnstr_set(x_19, 1, x_12);
return x_19;
}
else
{
obj* x_20; uint8 x_22; 
x_20 = lean::cnstr_get(x_10, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (x_22 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_30; obj* x_31; 
lean::dec(x_10);
x_24 = lean::apply_4(x_1, x_2, x_3, x_4, x_12);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_20, x_25);
if (lean::is_scalar(x_14)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_14;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_27);
return x_31;
}
else
{
obj* x_37; 
lean::dec(x_20);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
if (lean::is_scalar(x_14)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_14;
}
lean::cnstr_set(x_37, 0, x_10);
lean::cnstr_set(x_37, 1, x_12);
return x_37;
}
}
}
}
obj* l_reader__t_orelse___at_lean_parser_command_universe_parser___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_orelse___at_lean_parser_command_universe_parser___spec__2___rarg), 6, 0);
return x_2;
}
}
obj* l_list_foldl___main___at_lean_parser_command_universe_parser___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; 
lean::dec(x_1);
x_7 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_orelse___at_lean_parser_command_universe_parser___spec__2___rarg), 6, 2);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_8);
x_0 = x_13;
x_1 = x_10;
goto _start;
}
}
}
obj* l_lean_parser_combinators_any__of___at_lean_parser_command_universe_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_12; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_lean_parser_combinators_any__of___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
lean::inc(x_6);
lean::inc(x_8);
lean::inc(x_7);
x_12 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__4___rarg(x_7, x_8, x_6, x_6, x_1, x_2, x_3, x_4);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_18; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
lean::dec(x_0);
x_18 = l_list_foldl___main___at_lean_parser_command_universe_parser___spec__3(x_13, x_15, x_1, x_2, x_3, x_4);
return x_18;
}
}
}
obj* _init_l_lean_parser_command_universe_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
x_0 = lean::mk_string("universes");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_9, 0, x_7);
x_10 = lean::box(0);
lean::inc(x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_lean_parser_command_universes;
lean::inc(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::mk_string("universe");
x_18 = l_string_trim(x_17);
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_20, 0, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_21, 0, x_18);
lean::closure_set(x_21, 1, x_4);
lean::closure_set(x_21, 2, x_20);
lean::inc(x_10);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_10);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_command_universe;
lean::inc(x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_27, 0, x_25);
lean::closure_set(x_27, 1, x_24);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_10);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_16);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
obj* l_lean_parser_command_universe_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; 
x_4 = l_lean_parser_command_universe_parser___closed__1;
lean::inc(x_4);
x_6 = l_lean_parser_combinators_any__of___at_lean_parser_command_universe_parser___spec__1(x_4, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_lean_parser_command_check() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("check");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1() {
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
obj* l_lean_parser_command_check_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1;
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_7 = x_1;
}
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; 
lean::dec(x_8);
x_13 = l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1;
lean::inc(x_13);
return x_13;
}
else
{
obj* x_15; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_15);
return x_19;
}
}
else
{
obj* x_20; obj* x_22; 
x_20 = lean::cnstr_get(x_8, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_8, 1);
lean::inc(x_22);
lean::dec(x_8);
switch (lean::obj_tag(x_20)) {
case 0:
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
lean::dec(x_20);
if (lean::is_scalar(x_7)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_7;
}
lean::cnstr_set(x_28, 0, x_25);
if (lean::obj_tag(x_22) == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_22);
x_30 = lean::box(3);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_35; 
x_32 = lean::cnstr_get(x_22, 0);
lean::inc(x_32);
lean::dec(x_22);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
}
default:
{
lean::dec(x_7);
lean::dec(x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_39; 
lean::dec(x_22);
x_39 = l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1;
lean::inc(x_39);
return x_39;
}
else
{
obj* x_41; obj* x_44; obj* x_45; 
x_41 = lean::cnstr_get(x_22, 0);
lean::inc(x_41);
lean::dec(x_22);
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_41);
return x_45;
}
}
}
}
}
}
}
obj* l_lean_parser_command_check_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_lean_parser_command_check;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
}
obj* _init_l_lean_parser_command_check_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_check_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_check_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_check_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_check_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_check_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::mk_string("#check");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = l_lean_parser_term_parser_lean_parser_has__tokens___closed__1;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_2, x_7);
x_9 = l_lean_parser_tokens___rarg(x_8);
return x_9;
}
}
obj* _init_l_lean_parser_command_check_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_24; 
x_0 = lean::mk_string("#check");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_7, 0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_lean_parser_command__parser__m_monad___closed__1;
x_13 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_14 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_15 = l_lean_parser_command__parser__m_alternative___closed__1;
x_16 = l_lean_parser_command_check;
x_17 = l_lean_parser_command_check_has__view;
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
x_24 = l_lean_parser_combinators_node_view___rarg(x_12, x_13, x_14, x_15, x_16, x_11, x_17);
return x_24;
}
}
obj* _init_l_lean_parser_command_check_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::mk_string("#check");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_7, 0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_lean_parser_command_check_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_check;
x_5 = l_lean_parser_command_check_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_attribute() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("attribute");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
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
x_8 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__1(x_5);
switch (lean::obj_tag(x_3)) {
case 1:
{
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
default:
{
obj* x_14; obj* x_16; 
lean::dec(x_3);
x_14 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_14);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
}
}
}
}
obj* l___private_init_lean_parser_combinators_3__sep__by_view__aux___main___at_lean_parser_command_attribute_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; 
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
obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_5);
x_9 = l_lean_parser_command_attr__instance_has__view;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_3);
x_13 = lean::box(0);
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_26; 
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_lean_parser_command_attr__instance_has__view;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::apply_1(x_23, x_3);
x_26 = l___private_init_lean_parser_combinators_3__sep__by_view__aux___main___at_lean_parser_command_attribute_has__view_x_27___spec__2(x_19);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
lean::dec(x_17);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_27);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_25);
lean::cnstr_set(x_32, 1, x_31);
if (lean::is_scalar(x_7)) {
 x_33 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_33 = x_7;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
return x_33;
}
default:
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_17);
x_35 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_25);
lean::cnstr_set(x_37, 1, x_35);
if (lean::is_scalar(x_7)) {
 x_38 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_38 = x_7;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_26);
return x_38;
}
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__3(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_14; 
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
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::box(0);
x_14 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__3(x_5);
if (lean::obj_tag(x_10) == 0)
{
obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_10);
x_16 = l_lean_parser_command_attr__instance_has__view;
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
x_19 = lean::apply_1(x_17, x_8);
if (lean::is_scalar(x_7)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_7;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_22 = lean::cnstr_get(x_10, 0);
lean::inc(x_22);
lean::dec(x_10);
x_25 = l_lean_parser_command_attr__instance_has__view;
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
x_28 = lean::apply_1(x_26, x_8);
x_29 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_29);
x_31 = l_option_map___rarg(x_29, x_22);
x_32 = lean::box(3);
x_33 = l_option_get__or__else___main___rarg(x_31, x_32);
if (lean::is_scalar(x_7)) {
 x_34 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_34 = x_7;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_13);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_14);
return x_36;
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__4(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__4(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_lean_parser_command_attribute_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; obj* x_7; 
x_7 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_9);
x_5 = x_9;
goto lbl_6;
}
else
{
obj* x_11; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_13 = x_7;
}
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; 
lean::dec(x_14);
lean::dec(x_13);
x_19 = lean::box(0);
x_5 = x_19;
goto lbl_6;
}
else
{
obj* x_20; obj* x_22; 
x_20 = lean::cnstr_get(x_14, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_14, 1);
lean::inc(x_22);
lean::dec(x_14);
if (lean::obj_tag(x_22) == 0)
{
lean::dec(x_22);
switch (lean::obj_tag(x_20)) {
case 0:
{
obj* x_26; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_20, 0);
lean::inc(x_26);
lean::dec(x_20);
if (lean::is_scalar(x_13)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_13;
}
lean::cnstr_set(x_29, 0, x_26);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_5 = x_30;
goto lbl_6;
}
default:
{
obj* x_33; 
lean::dec(x_13);
lean::dec(x_20);
x_33 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_33);
x_5 = x_33;
goto lbl_6;
}
}
}
else
{
obj* x_38; 
lean::dec(x_22);
lean::dec(x_13);
lean::dec(x_20);
x_38 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_38);
x_5 = x_38;
goto lbl_6;
}
}
}
lbl_6:
{
obj* x_40; obj* x_41; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_43; 
x_43 = lean::box(3);
x_40 = x_0;
x_41 = x_43;
goto lbl_42;
}
else
{
obj* x_44; obj* x_46; 
x_44 = lean::cnstr_get(x_0, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_0, 1);
lean::inc(x_46);
lean::dec(x_0);
x_40 = x_46;
x_41 = x_44;
goto lbl_42;
}
lbl_42:
{
obj* x_49; 
switch (lean::obj_tag(x_41)) {
case 0:
{
obj* x_51; obj* x_54; 
x_51 = lean::cnstr_get(x_41, 0);
lean::inc(x_51);
lean::dec(x_41);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_51);
x_49 = x_54;
goto lbl_50;
}
default:
{
obj* x_56; 
lean::dec(x_41);
x_56 = lean::box(0);
x_49 = x_56;
goto lbl_50;
}
}
lbl_50:
{
obj* x_57; obj* x_58; 
if (lean::obj_tag(x_40) == 0)
{
obj* x_60; 
x_60 = lean::box(3);
x_57 = x_40;
x_58 = x_60;
goto lbl_59;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_40, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_40, 1);
lean::inc(x_63);
lean::dec(x_40);
x_57 = x_63;
x_58 = x_61;
goto lbl_59;
}
lbl_59:
{
obj* x_66; 
switch (lean::obj_tag(x_58)) {
case 0:
{
obj* x_68; obj* x_71; 
x_68 = lean::cnstr_get(x_58, 0);
lean::inc(x_68);
lean::dec(x_58);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_68);
x_66 = x_71;
goto lbl_67;
}
default:
{
obj* x_73; 
lean::dec(x_58);
x_73 = lean::box(0);
x_66 = x_73;
goto lbl_67;
}
}
lbl_67:
{
obj* x_74; obj* x_75; 
if (lean::obj_tag(x_57) == 0)
{
obj* x_77; 
x_77 = lean::box(3);
x_74 = x_57;
x_75 = x_77;
goto lbl_76;
}
else
{
obj* x_78; obj* x_80; 
x_78 = lean::cnstr_get(x_57, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_57, 1);
lean::inc(x_80);
lean::dec(x_57);
x_74 = x_80;
x_75 = x_78;
goto lbl_76;
}
lbl_76:
{
obj* x_83; obj* x_85; 
x_85 = l_lean_parser_syntax_as__node___main(x_75);
if (lean::obj_tag(x_85) == 0)
{
obj* x_87; 
lean::dec(x_85);
x_87 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_87);
x_83 = x_87;
goto lbl_84;
}
else
{
obj* x_89; obj* x_92; obj* x_95; 
x_89 = lean::cnstr_get(x_85, 0);
lean::inc(x_89);
lean::dec(x_85);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
x_95 = l___private_init_lean_parser_combinators_3__sep__by_view__aux___main___at_lean_parser_command_attribute_has__view_x_27___spec__2(x_92);
x_83 = x_95;
goto lbl_84;
}
lbl_84:
{
obj* x_96; obj* x_97; 
if (lean::obj_tag(x_74) == 0)
{
obj* x_99; 
x_99 = lean::box(3);
x_96 = x_74;
x_97 = x_99;
goto lbl_98;
}
else
{
obj* x_100; obj* x_102; 
x_100 = lean::cnstr_get(x_74, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_74, 1);
lean::inc(x_102);
lean::dec(x_74);
x_96 = x_102;
x_97 = x_100;
goto lbl_98;
}
lbl_98:
{
obj* x_105; 
switch (lean::obj_tag(x_97)) {
case 0:
{
obj* x_107; obj* x_110; 
x_107 = lean::cnstr_get(x_97, 0);
lean::inc(x_107);
lean::dec(x_97);
x_110 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_110, 0, x_107);
x_105 = x_110;
goto lbl_106;
}
default:
{
obj* x_112; 
lean::dec(x_97);
x_112 = lean::box(0);
x_105 = x_112;
goto lbl_106;
}
}
lbl_106:
{
obj* x_113; 
if (lean::obj_tag(x_96) == 0)
{
obj* x_116; 
lean::dec(x_96);
x_116 = lean::box(3);
x_113 = x_116;
goto lbl_114;
}
else
{
obj* x_117; 
x_117 = lean::cnstr_get(x_96, 0);
lean::inc(x_117);
lean::dec(x_96);
x_113 = x_117;
goto lbl_114;
}
lbl_114:
{
obj* x_120; 
x_120 = l_lean_parser_syntax_as__node___main(x_113);
if (lean::obj_tag(x_120) == 0)
{
obj* x_122; obj* x_124; 
lean::dec(x_120);
x_122 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_122);
x_124 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_124, 0, x_5);
lean::cnstr_set(x_124, 1, x_49);
lean::cnstr_set(x_124, 2, x_66);
lean::cnstr_set(x_124, 3, x_83);
lean::cnstr_set(x_124, 4, x_105);
lean::cnstr_set(x_124, 5, x_122);
return x_124;
}
else
{
obj* x_125; obj* x_128; obj* x_131; obj* x_132; 
x_125 = lean::cnstr_get(x_120, 0);
lean::inc(x_125);
lean::dec(x_120);
x_128 = lean::cnstr_get(x_125, 1);
lean::inc(x_128);
lean::dec(x_125);
x_131 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__1(x_128);
x_132 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_132, 0, x_5);
lean::cnstr_set(x_132, 1, x_49);
lean::cnstr_set(x_132, 2, x_66);
lean::cnstr_set(x_132, 3, x_83);
lean::cnstr_set(x_132, 4, x_105);
lean::cnstr_set(x_132, 5, x_131);
return x_132;
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
obj* l_lean_parser_command_attribute_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_attribute_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
else
{
obj* x_20; obj* x_22; obj* x_25; 
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_25 = l_lean_parser_syntax_as__node___main(x_20);
if (lean::obj_tag(x_25) == 0)
{
lean::dec(x_25);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; 
x_27 = lean::box(3);
x_1 = x_22;
x_2 = x_27;
goto lbl_3;
}
else
{
obj* x_28; obj* x_30; 
x_28 = lean::cnstr_get(x_22, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_22, 1);
lean::inc(x_30);
lean::dec(x_22);
x_1 = x_30;
x_2 = x_28;
goto lbl_3;
}
}
else
{
obj* x_33; obj* x_36; obj* x_39; 
x_33 = lean::cnstr_get(x_25, 0);
lean::inc(x_33);
lean::dec(x_25);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_list_append___rarg(x_36, x_22);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; 
x_40 = lean::box(3);
x_1 = x_39;
x_2 = x_40;
goto lbl_3;
}
else
{
obj* x_41; obj* x_43; 
x_41 = lean::cnstr_get(x_39, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_39, 1);
lean::inc(x_43);
lean::dec(x_39);
x_1 = x_43;
x_2 = x_41;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_46; obj* x_48; 
x_48 = l_lean_parser_syntax_as__node___main(x_2);
if (lean::obj_tag(x_48) == 0)
{
obj* x_50; 
lean::dec(x_48);
x_50 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_50);
x_46 = x_50;
goto lbl_47;
}
else
{
obj* x_52; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_48, 0);
lean::inc(x_52);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_54 = x_48;
}
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_60; 
lean::dec(x_54);
lean::dec(x_55);
x_60 = lean::box(0);
x_46 = x_60;
goto lbl_47;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_55, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_55, 1);
lean::inc(x_63);
lean::dec(x_55);
if (lean::obj_tag(x_63) == 0)
{
lean::dec(x_63);
switch (lean::obj_tag(x_61)) {
case 0:
{
obj* x_67; obj* x_70; obj* x_71; 
x_67 = lean::cnstr_get(x_61, 0);
lean::inc(x_67);
lean::dec(x_61);
if (lean::is_scalar(x_54)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_54;
}
lean::cnstr_set(x_70, 0, x_67);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
x_46 = x_71;
goto lbl_47;
}
default:
{
obj* x_74; 
lean::dec(x_61);
lean::dec(x_54);
x_74 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_74);
x_46 = x_74;
goto lbl_47;
}
}
}
else
{
obj* x_79; 
lean::dec(x_61);
lean::dec(x_54);
lean::dec(x_63);
x_79 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_79);
x_46 = x_79;
goto lbl_47;
}
}
}
lbl_47:
{
obj* x_81; obj* x_82; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_84; 
x_84 = lean::box(3);
x_81 = x_1;
x_82 = x_84;
goto lbl_83;
}
else
{
obj* x_85; obj* x_87; 
x_85 = lean::cnstr_get(x_1, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_1, 1);
lean::inc(x_87);
lean::dec(x_1);
x_81 = x_87;
x_82 = x_85;
goto lbl_83;
}
lbl_83:
{
obj* x_90; 
switch (lean::obj_tag(x_82)) {
case 0:
{
obj* x_92; obj* x_95; 
x_92 = lean::cnstr_get(x_82, 0);
lean::inc(x_92);
lean::dec(x_82);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_92);
x_90 = x_95;
goto lbl_91;
}
default:
{
obj* x_97; 
lean::dec(x_82);
x_97 = lean::box(0);
x_90 = x_97;
goto lbl_91;
}
}
lbl_91:
{
obj* x_98; obj* x_99; 
if (lean::obj_tag(x_81) == 0)
{
obj* x_101; 
x_101 = lean::box(3);
x_98 = x_81;
x_99 = x_101;
goto lbl_100;
}
else
{
obj* x_102; obj* x_104; 
x_102 = lean::cnstr_get(x_81, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_81, 1);
lean::inc(x_104);
lean::dec(x_81);
x_98 = x_104;
x_99 = x_102;
goto lbl_100;
}
lbl_100:
{
obj* x_107; 
switch (lean::obj_tag(x_99)) {
case 0:
{
obj* x_109; obj* x_112; 
x_109 = lean::cnstr_get(x_99, 0);
lean::inc(x_109);
lean::dec(x_99);
x_112 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_112, 0, x_109);
x_107 = x_112;
goto lbl_108;
}
default:
{
obj* x_114; 
lean::dec(x_99);
x_114 = lean::box(0);
x_107 = x_114;
goto lbl_108;
}
}
lbl_108:
{
obj* x_115; obj* x_116; 
if (lean::obj_tag(x_98) == 0)
{
obj* x_118; 
x_118 = lean::box(3);
x_115 = x_98;
x_116 = x_118;
goto lbl_117;
}
else
{
obj* x_119; obj* x_121; 
x_119 = lean::cnstr_get(x_98, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_98, 1);
lean::inc(x_121);
lean::dec(x_98);
x_115 = x_121;
x_116 = x_119;
goto lbl_117;
}
lbl_117:
{
obj* x_124; obj* x_126; 
x_126 = l_lean_parser_syntax_as__node___main(x_116);
if (lean::obj_tag(x_126) == 0)
{
obj* x_128; 
lean::dec(x_126);
x_128 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_128);
x_124 = x_128;
goto lbl_125;
}
else
{
obj* x_130; obj* x_133; obj* x_136; 
x_130 = lean::cnstr_get(x_126, 0);
lean::inc(x_130);
lean::dec(x_126);
x_133 = lean::cnstr_get(x_130, 1);
lean::inc(x_133);
lean::dec(x_130);
x_136 = l___private_init_lean_parser_combinators_3__sep__by_view__aux___main___at_lean_parser_command_attribute_has__view_x_27___spec__2(x_133);
x_124 = x_136;
goto lbl_125;
}
lbl_125:
{
obj* x_137; obj* x_138; 
if (lean::obj_tag(x_115) == 0)
{
obj* x_140; 
x_140 = lean::box(3);
x_137 = x_115;
x_138 = x_140;
goto lbl_139;
}
else
{
obj* x_141; obj* x_143; 
x_141 = lean::cnstr_get(x_115, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_115, 1);
lean::inc(x_143);
lean::dec(x_115);
x_137 = x_143;
x_138 = x_141;
goto lbl_139;
}
lbl_139:
{
obj* x_146; 
switch (lean::obj_tag(x_138)) {
case 0:
{
obj* x_148; obj* x_151; 
x_148 = lean::cnstr_get(x_138, 0);
lean::inc(x_148);
lean::dec(x_138);
x_151 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_151, 0, x_148);
x_146 = x_151;
goto lbl_147;
}
default:
{
obj* x_153; 
lean::dec(x_138);
x_153 = lean::box(0);
x_146 = x_153;
goto lbl_147;
}
}
lbl_147:
{
obj* x_154; 
if (lean::obj_tag(x_137) == 0)
{
obj* x_157; 
lean::dec(x_137);
x_157 = lean::box(3);
x_154 = x_157;
goto lbl_155;
}
else
{
obj* x_158; 
x_158 = lean::cnstr_get(x_137, 0);
lean::inc(x_158);
lean::dec(x_137);
x_154 = x_158;
goto lbl_155;
}
lbl_155:
{
obj* x_161; 
x_161 = l_lean_parser_syntax_as__node___main(x_154);
if (lean::obj_tag(x_161) == 0)
{
obj* x_163; obj* x_165; 
lean::dec(x_161);
x_163 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_163);
x_165 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_165, 0, x_46);
lean::cnstr_set(x_165, 1, x_90);
lean::cnstr_set(x_165, 2, x_107);
lean::cnstr_set(x_165, 3, x_124);
lean::cnstr_set(x_165, 4, x_146);
lean::cnstr_set(x_165, 5, x_163);
return x_165;
}
else
{
obj* x_166; obj* x_169; obj* x_172; obj* x_173; 
x_166 = lean::cnstr_get(x_161, 0);
lean::inc(x_166);
lean::dec(x_161);
x_169 = lean::cnstr_get(x_166, 1);
lean::inc(x_169);
lean::dec(x_166);
x_172 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__1(x_169);
x_173 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_173, 0, x_46);
lean::cnstr_set(x_173, 1, x_90);
lean::cnstr_set(x_173, 2, x_107);
lean::cnstr_set(x_173, 3, x_124);
lean::cnstr_set(x_173, 4, x_146);
lean::cnstr_set(x_173, 5, x_172);
return x_173;
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
obj* l_lean_parser_command_attribute_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
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
lean::dec(x_0);
x_14 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_14);
x_16 = l_option_map___rarg(x_14, x_3);
x_17 = lean::box(3);
lean::inc(x_17);
x_19 = l_option_get__or__else___main___rarg(x_16, x_17);
x_20 = lean::box(0);
lean::inc(x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_20);
lean::inc(x_14);
x_24 = l_option_map___rarg(x_14, x_5);
lean::inc(x_17);
x_26 = l_option_get__or__else___main___rarg(x_24, x_17);
x_27 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__3(x_7);
x_28 = l_list_join___main___rarg(x_27);
x_29 = l_lean_parser_no__kind;
lean::inc(x_29);
x_31 = l_lean_parser_syntax_mk__node(x_29, x_28);
lean::inc(x_14);
x_33 = l_option_map___rarg(x_14, x_9);
lean::inc(x_17);
x_35 = l_option_get__or__else___main___rarg(x_33, x_17);
x_36 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__4(x_11);
lean::inc(x_29);
x_38 = l_lean_parser_syntax_mk__node(x_29, x_36);
lean::inc(x_20);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_20);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_35);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_31);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_26);
lean::cnstr_set(x_43, 1, x_42);
if (lean::obj_tag(x_1) == 0)
{
obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_55; 
lean::dec(x_17);
lean::dec(x_20);
lean::dec(x_1);
x_47 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_47);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_22);
lean::inc(x_29);
x_51 = l_lean_parser_syntax_mk__node(x_29, x_49);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_43);
x_53 = l_lean_parser_command_attribute;
lean::inc(x_53);
x_55 = l_lean_parser_syntax_mk__node(x_53, x_52);
return x_55;
}
else
{
obj* x_56; obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_71; 
x_56 = lean::cnstr_get(x_1, 0);
lean::inc(x_56);
lean::dec(x_1);
lean::inc(x_14);
x_60 = l_option_map___rarg(x_14, x_56);
x_61 = l_option_get__or__else___main___rarg(x_60, x_17);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_20);
lean::inc(x_29);
x_64 = l_lean_parser_syntax_mk__node(x_29, x_62);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_22);
lean::inc(x_29);
x_67 = l_lean_parser_syntax_mk__node(x_29, x_65);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_43);
x_69 = l_lean_parser_command_attribute;
lean::inc(x_69);
x_71 = l_lean_parser_syntax_mk__node(x_69, x_68);
return x_71;
}
}
}
obj* _init_l_lean_parser_command_attribute_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attribute_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attribute_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_attribute_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_attribute_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_attribute_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_0 = lean::mk_string("local ");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = l_lean_parser_tokens___rarg(x_3);
x_5 = lean::mk_string("attribute ");
lean::inc(x_1);
x_7 = l_lean_parser_symbol_tokens___rarg(x_5, x_1);
x_8 = lean::box(0);
lean::inc(x_8);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_7, x_8);
x_11 = l_lean_parser_list_cons_tokens___rarg(x_4, x_10);
x_12 = l_lean_parser_tokens___rarg(x_11);
x_13 = l_lean_parser_tokens___rarg(x_12);
x_14 = lean::mk_string("[");
lean::inc(x_1);
x_16 = l_lean_parser_symbol_tokens___rarg(x_14, x_1);
x_17 = lean::mk_string(", ");
lean::inc(x_1);
x_19 = l_lean_parser_symbol_tokens___rarg(x_17, x_1);
x_20 = l_lean_parser_command_attr__instance_parser_lean_parser_has__tokens;
lean::inc(x_20);
x_22 = l_lean_parser_combinators_sep__by1_tokens___rarg(x_20, x_19);
x_23 = lean::mk_string("] ");
x_24 = l_lean_parser_symbol_tokens___rarg(x_23, x_1);
lean::inc(x_8);
x_26 = l_lean_parser_tokens___rarg(x_8);
x_27 = l_lean_parser_list_cons_tokens___rarg(x_26, x_8);
x_28 = l_lean_parser_list_cons_tokens___rarg(x_24, x_27);
x_29 = l_lean_parser_list_cons_tokens___rarg(x_22, x_28);
x_30 = l_lean_parser_list_cons_tokens___rarg(x_16, x_29);
x_31 = l_lean_parser_list_cons_tokens___rarg(x_13, x_30);
x_32 = l_lean_parser_tokens___rarg(x_31);
return x_32;
}
}
obj* _init_l_lean_parser_command_attribute_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_59; 
x_0 = lean::mk_string("local ");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_string("attribute ");
x_9 = l_string_trim(x_8);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
lean::inc(x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_4);
lean::closure_set(x_13, 2, x_11);
x_14 = lean::box(0);
lean::inc(x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_7);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::mk_string("[");
x_20 = l_string_trim(x_19);
lean::inc(x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_22, 0, x_20);
lean::inc(x_4);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_4);
lean::closure_set(x_24, 2, x_22);
x_25 = lean::mk_string(", ");
x_26 = l_string_trim(x_25);
lean::inc(x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_28, 0, x_26);
lean::inc(x_4);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_4);
lean::closure_set(x_30, 2, x_28);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attr__instance_parser), 4, 0);
x_32 = 1;
x_33 = lean::box(x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__tokens___spec__1___boxed), 7, 3);
lean::closure_set(x_34, 0, x_31);
lean::closure_set(x_34, 1, x_30);
lean::closure_set(x_34, 2, x_33);
x_35 = lean::mk_string("] ");
x_36 = l_string_trim(x_35);
lean::inc(x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_38, 0, x_36);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_39, 0, x_36);
lean::closure_set(x_39, 1, x_4);
lean::closure_set(x_39, 2, x_38);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__2), 5, 1);
lean::closure_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_14);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_34);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_18);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_lean_parser_command__parser__m_monad___closed__1;
x_48 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_49 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_50 = l_lean_parser_command__parser__m_alternative___closed__1;
x_51 = l_lean_parser_command_attribute;
x_52 = l_lean_parser_command_attribute_has__view;
lean::inc(x_52);
lean::inc(x_51);
lean::inc(x_50);
lean::inc(x_49);
lean::inc(x_48);
lean::inc(x_47);
x_59 = l_lean_parser_combinators_node_view___rarg(x_47, x_48, x_49, x_50, x_51, x_46, x_52);
return x_59;
}
}
obj* _init_l_lean_parser_command_attribute_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_0 = lean::mk_string("local ");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_string("attribute ");
x_9 = l_string_trim(x_8);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
lean::inc(x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_4);
lean::closure_set(x_13, 2, x_11);
x_14 = lean::box(0);
lean::inc(x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_7);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::mk_string("[");
x_20 = l_string_trim(x_19);
lean::inc(x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_22, 0, x_20);
lean::inc(x_4);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_4);
lean::closure_set(x_24, 2, x_22);
x_25 = lean::mk_string(", ");
x_26 = l_string_trim(x_25);
lean::inc(x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_28, 0, x_26);
lean::inc(x_4);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_4);
lean::closure_set(x_30, 2, x_28);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attr__instance_parser), 4, 0);
x_32 = 1;
x_33 = lean::box(x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__tokens___spec__1___boxed), 7, 3);
lean::closure_set(x_34, 0, x_31);
lean::closure_set(x_34, 1, x_30);
lean::closure_set(x_34, 2, x_33);
x_35 = lean::mk_string("] ");
x_36 = l_string_trim(x_35);
lean::inc(x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_38, 0, x_36);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_39, 0, x_36);
lean::closure_set(x_39, 1, x_4);
lean::closure_set(x_39, 2, x_38);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__2), 5, 1);
lean::closure_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_14);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_34);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_18);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
}
obj* l_lean_parser_command_attribute_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_attribute;
x_5 = l_lean_parser_command_attribute_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_init__quot() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("init_quot");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_command_init__quot_has__view_x_27___lambda__1(obj* x_0) {
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
x_8 = l_lean_parser_command_init__quot;
lean::inc(x_8);
x_10 = l_lean_parser_syntax_mk__node(x_8, x_7);
return x_10;
}
}
obj* _init_l_lean_parser_command_init__quot_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_init__quot_has__view_x_27___lambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_init__quot_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_init__quot_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_init__quot_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::mk_string("init_quot");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_2, x_3);
x_5 = l_lean_parser_tokens___rarg(x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_init__quot_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_20; 
x_0 = lean::mk_string("init_quot");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_lean_parser_command__parser__m_monad___closed__1;
x_9 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_10 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_11 = l_lean_parser_command__parser__m_alternative___closed__1;
x_12 = l_lean_parser_command_init__quot;
x_13 = l_lean_parser_command_init__quot_has__view;
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
obj* _init_l_lean_parser_command_init__quot_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::mk_string("init_quot");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
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
obj* l_lean_parser_command_init__quot_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_init__quot;
x_5 = l_lean_parser_command_init__quot_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_bool__option__value() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("bool_option_value");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
if (x_6 == 0)
{
obj* x_9; 
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_0);
return x_9;
}
else
{
obj* x_10; 
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_0);
return x_10;
}
}
}
}
obj* _init_l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("bool_option_value");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__2;
x_17 = lean_name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 2:
{
obj* x_43; obj* x_45; obj* x_48; uint8 x_49; 
x_43 = lean::cnstr_get(x_38, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_38, 1);
lean::inc(x_45);
lean::dec(x_38);
x_48 = lean::box(0);
x_49 = lean_name_dec_eq(x_43, x_48);
lean::dec(x_48);
lean::dec(x_43);
if (x_49 == 0)
{
obj* x_54; 
lean::dec(x_40);
lean::dec(x_45);
x_54 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_54);
return x_54;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_58; 
lean::dec(x_40);
lean::dec(x_45);
x_58 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_58);
return x_58;
}
else
{
obj* x_60; obj* x_62; 
x_60 = lean::cnstr_get(x_40, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_40, 1);
lean::inc(x_62);
lean::dec(x_40);
if (lean::obj_tag(x_62) == 0)
{
lean::dec(x_62);
x_1 = x_60;
x_2 = x_45;
goto lbl_3;
}
else
{
obj* x_69; 
lean::dec(x_45);
lean::dec(x_60);
lean::dec(x_62);
x_69 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_69);
return x_69;
}
}
}
}
default:
{
obj* x_73; 
lean::dec(x_38);
lean::dec(x_40);
x_73 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_73);
return x_73;
}
}
}
}
else
{
obj* x_77; 
lean::dec(x_25);
lean::dec(x_27);
x_77 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
return x_77;
}
}
}
}
lbl_3:
{
obj* x_79; uint8 x_80; 
x_79 = lean::mk_nat_obj(0u);
x_80 = lean::nat_dec_eq(x_2, x_79);
lean::dec(x_79);
lean::dec(x_2);
if (x_80 == 0)
{
obj* x_83; 
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_1);
return x_83;
}
else
{
obj* x_84; 
x_84 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_84, 0, x_1);
return x_84;
}
}
}
}
obj* l_lean_parser_command_bool__option__value_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_7);
x_9 = l_lean_parser_syntax_mk__node(x_7, x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_lean_parser_command_bool__option__value;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
return x_13;
}
else
{
obj* x_14; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
lean::inc(x_1);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_1);
x_19 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_19);
x_21 = l_lean_parser_syntax_mk__node(x_19, x_18);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_1);
x_23 = l_lean_parser_command_bool__option__value;
lean::inc(x_23);
x_25 = l_lean_parser_syntax_mk__node(x_23, x_22);
return x_25;
}
}
}
obj* _init_l_lean_parser_command_bool__option__value_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_bool__option__value_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_bool__option__value_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_bool__option__value_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_option__value() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("option_value");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_dec_eq(x_1, x_8);
lean::dec(x_8);
lean::dec(x_1);
if (x_9 == 0)
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = l_lean_parser_number_has__view;
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::apply_1(x_13, x_0);
x_16 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_17 = l_lean_parser_string__lit_has__view;
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::apply_1(x_18, x_0);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
else
{
obj* x_23; obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_1);
x_23 = l_lean_parser_command_bool__option__value_has__view;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::apply_1(x_24, x_0);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
}
}
}
obj* _init_l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("option_value");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_command_option__value_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__2;
x_17 = lean_name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 2:
{
obj* x_43; obj* x_45; obj* x_48; uint8 x_49; 
x_43 = lean::cnstr_get(x_38, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_38, 1);
lean::inc(x_45);
lean::dec(x_38);
x_48 = lean::box(0);
x_49 = lean_name_dec_eq(x_43, x_48);
lean::dec(x_48);
lean::dec(x_43);
if (x_49 == 0)
{
obj* x_54; 
lean::dec(x_40);
lean::dec(x_45);
x_54 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_54);
return x_54;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_58; 
lean::dec(x_40);
lean::dec(x_45);
x_58 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_58);
return x_58;
}
else
{
obj* x_60; obj* x_62; 
x_60 = lean::cnstr_get(x_40, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_40, 1);
lean::inc(x_62);
lean::dec(x_40);
if (lean::obj_tag(x_62) == 0)
{
lean::dec(x_62);
x_1 = x_60;
x_2 = x_45;
goto lbl_3;
}
else
{
obj* x_69; 
lean::dec(x_45);
lean::dec(x_60);
lean::dec(x_62);
x_69 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_69);
return x_69;
}
}
}
}
default:
{
obj* x_73; 
lean::dec(x_38);
lean::dec(x_40);
x_73 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_73);
return x_73;
}
}
}
}
else
{
obj* x_77; 
lean::dec(x_25);
lean::dec(x_27);
x_77 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
return x_77;
}
}
}
}
lbl_3:
{
obj* x_79; uint8 x_80; 
x_79 = lean::mk_nat_obj(0u);
x_80 = lean::nat_dec_eq(x_2, x_79);
lean::dec(x_79);
if (x_80 == 0)
{
obj* x_82; uint8 x_83; 
x_82 = lean::mk_nat_obj(1u);
x_83 = lean::nat_dec_eq(x_2, x_82);
lean::dec(x_82);
lean::dec(x_2);
if (x_83 == 0)
{
obj* x_86; obj* x_87; obj* x_89; obj* x_90; 
x_86 = l_lean_parser_number_has__view;
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_89 = lean::apply_1(x_87, x_1);
x_90 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
return x_90;
}
else
{
obj* x_91; obj* x_92; obj* x_94; obj* x_95; 
x_91 = l_lean_parser_string__lit_has__view;
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_94 = lean::apply_1(x_92, x_1);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
}
else
{
obj* x_97; obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_2);
x_97 = l_lean_parser_command_bool__option__value_has__view;
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
x_100 = lean::apply_1(x_98, x_1);
x_101 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
}
}
}
obj* l_lean_parser_command_option__value_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_command_bool__option__value_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_2);
lean::inc(x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_lean_parser_command_option__value;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
case 1:
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_lean_parser_string__lit_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_18);
lean::inc(x_1);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_1);
x_27 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_27);
x_29 = l_lean_parser_syntax_mk__node(x_27, x_26);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_1);
x_31 = l_lean_parser_command_option__value;
lean::inc(x_31);
x_33 = l_lean_parser_syntax_mk__node(x_31, x_30);
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_49; 
x_34 = lean::cnstr_get(x_0, 0);
lean::inc(x_34);
lean::dec(x_0);
x_37 = l_lean_parser_number_has__view;
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
x_40 = lean::apply_1(x_38, x_34);
lean::inc(x_1);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_1);
x_43 = l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
lean::inc(x_43);
x_45 = l_lean_parser_syntax_mk__node(x_43, x_42);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_1);
x_47 = l_lean_parser_command_option__value;
lean::inc(x_47);
x_49 = l_lean_parser_syntax_mk__node(x_47, x_46);
return x_49;
}
}
}
}
obj* _init_l_lean_parser_command_option__value_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_option__value_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_option__value_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_option__value_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_option__value_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_set__option() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("set_option");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_option__value_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
}
lbl_6:
{
obj* x_13; obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_13 = x_0;
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::dec(x_0);
x_13 = x_19;
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_22; 
switch (lean::obj_tag(x_14)) {
case 1:
{
obj* x_24; 
x_24 = lean::cnstr_get(x_14, 0);
lean::inc(x_24);
lean::dec(x_14);
if (lean::obj_tag(x_13) == 0)
{
obj* x_28; obj* x_30; 
lean::dec(x_13);
x_28 = l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::cnstr_set(x_30, 1, x_24);
lean::cnstr_set(x_30, 2, x_28);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_35; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_13, 0);
lean::inc(x_31);
lean::dec(x_13);
x_34 = l_lean_parser_command_option__value_has__view;
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::apply_1(x_35, x_31);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_5);
lean::cnstr_set(x_38, 1, x_24);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
}
default:
{
obj* x_40; 
lean::dec(x_14);
x_40 = lean::box(0);
x_22 = x_40;
goto lbl_23;
}
}
lbl_23:
{
lean::dec(x_22);
if (lean::obj_tag(x_13) == 0)
{
obj* x_43; obj* x_44; obj* x_47; 
lean::dec(x_13);
x_43 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
x_44 = l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1;
lean::inc(x_44);
lean::inc(x_43);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_5);
lean::cnstr_set(x_47, 1, x_43);
lean::cnstr_set(x_47, 2, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_57; 
x_48 = lean::cnstr_get(x_13, 0);
lean::inc(x_48);
lean::dec(x_13);
x_51 = l_lean_parser_command_option__value_has__view;
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_54 = lean::apply_1(x_52, x_48);
x_55 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_5);
lean::cnstr_set(x_57, 1, x_55);
lean::cnstr_set(x_57, 2, x_54);
return x_57;
}
}
}
}
}
}
}
obj* l_lean_parser_command_set__option_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__2;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
}
lbl_21:
{
obj* x_28; obj* x_29; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_31; 
x_31 = lean::box(3);
x_28 = x_1;
x_29 = x_31;
goto lbl_30;
}
else
{
obj* x_32; obj* x_34; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_1, 1);
lean::inc(x_34);
lean::dec(x_1);
x_28 = x_34;
x_29 = x_32;
goto lbl_30;
}
lbl_30:
{
obj* x_37; 
switch (lean::obj_tag(x_29)) {
case 1:
{
obj* x_39; 
x_39 = lean::cnstr_get(x_29, 0);
lean::inc(x_39);
lean::dec(x_29);
if (lean::obj_tag(x_28) == 0)
{
obj* x_43; obj* x_45; 
lean::dec(x_28);
x_43 = l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_20);
lean::cnstr_set(x_45, 1, x_39);
lean::cnstr_set(x_45, 2, x_43);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_50; obj* x_52; obj* x_53; 
x_46 = lean::cnstr_get(x_28, 0);
lean::inc(x_46);
lean::dec(x_28);
x_49 = l_lean_parser_command_option__value_has__view;
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::apply_1(x_50, x_46);
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_20);
lean::cnstr_set(x_53, 1, x_39);
lean::cnstr_set(x_53, 2, x_52);
return x_53;
}
}
default:
{
obj* x_55; 
lean::dec(x_29);
x_55 = lean::box(0);
x_37 = x_55;
goto lbl_38;
}
}
lbl_38:
{
lean::dec(x_37);
if (lean::obj_tag(x_28) == 0)
{
obj* x_58; obj* x_59; obj* x_62; 
lean::dec(x_28);
x_58 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
x_59 = l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1;
lean::inc(x_59);
lean::inc(x_58);
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_20);
lean::cnstr_set(x_62, 1, x_58);
lean::cnstr_set(x_62, 2, x_59);
return x_62;
}
else
{
obj* x_63; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_72; 
x_63 = lean::cnstr_get(x_28, 0);
lean::inc(x_63);
lean::dec(x_28);
x_66 = l_lean_parser_command_option__value_has__view;
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_69 = lean::apply_1(x_67, x_63);
x_70 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_70);
x_72 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_72, 0, x_20);
lean::cnstr_set(x_72, 1, x_70);
lean::cnstr_set(x_72, 2, x_69);
return x_72;
}
}
}
}
}
}
}
obj* l_lean_parser_command_set__option_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
x_12 = l_option_get__or__else___main___rarg(x_10, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_3);
x_14 = l_lean_parser_command_option__value_has__view;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::apply_1(x_15, x_5);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_13);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_12);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_lean_parser_command_set__option;
lean::inc(x_22);
x_24 = l_lean_parser_syntax_mk__node(x_22, x_21);
return x_24;
}
}
obj* _init_l_lean_parser_command_set__option_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_set__option_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_set__option_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_command_set__option_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_set__option_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_symbol__or__ident___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_11; obj* x_12; obj* x_14; obj* x_16; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_6);
x_11 = l_lean_parser_token(x_6, x_3, x_4);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_12, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_12, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_12, 2);
lean::inc(x_21);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 lean::cnstr_release(x_12, 2);
 x_23 = x_12;
}
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_26; obj* x_28; obj* x_31; 
x_26 = lean::cnstr_get(x_17, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_26, 1);
lean::inc(x_28);
lean::dec(x_26);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_28);
x_24 = x_31;
goto lbl_25;
}
case 1:
{
obj* x_32; obj* x_34; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_17, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_32, 1);
lean::inc(x_34);
lean::dec(x_32);
x_37 = l_lean_parser_substring_to__string(x_34);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_24 = x_38;
goto lbl_25;
}
default:
{
obj* x_39; 
x_39 = lean::box(0);
x_24 = x_39;
goto lbl_25;
}
}
lbl_25:
{
uint8 x_40; 
if (lean::obj_tag(x_24) == 0)
{
uint8 x_43; 
lean::dec(x_24);
x_43 = 1;
x_40 = x_43;
goto lbl_41;
}
else
{
obj* x_44; uint8 x_47; 
x_44 = lean::cnstr_get(x_24, 0);
lean::inc(x_44);
lean::dec(x_24);
x_47 = lean::string_dec_eq(x_44, x_0);
lean::dec(x_44);
if (x_47 == 0)
{
uint8 x_49; 
x_49 = 1;
x_40 = x_49;
goto lbl_41;
}
else
{
uint8 x_50; 
x_50 = 0;
x_40 = x_50;
goto lbl_41;
}
}
lbl_41:
{
if (x_40 == 0)
{
obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
x_54 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_54);
if (lean::is_scalar(x_23)) {
 x_56 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_56 = x_23;
}
lean::cnstr_set(x_56, 0, x_17);
lean::cnstr_set(x_56, 1, x_19);
lean::cnstr_set(x_56, 2, x_54);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_56);
x_58 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_58);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_57);
x_61 = l_lean_parser_parsec__t_try__mk__res___rarg(x_60);
if (lean::is_scalar(x_16)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_16;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_14);
return x_62;
}
else
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_72; 
x_63 = l_string_quote(x_0);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_64, 0, x_63);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_3);
x_66 = lean::box(0);
x_67 = l_string_join___closed__1;
lean::inc(x_67);
x_69 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_67, x_64, x_65, x_66, x_6, x_19, x_14);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
lean::dec(x_69);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_77; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_87; obj* x_88; 
x_75 = lean::cnstr_get(x_70, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_70, 2);
lean::inc(x_77);
lean::dec(x_70);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_80);
if (lean::is_scalar(x_23)) {
 x_82 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_82 = x_23;
}
lean::cnstr_set(x_82, 0, x_17);
lean::cnstr_set(x_82, 1, x_75);
lean::cnstr_set(x_82, 2, x_80);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_83);
lean::inc(x_80);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_84);
x_87 = l_lean_parser_parsec__t_try__mk__res___rarg(x_86);
if (lean::is_scalar(x_16)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_16;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_72);
return x_88;
}
else
{
obj* x_91; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_17);
lean::dec(x_23);
x_91 = lean::cnstr_get(x_70, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_94 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_94 = x_70;
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_91);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
x_96 = x_95;
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_96);
x_98 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_98);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_97);
x_101 = l_lean_parser_parsec__t_try__mk__res___rarg(x_100);
if (lean::is_scalar(x_16)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_16;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_72);
return x_102;
}
}
}
}
}
else
{
obj* x_106; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
x_106 = lean::cnstr_get(x_12, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_109 = x_12;
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set_scalar(x_110, sizeof(void*)*1, x_108);
x_111 = x_110;
x_112 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_112);
x_114 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_112, x_111);
x_115 = l_lean_parser_parsec__t_try__mk__res___rarg(x_114);
if (lean::is_scalar(x_16)) {
 x_116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_116 = x_16;
}
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_14);
return x_116;
}
}
}
obj* l_lean_parser_string__lit_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_5);
x_10 = l_lean_parser_token(x_5, x_2, x_3);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_11, 2);
lean::inc(x_20);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_22 = x_11;
}
lean::inc(x_16);
x_24 = l_lean_parser_try__view___at_lean_parser_string__lit_parser___spec__1(x_16);
if (lean::obj_tag(x_24) == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_35; obj* x_37; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_16);
lean::dec(x_22);
lean::dec(x_24);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_2);
x_29 = lean::box(0);
x_30 = l_string_join___closed__1;
x_31 = l_lean_parser_string__lit_parser___at_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_31);
lean::inc(x_30);
x_34 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_30, x_31, x_28, x_29, x_5, x_18, x_13);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_40 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_40);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_35);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_42);
lean::inc(x_40);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_43);
lean::inc(x_31);
x_47 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_45, x_31);
x_48 = l_lean_parser_parsec__t_try__mk__res___rarg(x_47);
if (lean::is_scalar(x_15)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_15;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_37);
return x_49;
}
else
{
obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_5);
lean::dec(x_24);
lean::dec(x_2);
x_53 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_53);
if (lean::is_scalar(x_22)) {
 x_55 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_55 = x_22;
}
lean::cnstr_set(x_55, 0, x_16);
lean::cnstr_set(x_55, 1, x_18);
lean::cnstr_set(x_55, 2, x_53);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_55);
x_57 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_57);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_56);
x_60 = l_lean_parser_string__lit_parser___at_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_60);
x_62 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_59, x_60);
x_63 = l_lean_parser_parsec__t_try__mk__res___rarg(x_62);
if (lean::is_scalar(x_15)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_15;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_13);
return x_64;
}
}
else
{
obj* x_67; uint8 x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_5);
lean::dec(x_2);
x_67 = lean::cnstr_get(x_11, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_70 = x_11;
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_67);
lean::cnstr_set_scalar(x_71, sizeof(void*)*1, x_69);
x_72 = x_71;
x_73 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_73);
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_72);
x_76 = l_lean_parser_string__lit_parser___at_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_76);
x_78 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_75, x_76);
x_79 = l_lean_parser_parsec__t_try__mk__res___rarg(x_78);
if (lean::is_scalar(x_15)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_15;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_13);
return x_80;
}
}
}
obj* l_lean_parser_number_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_5);
x_10 = l_lean_parser_token(x_5, x_2, x_3);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_11, 2);
lean::inc(x_20);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_22 = x_11;
}
lean::inc(x_16);
x_24 = l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(x_16);
if (lean::obj_tag(x_24) == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_35; obj* x_37; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_16);
lean::dec(x_22);
lean::dec(x_24);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_2);
x_29 = lean::box(0);
x_30 = l_string_join___closed__1;
x_31 = l_lean_parser_number_parser___at_lean_parser_command_notation__spec_precedence__lit_parser_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_31);
lean::inc(x_30);
x_34 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_30, x_31, x_28, x_29, x_5, x_18, x_13);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_40 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_40);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_35);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_42);
lean::inc(x_40);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_43);
lean::inc(x_31);
x_47 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_45, x_31);
x_48 = l_lean_parser_parsec__t_try__mk__res___rarg(x_47);
if (lean::is_scalar(x_15)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_15;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_37);
return x_49;
}
else
{
obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_5);
lean::dec(x_24);
lean::dec(x_2);
x_53 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_53);
if (lean::is_scalar(x_22)) {
 x_55 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_55 = x_22;
}
lean::cnstr_set(x_55, 0, x_16);
lean::cnstr_set(x_55, 1, x_18);
lean::cnstr_set(x_55, 2, x_53);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_55);
x_57 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_57);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_56);
x_60 = l_lean_parser_number_parser___at_lean_parser_command_notation__spec_precedence__lit_parser_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_60);
x_62 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_59, x_60);
x_63 = l_lean_parser_parsec__t_try__mk__res___rarg(x_62);
if (lean::is_scalar(x_15)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_15;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_13);
return x_64;
}
}
else
{
obj* x_67; uint8 x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_5);
lean::dec(x_2);
x_67 = lean::cnstr_get(x_11, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_70 = x_11;
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_67);
lean::cnstr_set_scalar(x_71, sizeof(void*)*1, x_69);
x_72 = x_71;
x_73 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_73);
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_72);
x_76 = l_lean_parser_number_parser___at_lean_parser_command_notation__spec_precedence__lit_parser_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_76);
x_78 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_75, x_76);
x_79 = l_lean_parser_parsec__t_try__mk__res___rarg(x_78);
if (lean::is_scalar(x_15)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_15;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_13);
return x_80;
}
}
}
obj* _init_l_lean_parser_command_set__option_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_0 = lean::mk_string("set_option");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
lean::inc(x_3);
lean::inc(x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_3, x_3);
lean::inc(x_3);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_3, x_6);
lean::inc(x_8);
x_10 = l_lean_parser_tokens___rarg(x_8);
lean::inc(x_3);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_10, x_3);
x_13 = l_lean_parser_tokens___rarg(x_12);
x_14 = l_lean_parser_list_cons_tokens___rarg(x_13, x_8);
x_15 = l_lean_parser_tokens___rarg(x_14);
lean::inc(x_3);
x_17 = l_lean_parser_list_cons_tokens___rarg(x_15, x_3);
x_18 = l_lean_parser_tokens___rarg(x_17);
lean::inc(x_3);
x_20 = l_lean_parser_list_cons_tokens___rarg(x_18, x_3);
x_21 = l_lean_parser_list_cons_tokens___rarg(x_3, x_20);
x_22 = l_lean_parser_list_cons_tokens___rarg(x_2, x_21);
x_23 = l_lean_parser_tokens___rarg(x_22);
return x_23;
}
}
obj* _init_l_lean_parser_command_set__option_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_49; 
x_0 = lean::mk_string("set_option");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_string("true");
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
lean::inc(x_9);
lean::inc(x_8);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_9);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_12);
lean::inc(x_4);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__2), 6, 2);
lean::closure_set(x_15, 0, x_13);
lean::closure_set(x_15, 1, x_4);
lean::inc(x_9);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_9);
x_18 = l_lean_parser_command_bool__option__value;
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_20, 0, x_18);
lean::closure_set(x_20, 1, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__3), 4, 0);
lean::inc(x_9);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_9);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__2), 4, 0);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_20);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__2), 6, 2);
lean::closure_set(x_27, 0, x_26);
lean::closure_set(x_27, 1, x_4);
lean::inc(x_9);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_9);
x_30 = l_lean_parser_command_option__value;
lean::inc(x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_9);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_lean_parser_command__parser__m_monad___closed__1;
x_38 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_39 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_40 = l_lean_parser_command__parser__m_alternative___closed__1;
x_41 = l_lean_parser_command_set__option;
x_42 = l_lean_parser_command_set__option_has__view;
lean::inc(x_42);
lean::inc(x_41);
lean::inc(x_40);
lean::inc(x_39);
lean::inc(x_38);
lean::inc(x_37);
x_49 = l_lean_parser_combinators_node_view___rarg(x_37, x_38, x_39, x_40, x_41, x_36, x_42);
return x_49;
}
}
obj* _init_l_lean_parser_command_set__option_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_0 = lean::mk_string("set_option");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_string("true");
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
lean::inc(x_9);
lean::inc(x_8);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_9);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_12);
lean::inc(x_4);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__2), 6, 2);
lean::closure_set(x_15, 0, x_13);
lean::closure_set(x_15, 1, x_4);
lean::inc(x_9);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_9);
x_18 = l_lean_parser_command_bool__option__value;
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_20, 0, x_18);
lean::closure_set(x_20, 1, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__3), 4, 0);
lean::inc(x_9);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_9);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__2), 4, 0);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_20);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__2), 6, 2);
lean::closure_set(x_27, 0, x_26);
lean::closure_set(x_27, 1, x_4);
lean::inc(x_9);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_9);
x_30 = l_lean_parser_command_option__value;
lean::inc(x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_9);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
obj* l_lean_parser_command_set__option_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_set__option;
x_5 = l_lean_parser_command_set__option_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_61; 
x_0 = l_lean_parser_command_notation_parser_lean_parser_has__tokens;
lean::inc(x_0);
x_2 = l_lean_parser_tokens___rarg(x_0);
x_3 = l_lean_parser_command_reserve__notation_parser_lean_parser_has__tokens;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = l_lean_parser_command_mixfix_parser_lean_parser_has__tokens;
lean::inc(x_6);
x_8 = l_lean_parser_tokens___rarg(x_6);
x_9 = l_lean_parser_command_reserve__mixfix_parser_lean_parser_has__tokens;
lean::inc(x_9);
x_11 = l_lean_parser_tokens___rarg(x_9);
x_12 = lean::box(0);
x_13 = l_lean_parser_command_set__option_parser_lean_parser_has__tokens;
lean::inc(x_13);
x_15 = l_lean_parser_list_cons_tokens___rarg(x_13, x_12);
x_16 = l_lean_parser_command_init__quot_parser_lean_parser_has__tokens;
lean::inc(x_16);
x_18 = l_lean_parser_list_cons_tokens___rarg(x_16, x_15);
x_19 = l_lean_parser_command_omit_parser_lean_parser_has__tokens;
lean::inc(x_19);
x_21 = l_lean_parser_list_cons_tokens___rarg(x_19, x_18);
x_22 = l_lean_parser_command_include_parser_lean_parser_has__tokens;
lean::inc(x_22);
x_24 = l_lean_parser_list_cons_tokens___rarg(x_22, x_21);
x_25 = l_lean_parser_command_export_parser_lean_parser_has__tokens;
lean::inc(x_25);
x_27 = l_lean_parser_list_cons_tokens___rarg(x_25, x_24);
x_28 = l_lean_parser_command_attribute_parser_lean_parser_has__tokens;
lean::inc(x_28);
x_30 = l_lean_parser_list_cons_tokens___rarg(x_28, x_27);
x_31 = l_lean_parser_command_check_parser_lean_parser_has__tokens;
lean::inc(x_31);
x_33 = l_lean_parser_list_cons_tokens___rarg(x_31, x_30);
x_34 = l_lean_parser_list_cons_tokens___rarg(x_11, x_33);
x_35 = l_lean_parser_list_cons_tokens___rarg(x_8, x_34);
x_36 = l_lean_parser_list_cons_tokens___rarg(x_5, x_35);
x_37 = l_lean_parser_list_cons_tokens___rarg(x_2, x_36);
x_38 = l_lean_parser_command_universe_parser_lean_parser_has__tokens;
lean::inc(x_38);
x_40 = l_lean_parser_list_cons_tokens___rarg(x_38, x_37);
x_41 = l_lean_parser_command_section_parser_lean_parser_has__tokens;
lean::inc(x_41);
x_43 = l_lean_parser_list_cons_tokens___rarg(x_41, x_40);
x_44 = l_lean_parser_command_open_parser_lean_parser_has__tokens;
lean::inc(x_44);
x_46 = l_lean_parser_list_cons_tokens___rarg(x_44, x_43);
x_47 = l_lean_parser_command_end_parser_lean_parser_has__tokens;
lean::inc(x_47);
x_49 = l_lean_parser_list_cons_tokens___rarg(x_47, x_46);
x_50 = l_lean_parser_command_namespace_parser_lean_parser_has__tokens;
lean::inc(x_50);
x_52 = l_lean_parser_list_cons_tokens___rarg(x_50, x_49);
x_53 = l_lean_parser_command_variables_parser_lean_parser_has__tokens;
lean::inc(x_53);
x_55 = l_lean_parser_list_cons_tokens___rarg(x_53, x_52);
x_56 = l_lean_parser_command_variable_parser_lean_parser_has__tokens;
lean::inc(x_56);
x_58 = l_lean_parser_list_cons_tokens___rarg(x_56, x_55);
x_59 = l_lean_parser_command_declaration_parser_lean_parser_has__tokens;
lean::inc(x_59);
x_61 = l_lean_parser_list_cons_tokens___rarg(x_59, x_58);
return x_61;
}
}
obj* _init_l_lean_parser_command_builtin__command__parsers() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_notation_parser), 5, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_reserve__notation_parser), 5, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_mixfix_parser), 5, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_reserve__mixfix_parser), 5, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_set__option_parser), 4, 0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_init__quot_parser), 4, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_omit_parser), 4, 0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_include_parser), 4, 0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_export_parser), 4, 0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attribute_parser), 4, 0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_check_parser), 4, 0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_3);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_universe_parser), 4, 0);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_section_parser), 4, 0);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_open_parser), 4, 0);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_end_parser), 4, 0);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_32);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_namespace_parser), 4, 0);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_34);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_variables_parser), 4, 0);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_36);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_variable_parser), 4, 0);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser), 4, 0);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
return x_42;
}
}
obj* l_list_map___main___at_lean_parser_command__parser_run___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = lean::apply_1(x_5, x_0);
x_12 = l_list_map___main___at_lean_parser_command__parser_run___spec__1(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_4);
x_8 = l_option_get__or__else___main___rarg(x_2, x_5);
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_1);
lean::cnstr_set(x_9, 3, x_3);
x_10 = 0;
x_11 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set_scalar(x_11, sizeof(void*)*1, x_10);
x_12 = x_11;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_6);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__3___rarg), 7, 0);
return x_2;
}
}
obj* l_reader__t_orelse___at_lean_parser_command__parser_run___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
lean::inc(x_3);
lean::inc(x_2);
x_7 = lean::apply_3(x_0, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_12 = x_7;
}
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
if (lean::is_scalar(x_12)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_12;
}
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_10);
return x_16;
}
else
{
obj* x_17; uint8 x_19; 
x_17 = lean::cnstr_get(x_8, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_19 == 0)
{
obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_28; 
lean::dec(x_8);
x_21 = lean::apply_3(x_1, x_2, x_3, x_10);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_27 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_17, x_22);
if (lean::is_scalar(x_12)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_12;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
else
{
obj* x_33; 
lean::dec(x_17);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
if (lean::is_scalar(x_12)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_12;
}
lean::cnstr_set(x_33, 0, x_8);
lean::cnstr_set(x_33, 1, x_10);
return x_33;
}
}
}
}
obj* l_reader__t_orelse___at_lean_parser_command__parser_run___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_orelse___at_lean_parser_command__parser_run___spec__4___rarg), 5, 0);
return x_2;
}
}
obj* l_list_foldl___main___at_lean_parser_command__parser_run___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_orelse___at_lean_parser_command__parser_run___spec__4___rarg), 5, 2);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_7);
x_0 = x_12;
x_1 = x_9;
goto _start;
}
}
}
obj* l_lean_parser_combinators_any__of___at_lean_parser_command__parser_run___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_11; 
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = l_lean_parser_combinators_any__of___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_7);
lean::inc(x_6);
x_11 = l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__3___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_17; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
lean::dec(x_0);
x_17 = l_list_foldl___main___at_lean_parser_command__parser_run___spec__5(x_12, x_14, x_1, x_2, x_3);
return x_17;
}
}
}
obj* _init_l_lean_parser_parser__core__t___at_lean_parser_command__parser_run___spec__7() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = l_option_get__or__else___main___rarg(x_2, x_4);
x_7 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
lean::cnstr_set(x_7, 2, x_1);
lean::cnstr_set(x_7, 3, x_3);
x_8 = 0;
x_9 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set_scalar(x_9, sizeof(void*)*1, x_8);
x_10 = x_9;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_5);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__8(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__8___rarg), 6, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_command__parser_run___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_rec_1__run__aux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_parser_rec__t_run___at_lean_parser_command__parser_run___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_command__parser_run___spec__10), 4, 3);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_3);
x_5 = lean::apply_1(x_0, x_4);
return x_5;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_10; 
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_10 = l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__8___rarg(x_5, x_6, x_4, x_4, x_1, x_2);
return x_10;
}
}
obj* _init_l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6___lambda__1), 3, 0);
return x_0;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_4 = lean::string_iterator_remaining(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_add(x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
x_9 = l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_rec__t_run___at_lean_parser_command__parser_run___spec__9(x_0, x_9, x_1, x_6);
x_12 = lean::apply_2(x_11, x_2, x_3);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_17 = x_12;
}
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_18);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_13);
if (lean::is_scalar(x_17)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_17;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_15);
return x_21;
}
}
obj* l_lean_parser_command__parser_run___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; 
lean::dec(x_2);
x_7 = l_list_map___main___at_lean_parser_command__parser_run___spec__1(x_0, x_1);
x_8 = l_lean_parser_combinators_any__of___at_lean_parser_command__parser_run___spec__2(x_7, x_3, x_4, x_5);
return x_8;
}
}
obj* l_lean_parser_command__parser_run(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_2);
x_6 = lean::apply_1(x_1, x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command__parser_run___lambda__1), 6, 2);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_0);
x_8 = l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6(x_6, x_7, x_3, x_4);
return x_8;
}
}
void initialize_init_lean_parser_declaration();
static bool _G_initialized = false;
void initialize_init_lean_parser_command() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_declaration();
 l_lean_parser_command_parser_lean_parser_has__view = _init_l_lean_parser_command_parser_lean_parser_has__view();
 l_lean_parser_command_parser_lean_parser_has__tokens = _init_l_lean_parser_command_parser_lean_parser_has__tokens();
 l_lean_parser_command_parser___rarg___closed__1 = _init_l_lean_parser_command_parser___rarg___closed__1();
 l_lean_parser_command_open__spec_as = _init_l_lean_parser_command_open__spec_as();
 l_lean_parser_command_open__spec_as_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_open__spec_as_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_open__spec_as_has__view_x_27 = _init_l_lean_parser_command_open__spec_as_has__view_x_27();
 l_lean_parser_command_open__spec_as_has__view = _init_l_lean_parser_command_open__spec_as_has__view();
 l_lean_parser_command_open__spec_only = _init_l_lean_parser_command_open__spec_only();
 l_lean_parser_command_open__spec_only_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_open__spec_only_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_open__spec_only_has__view_x_27 = _init_l_lean_parser_command_open__spec_only_has__view_x_27();
 l_lean_parser_command_open__spec_only_has__view = _init_l_lean_parser_command_open__spec_only_has__view();
 l_lean_parser_command_open__spec_renaming_item = _init_l_lean_parser_command_open__spec_renaming_item();
 l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_open__spec_renaming_item_has__view_x_27 = _init_l_lean_parser_command_open__spec_renaming_item_has__view_x_27();
 l_lean_parser_command_open__spec_renaming_item_has__view = _init_l_lean_parser_command_open__spec_renaming_item_has__view();
 l_lean_parser_command_open__spec_renaming = _init_l_lean_parser_command_open__spec_renaming();
 l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_command_open__spec_renaming_has__view_x_27 = _init_l_lean_parser_command_open__spec_renaming_has__view_x_27();
 l_lean_parser_command_open__spec_renaming_has__view = _init_l_lean_parser_command_open__spec_renaming_has__view();
 l_lean_parser_command_open__spec_hiding = _init_l_lean_parser_command_open__spec_hiding();
 l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_open__spec_hiding_has__view_x_27 = _init_l_lean_parser_command_open__spec_hiding_has__view_x_27();
 l_lean_parser_command_open__spec_hiding_has__view = _init_l_lean_parser_command_open__spec_hiding_has__view();
 l_lean_parser_command_open__spec = _init_l_lean_parser_command_open__spec();
 l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__5();
 l_lean_parser_command_open__spec_has__view_x_27 = _init_l_lean_parser_command_open__spec_has__view_x_27();
 l_lean_parser_command_open__spec_has__view = _init_l_lean_parser_command_open__spec_has__view();
 l_lean_parser_command_open__spec_parser_lean_parser_has__view = _init_l_lean_parser_command_open__spec_parser_lean_parser_has__view();
 l_lean_parser_command_open__spec_parser_lean_parser_has__tokens = _init_l_lean_parser_command_open__spec_parser_lean_parser_has__tokens();
 l_lean_parser_command_open__spec_parser___closed__1 = _init_l_lean_parser_command_open__spec_parser___closed__1();
 l_lean_parser_command_open = _init_l_lean_parser_command_open();
 l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_open_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_command_open_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_command_open_has__view_x_27 = _init_l_lean_parser_command_open_has__view_x_27();
 l_lean_parser_command_open_has__view = _init_l_lean_parser_command_open_has__view();
 l_lean_parser_command_open_parser_lean_parser_has__tokens = _init_l_lean_parser_command_open_parser_lean_parser_has__tokens();
 l_lean_parser_command_open_parser___closed__1 = _init_l_lean_parser_command_open_parser___closed__1();
 l_lean_parser_command_export = _init_l_lean_parser_command_export();
 l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_export_has__view_x_27 = _init_l_lean_parser_command_export_has__view_x_27();
 l_lean_parser_command_export_has__view = _init_l_lean_parser_command_export_has__view();
 l_lean_parser_command_export_parser_lean_parser_has__tokens = _init_l_lean_parser_command_export_parser_lean_parser_has__tokens();
 l_lean_parser_command_export_parser___closed__1 = _init_l_lean_parser_command_export_parser___closed__1();
 l_lean_parser_command_section = _init_l_lean_parser_command_section();
 l_lean_parser_command_section_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_section_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_section_has__view_x_27 = _init_l_lean_parser_command_section_has__view_x_27();
 l_lean_parser_command_section_has__view = _init_l_lean_parser_command_section_has__view();
 l_lean_parser_command_section_parser_lean_parser_has__tokens = _init_l_lean_parser_command_section_parser_lean_parser_has__tokens();
 l_lean_parser_command_section_parser___closed__1 = _init_l_lean_parser_command_section_parser___closed__1();
 l_lean_parser_command_namespace = _init_l_lean_parser_command_namespace();
 l_lean_parser_command_namespace_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_namespace_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_namespace_has__view_x_27 = _init_l_lean_parser_command_namespace_has__view_x_27();
 l_lean_parser_command_namespace_has__view = _init_l_lean_parser_command_namespace_has__view();
 l_lean_parser_command_namespace_parser_lean_parser_has__tokens = _init_l_lean_parser_command_namespace_parser_lean_parser_has__tokens();
 l_lean_parser_command_namespace_parser___closed__1 = _init_l_lean_parser_command_namespace_parser___closed__1();
 l_lean_parser_command_variable = _init_l_lean_parser_command_variable();
 l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_variable_has__view_x_27 = _init_l_lean_parser_command_variable_has__view_x_27();
 l_lean_parser_command_variable_has__view = _init_l_lean_parser_command_variable_has__view();
 l_lean_parser_command_variable_parser_lean_parser_has__tokens = _init_l_lean_parser_command_variable_parser_lean_parser_has__tokens();
 l_lean_parser_command_variable_parser___closed__1 = _init_l_lean_parser_command_variable_parser___closed__1();
 l_lean_parser_command_variables = _init_l_lean_parser_command_variables();
 l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_variables_has__view_x_27 = _init_l_lean_parser_command_variables_has__view_x_27();
 l_lean_parser_command_variables_has__view = _init_l_lean_parser_command_variables_has__view();
 l_lean_parser_command_variables_parser_lean_parser_has__tokens = _init_l_lean_parser_command_variables_parser_lean_parser_has__tokens();
 l_lean_parser_command_variables_parser___closed__1 = _init_l_lean_parser_command_variables_parser___closed__1();
 l_lean_parser_command_include = _init_l_lean_parser_command_include();
 l_lean_parser_command_include_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_include_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_include_has__view_x_27 = _init_l_lean_parser_command_include_has__view_x_27();
 l_lean_parser_command_include_has__view = _init_l_lean_parser_command_include_has__view();
 l_lean_parser_command_include_parser_lean_parser_has__tokens = _init_l_lean_parser_command_include_parser_lean_parser_has__tokens();
 l_lean_parser_command_include_parser___closed__1 = _init_l_lean_parser_command_include_parser___closed__1();
 l_lean_parser_command_omit = _init_l_lean_parser_command_omit();
 l_lean_parser_command_omit_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_omit_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_omit_has__view_x_27 = _init_l_lean_parser_command_omit_has__view_x_27();
 l_lean_parser_command_omit_has__view = _init_l_lean_parser_command_omit_has__view();
 l_lean_parser_command_omit_parser_lean_parser_has__tokens = _init_l_lean_parser_command_omit_parser_lean_parser_has__tokens();
 l_lean_parser_command_omit_parser___closed__1 = _init_l_lean_parser_command_omit_parser___closed__1();
 l_lean_parser_command_end = _init_l_lean_parser_command_end();
 l_lean_parser_command_end_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_end_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_end_has__view_x_27 = _init_l_lean_parser_command_end_has__view_x_27();
 l_lean_parser_command_end_has__view = _init_l_lean_parser_command_end_has__view();
 l_lean_parser_command_end_parser_lean_parser_has__tokens = _init_l_lean_parser_command_end_parser_lean_parser_has__tokens();
 l_lean_parser_command_end_parser___closed__1 = _init_l_lean_parser_command_end_parser___closed__1();
 l_lean_parser_command_universes = _init_l_lean_parser_command_universes();
 l_lean_parser_command_universes_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_universes_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_universes_has__view_x_27 = _init_l_lean_parser_command_universes_has__view_x_27();
 l_lean_parser_command_universes_has__view = _init_l_lean_parser_command_universes_has__view();
 l_lean_parser_command_universe = _init_l_lean_parser_command_universe();
 l_lean_parser_command_universe_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_universe_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_universe_has__view_x_27 = _init_l_lean_parser_command_universe_has__view_x_27();
 l_lean_parser_command_universe_has__view = _init_l_lean_parser_command_universe_has__view();
 l_lean_parser_command_universe_parser_lean_parser_has__tokens = _init_l_lean_parser_command_universe_parser_lean_parser_has__tokens();
 l_lean_parser_command_universe_parser___closed__1 = _init_l_lean_parser_command_universe_parser___closed__1();
 l_lean_parser_command_check = _init_l_lean_parser_command_check();
 l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_check_has__view_x_27 = _init_l_lean_parser_command_check_has__view_x_27();
 l_lean_parser_command_check_has__view = _init_l_lean_parser_command_check_has__view();
 l_lean_parser_command_check_parser_lean_parser_has__tokens = _init_l_lean_parser_command_check_parser_lean_parser_has__tokens();
 l_lean_parser_command_check_parser_lean_parser_has__view = _init_l_lean_parser_command_check_parser_lean_parser_has__view();
 l_lean_parser_command_check_parser___closed__1 = _init_l_lean_parser_command_check_parser___closed__1();
 l_lean_parser_command_attribute = _init_l_lean_parser_command_attribute();
 l_lean_parser_command_attribute_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_attribute_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_attribute_has__view_x_27 = _init_l_lean_parser_command_attribute_has__view_x_27();
 l_lean_parser_command_attribute_has__view = _init_l_lean_parser_command_attribute_has__view();
 l_lean_parser_command_attribute_parser_lean_parser_has__tokens = _init_l_lean_parser_command_attribute_parser_lean_parser_has__tokens();
 l_lean_parser_command_attribute_parser_lean_parser_has__view = _init_l_lean_parser_command_attribute_parser_lean_parser_has__view();
 l_lean_parser_command_attribute_parser___closed__1 = _init_l_lean_parser_command_attribute_parser___closed__1();
 l_lean_parser_command_init__quot = _init_l_lean_parser_command_init__quot();
 l_lean_parser_command_init__quot_has__view_x_27 = _init_l_lean_parser_command_init__quot_has__view_x_27();
 l_lean_parser_command_init__quot_has__view = _init_l_lean_parser_command_init__quot_has__view();
 l_lean_parser_command_init__quot_parser_lean_parser_has__tokens = _init_l_lean_parser_command_init__quot_parser_lean_parser_has__tokens();
 l_lean_parser_command_init__quot_parser_lean_parser_has__view = _init_l_lean_parser_command_init__quot_parser_lean_parser_has__view();
 l_lean_parser_command_init__quot_parser___closed__1 = _init_l_lean_parser_command_init__quot_parser___closed__1();
 l_lean_parser_command_bool__option__value = _init_l_lean_parser_command_bool__option__value();
 l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_bool__option__value_has__view_x_27 = _init_l_lean_parser_command_bool__option__value_has__view_x_27();
 l_lean_parser_command_bool__option__value_has__view = _init_l_lean_parser_command_bool__option__value_has__view();
 l_lean_parser_command_option__value = _init_l_lean_parser_command_option__value();
 l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_option__value_has__view_x_27 = _init_l_lean_parser_command_option__value_has__view_x_27();
 l_lean_parser_command_option__value_has__view = _init_l_lean_parser_command_option__value_has__view();
 l_lean_parser_command_set__option = _init_l_lean_parser_command_set__option();
 l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_set__option_has__view_x_27 = _init_l_lean_parser_command_set__option_has__view_x_27();
 l_lean_parser_command_set__option_has__view = _init_l_lean_parser_command_set__option_has__view();
 l_lean_parser_command_set__option_parser_lean_parser_has__tokens = _init_l_lean_parser_command_set__option_parser_lean_parser_has__tokens();
 l_lean_parser_command_set__option_parser_lean_parser_has__view = _init_l_lean_parser_command_set__option_parser_lean_parser_has__view();
 l_lean_parser_command_set__option_parser___closed__1 = _init_l_lean_parser_command_set__option_parser___closed__1();
 l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens = _init_l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens();
 l_lean_parser_command_builtin__command__parsers = _init_l_lean_parser_command_builtin__command__parsers();
 l_lean_parser_parser__core__t___at_lean_parser_command__parser_run___spec__7 = _init_l_lean_parser_parser__core__t___at_lean_parser_command__parser_run___spec__7();
 l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6___closed__1 = _init_l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6___closed__1();
}
