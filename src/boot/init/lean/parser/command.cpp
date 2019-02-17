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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
} else {
 lean::dec(x_4);
 x_9 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_command_parser_lean_parser_has__view___spec__1), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__8___rarg), 5, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_lean_parser_command__parser__m_lean_parser_monad__rec___closed__1;
lean::inc(x_3);
x_5 = l_lean_parser_combinators_recurse_view___rarg(x_0, x_3);
x_6 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_7 = l_lean_parser_command__parser__m_alternative___closed__1;
x_8 = lean::mk_string("command");
lean::inc(x_7);
lean::inc(x_6);
x_11 = l_lean_parser_combinators_label_view___rarg(x_6, x_7, x_2, x_8, x_5);
return x_11;
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
} else {
 lean::dec(x_4);
 x_9 = lean::box(0);
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_14; obj* x_16; 
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
case 3:
{
obj* x_24; obj* x_26; 
x_24 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_24);
return x_26;
}
default:
{
obj* x_28; obj* x_30; 
lean::dec(x_17);
x_28 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
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
obj* x_5; 
x_5 = l_lean_parser_command_open__spec_as_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_19 = x_24;
goto lbl_20;
}
case 3:
{
obj* x_25; 
x_25 = lean::box(0);
x_19 = x_25;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_28; obj* x_30; 
x_28 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_19);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
lean::dec(x_1);
switch (lean::obj_tag(x_31)) {
case 1:
{
obj* x_34; obj* x_37; 
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_19);
lean::cnstr_set(x_37, 1, x_34);
return x_37;
}
case 3:
{
obj* x_38; obj* x_40; 
x_38 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_19);
lean::cnstr_set(x_40, 1, x_38);
return x_40;
}
default:
{
obj* x_42; obj* x_44; 
lean::dec(x_31);
x_42 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_19);
lean::cnstr_set(x_44, 1, x_42);
return x_44;
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
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__1(x_4);
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
obj* x_12; obj* x_14; 
x_12 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_12);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
default:
{
obj* x_16; obj* x_18; 
lean::dec(x_2);
x_16 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_16);
if (lean::is_scalar(x_6)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_6;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
x_8 = l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__2(x_4);
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_14; obj* x_15; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_17; 
x_17 = lean::box(3);
x_14 = x_0;
x_15 = x_17;
goto lbl_16;
}
else
{
obj* x_18; obj* x_20; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
lean::dec(x_0);
x_14 = x_20;
x_15 = x_18;
goto lbl_16;
}
lbl_16:
{
obj* x_23; 
switch (lean::obj_tag(x_15)) {
case 1:
{
obj* x_25; 
x_25 = lean::cnstr_get(x_15, 0);
lean::inc(x_25);
lean::dec(x_15);
x_23 = x_25;
goto lbl_24;
}
case 3:
{
obj* x_28; 
x_28 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_28);
x_23 = x_28;
goto lbl_24;
}
default:
{
obj* x_31; 
lean::dec(x_15);
x_31 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_31);
x_23 = x_31;
goto lbl_24;
}
}
lbl_24:
{
obj* x_33; obj* x_34; 
if (lean::obj_tag(x_14) == 0)
{
obj* x_36; 
x_36 = lean::box(3);
x_33 = x_14;
x_34 = x_36;
goto lbl_35;
}
else
{
obj* x_37; obj* x_39; 
x_37 = lean::cnstr_get(x_14, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_14, 1);
lean::inc(x_39);
lean::dec(x_14);
x_33 = x_39;
x_34 = x_37;
goto lbl_35;
}
lbl_35:
{
obj* x_42; 
x_42 = l_lean_parser_syntax_as__node___main(x_34);
if (lean::obj_tag(x_42) == 0)
{
if (lean::obj_tag(x_33) == 0)
{
obj* x_43; obj* x_44; obj* x_46; 
x_43 = lean::box(0);
x_44 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_44);
x_46 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_46, 0, x_5);
lean::cnstr_set(x_46, 1, x_23);
lean::cnstr_set(x_46, 2, x_44);
lean::cnstr_set(x_46, 3, x_43);
return x_46;
}
else
{
obj* x_47; 
x_47 = lean::cnstr_get(x_33, 0);
lean::inc(x_47);
lean::dec(x_33);
switch (lean::obj_tag(x_47)) {
case 0:
{
obj* x_50; obj* x_53; obj* x_54; obj* x_56; 
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
lean::dec(x_47);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_50);
x_54 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_54);
x_56 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_56, 0, x_5);
lean::cnstr_set(x_56, 1, x_23);
lean::cnstr_set(x_56, 2, x_54);
lean::cnstr_set(x_56, 3, x_53);
return x_56;
}
case 3:
{
obj* x_57; obj* x_58; obj* x_60; 
x_57 = lean::box(0);
x_58 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_60, 0, x_5);
lean::cnstr_set(x_60, 1, x_23);
lean::cnstr_set(x_60, 2, x_58);
lean::cnstr_set(x_60, 3, x_57);
return x_60;
}
default:
{
obj* x_62; obj* x_63; obj* x_65; 
lean::dec(x_47);
x_62 = lean::box(0);
x_63 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_63);
x_65 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_65, 0, x_5);
lean::cnstr_set(x_65, 1, x_23);
lean::cnstr_set(x_65, 2, x_63);
lean::cnstr_set(x_65, 3, x_62);
return x_65;
}
}
}
}
else
{
obj* x_66; obj* x_68; obj* x_69; obj* x_72; 
x_66 = lean::cnstr_get(x_42, 0);
lean::inc(x_66);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_68 = x_42;
} else {
 lean::dec(x_42);
 x_68 = lean::box(0);
}
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
lean::dec(x_66);
x_72 = l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__1(x_69);
if (lean::obj_tag(x_33) == 0)
{
obj* x_74; obj* x_75; 
lean::dec(x_68);
x_74 = lean::box(0);
x_75 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_75, 0, x_5);
lean::cnstr_set(x_75, 1, x_23);
lean::cnstr_set(x_75, 2, x_72);
lean::cnstr_set(x_75, 3, x_74);
return x_75;
}
else
{
obj* x_76; 
x_76 = lean::cnstr_get(x_33, 0);
lean::inc(x_76);
lean::dec(x_33);
switch (lean::obj_tag(x_76)) {
case 0:
{
obj* x_79; obj* x_82; obj* x_83; 
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
lean::dec(x_76);
if (lean::is_scalar(x_68)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_68;
}
lean::cnstr_set(x_82, 0, x_79);
x_83 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_83, 0, x_5);
lean::cnstr_set(x_83, 1, x_23);
lean::cnstr_set(x_83, 2, x_72);
lean::cnstr_set(x_83, 3, x_82);
return x_83;
}
case 3:
{
obj* x_85; obj* x_86; 
lean::dec(x_68);
x_85 = lean::box(0);
x_86 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_86, 0, x_5);
lean::cnstr_set(x_86, 1, x_23);
lean::cnstr_set(x_86, 2, x_72);
lean::cnstr_set(x_86, 3, x_85);
return x_86;
}
default:
{
obj* x_89; obj* x_90; 
lean::dec(x_68);
lean::dec(x_76);
x_89 = lean::box(0);
x_90 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_90, 0, x_5);
lean::cnstr_set(x_90, 1, x_23);
lean::cnstr_set(x_90, 2, x_72);
lean::cnstr_set(x_90, 3, x_89);
return x_90;
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
obj* x_5; 
x_5 = l_lean_parser_command_open__spec_only_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
else
{
obj* x_19; obj* x_21; obj* x_24; 
x_19 = lean::cnstr_get(x_10, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_10, 1);
lean::inc(x_21);
lean::dec(x_10);
x_24 = l_lean_parser_syntax_as__node___main(x_19);
if (lean::obj_tag(x_24) == 0)
{
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; 
x_25 = lean::box(3);
x_1 = x_21;
x_2 = x_25;
goto lbl_3;
}
else
{
obj* x_26; obj* x_28; 
x_26 = lean::cnstr_get(x_21, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_21, 1);
lean::inc(x_28);
lean::dec(x_21);
x_1 = x_28;
x_2 = x_26;
goto lbl_3;
}
}
else
{
obj* x_31; obj* x_34; obj* x_37; 
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = l_list_append___rarg(x_34, x_21);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::box(3);
x_1 = x_37;
x_2 = x_38;
goto lbl_3;
}
else
{
obj* x_39; obj* x_41; 
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_37, 1);
lean::inc(x_41);
lean::dec(x_37);
x_1 = x_41;
x_2 = x_39;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_44; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_46; obj* x_49; 
x_46 = lean::cnstr_get(x_2, 0);
lean::inc(x_46);
lean::dec(x_2);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_46);
x_44 = x_49;
goto lbl_45;
}
case 3:
{
obj* x_50; 
x_50 = lean::box(0);
x_44 = x_50;
goto lbl_45;
}
default:
{
obj* x_52; 
lean::dec(x_2);
x_52 = lean::box(0);
x_44 = x_52;
goto lbl_45;
}
}
lbl_45:
{
obj* x_53; obj* x_54; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_56; 
x_56 = lean::box(3);
x_53 = x_1;
x_54 = x_56;
goto lbl_55;
}
else
{
obj* x_57; obj* x_59; 
x_57 = lean::cnstr_get(x_1, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_1, 1);
lean::inc(x_59);
lean::dec(x_1);
x_53 = x_59;
x_54 = x_57;
goto lbl_55;
}
lbl_55:
{
obj* x_62; 
switch (lean::obj_tag(x_54)) {
case 1:
{
obj* x_64; 
x_64 = lean::cnstr_get(x_54, 0);
lean::inc(x_64);
lean::dec(x_54);
x_62 = x_64;
goto lbl_63;
}
case 3:
{
obj* x_67; 
x_67 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_67);
x_62 = x_67;
goto lbl_63;
}
default:
{
obj* x_70; 
lean::dec(x_54);
x_70 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_70);
x_62 = x_70;
goto lbl_63;
}
}
lbl_63:
{
obj* x_72; obj* x_73; 
if (lean::obj_tag(x_53) == 0)
{
obj* x_75; 
x_75 = lean::box(3);
x_72 = x_53;
x_73 = x_75;
goto lbl_74;
}
else
{
obj* x_76; obj* x_78; 
x_76 = lean::cnstr_get(x_53, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_53, 1);
lean::inc(x_78);
lean::dec(x_53);
x_72 = x_78;
x_73 = x_76;
goto lbl_74;
}
lbl_74:
{
obj* x_81; 
x_81 = l_lean_parser_syntax_as__node___main(x_73);
if (lean::obj_tag(x_81) == 0)
{
if (lean::obj_tag(x_72) == 0)
{
obj* x_82; obj* x_83; obj* x_85; 
x_82 = lean::box(0);
x_83 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_83);
x_85 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_85, 0, x_44);
lean::cnstr_set(x_85, 1, x_62);
lean::cnstr_set(x_85, 2, x_83);
lean::cnstr_set(x_85, 3, x_82);
return x_85;
}
else
{
obj* x_86; 
x_86 = lean::cnstr_get(x_72, 0);
lean::inc(x_86);
lean::dec(x_72);
switch (lean::obj_tag(x_86)) {
case 0:
{
obj* x_89; obj* x_92; obj* x_93; obj* x_95; 
x_89 = lean::cnstr_get(x_86, 0);
lean::inc(x_89);
lean::dec(x_86);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_89);
x_93 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_93);
x_95 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_95, 0, x_44);
lean::cnstr_set(x_95, 1, x_62);
lean::cnstr_set(x_95, 2, x_93);
lean::cnstr_set(x_95, 3, x_92);
return x_95;
}
case 3:
{
obj* x_96; obj* x_97; obj* x_99; 
x_96 = lean::box(0);
x_97 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_97);
x_99 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_99, 0, x_44);
lean::cnstr_set(x_99, 1, x_62);
lean::cnstr_set(x_99, 2, x_97);
lean::cnstr_set(x_99, 3, x_96);
return x_99;
}
default:
{
obj* x_101; obj* x_102; obj* x_104; 
lean::dec(x_86);
x_101 = lean::box(0);
x_102 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_102);
x_104 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_104, 0, x_44);
lean::cnstr_set(x_104, 1, x_62);
lean::cnstr_set(x_104, 2, x_102);
lean::cnstr_set(x_104, 3, x_101);
return x_104;
}
}
}
}
else
{
obj* x_105; obj* x_107; obj* x_108; obj* x_111; 
x_105 = lean::cnstr_get(x_81, 0);
lean::inc(x_105);
if (lean::is_exclusive(x_81)) {
 lean::cnstr_release(x_81, 0);
 x_107 = x_81;
} else {
 lean::dec(x_81);
 x_107 = lean::box(0);
}
x_108 = lean::cnstr_get(x_105, 1);
lean::inc(x_108);
lean::dec(x_105);
x_111 = l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__1(x_108);
if (lean::obj_tag(x_72) == 0)
{
obj* x_113; obj* x_114; 
lean::dec(x_107);
x_113 = lean::box(0);
x_114 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_114, 0, x_44);
lean::cnstr_set(x_114, 1, x_62);
lean::cnstr_set(x_114, 2, x_111);
lean::cnstr_set(x_114, 3, x_113);
return x_114;
}
else
{
obj* x_115; 
x_115 = lean::cnstr_get(x_72, 0);
lean::inc(x_115);
lean::dec(x_72);
switch (lean::obj_tag(x_115)) {
case 0:
{
obj* x_118; obj* x_121; obj* x_122; 
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
lean::dec(x_115);
if (lean::is_scalar(x_107)) {
 x_121 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_121 = x_107;
}
lean::cnstr_set(x_121, 0, x_118);
x_122 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_122, 0, x_44);
lean::cnstr_set(x_122, 1, x_62);
lean::cnstr_set(x_122, 2, x_111);
lean::cnstr_set(x_122, 3, x_121);
return x_122;
}
case 3:
{
obj* x_124; obj* x_125; 
lean::dec(x_107);
x_124 = lean::box(0);
x_125 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_125, 0, x_44);
lean::cnstr_set(x_125, 1, x_62);
lean::cnstr_set(x_125, 2, x_111);
lean::cnstr_set(x_125, 3, x_124);
return x_125;
}
default:
{
obj* x_128; obj* x_129; 
lean::dec(x_107);
lean::dec(x_115);
x_128 = lean::box(0);
x_129 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_129, 0, x_44);
lean::cnstr_set(x_129, 1, x_62);
lean::cnstr_set(x_129, 2, x_111);
lean::cnstr_set(x_129, 3, x_128);
return x_129;
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
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
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
x_14 = l_option_get__or__else___main___rarg(x_12, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_3);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_lean_parser_no__kind;
lean::inc(x_19);
x_21 = l_lean_parser_syntax_mk__node(x_19, x_18);
x_22 = l_list_map___main___at_lean_parser_command_open__spec_only_has__view_x_27___spec__2(x_5);
lean::inc(x_19);
x_24 = l_lean_parser_syntax_mk__node(x_19, x_22);
lean::inc(x_10);
x_26 = l_option_map___rarg(x_10, x_7);
x_27 = l_option_get__or__else___main___rarg(x_26, x_13);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_16);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_21);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_lean_parser_command_open__spec_only;
lean::inc(x_31);
x_33 = l_lean_parser_syntax_mk__node(x_31, x_30);
return x_33;
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
case 3:
{
obj* x_10; 
x_10 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_10);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_13);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_15; obj* x_16; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_18; 
x_18 = lean::box(3);
x_15 = x_0;
x_16 = x_18;
goto lbl_17;
}
else
{
obj* x_19; obj* x_21; 
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::dec(x_0);
x_15 = x_21;
x_16 = x_19;
goto lbl_17;
}
lbl_17:
{
obj* x_24; 
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_26; obj* x_29; 
x_26 = lean::cnstr_get(x_16, 0);
lean::inc(x_26);
lean::dec(x_16);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_26);
x_24 = x_29;
goto lbl_25;
}
case 3:
{
obj* x_30; 
x_30 = lean::box(0);
x_24 = x_30;
goto lbl_25;
}
default:
{
obj* x_32; 
lean::dec(x_16);
x_32 = lean::box(0);
x_24 = x_32;
goto lbl_25;
}
}
lbl_25:
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_33; obj* x_35; 
x_33 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_5);
lean::cnstr_set(x_35, 1, x_24);
lean::cnstr_set(x_35, 2, x_33);
return x_35;
}
else
{
obj* x_36; 
x_36 = lean::cnstr_get(x_15, 0);
lean::inc(x_36);
lean::dec(x_15);
switch (lean::obj_tag(x_36)) {
case 1:
{
obj* x_39; obj* x_42; 
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
lean::dec(x_36);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_5);
lean::cnstr_set(x_42, 1, x_24);
lean::cnstr_set(x_42, 2, x_39);
return x_42;
}
case 3:
{
obj* x_43; obj* x_45; 
x_43 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_5);
lean::cnstr_set(x_45, 1, x_24);
lean::cnstr_set(x_45, 2, x_43);
return x_45;
}
default:
{
obj* x_47; obj* x_49; 
lean::dec(x_36);
x_47 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_47);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_5);
lean::cnstr_set(x_49, 1, x_24);
lean::cnstr_set(x_49, 2, x_47);
return x_49;
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
obj* x_5; 
x_5 = l_lean_parser_command_open__spec_renaming_item_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_21; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_19 = x_21;
goto lbl_20;
}
case 3:
{
obj* x_24; 
x_24 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_24);
x_19 = x_24;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_27);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
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
obj* x_38; 
switch (lean::obj_tag(x_30)) {
case 0:
{
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_30, 0);
lean::inc(x_40);
lean::dec(x_30);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_40);
x_38 = x_43;
goto lbl_39;
}
case 3:
{
obj* x_44; 
x_44 = lean::box(0);
x_38 = x_44;
goto lbl_39;
}
default:
{
obj* x_46; 
lean::dec(x_30);
x_46 = lean::box(0);
x_38 = x_46;
goto lbl_39;
}
}
lbl_39:
{
if (lean::obj_tag(x_29) == 0)
{
obj* x_47; obj* x_49; 
x_47 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_47);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_19);
lean::cnstr_set(x_49, 1, x_38);
lean::cnstr_set(x_49, 2, x_47);
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_29, 0);
lean::inc(x_50);
lean::dec(x_29);
switch (lean::obj_tag(x_50)) {
case 1:
{
obj* x_53; obj* x_56; 
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
lean::dec(x_50);
x_56 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_56, 0, x_19);
lean::cnstr_set(x_56, 1, x_38);
lean::cnstr_set(x_56, 2, x_53);
return x_56;
}
case 3:
{
obj* x_57; obj* x_59; 
x_57 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_19);
lean::cnstr_set(x_59, 1, x_38);
lean::cnstr_set(x_59, 2, x_57);
return x_59;
}
default:
{
obj* x_61; obj* x_63; 
lean::dec(x_50);
x_61 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_61);
x_63 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_63, 0, x_19);
lean::cnstr_set(x_63, 1, x_38);
lean::cnstr_set(x_63, 2, x_61);
return x_63;
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_14; obj* x_15; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_17; 
x_17 = lean::box(3);
x_14 = x_0;
x_15 = x_17;
goto lbl_16;
}
else
{
obj* x_18; obj* x_20; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
lean::dec(x_0);
x_14 = x_20;
x_15 = x_18;
goto lbl_16;
}
lbl_16:
{
obj* x_23; 
switch (lean::obj_tag(x_15)) {
case 0:
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_15, 0);
lean::inc(x_25);
lean::dec(x_15);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
x_23 = x_28;
goto lbl_24;
}
case 3:
{
obj* x_29; 
x_29 = lean::box(0);
x_23 = x_29;
goto lbl_24;
}
default:
{
obj* x_31; 
lean::dec(x_15);
x_31 = lean::box(0);
x_23 = x_31;
goto lbl_24;
}
}
lbl_24:
{
obj* x_32; obj* x_33; 
if (lean::obj_tag(x_14) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_32 = x_14;
x_33 = x_35;
goto lbl_34;
}
else
{
obj* x_36; obj* x_38; 
x_36 = lean::cnstr_get(x_14, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_14, 1);
lean::inc(x_38);
lean::dec(x_14);
x_32 = x_38;
x_33 = x_36;
goto lbl_34;
}
lbl_34:
{
obj* x_41; 
x_41 = l_lean_parser_syntax_as__node___main(x_33);
if (lean::obj_tag(x_41) == 0)
{
if (lean::obj_tag(x_32) == 0)
{
obj* x_42; obj* x_43; obj* x_45; 
x_42 = lean::box(0);
x_43 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_45, 0, x_5);
lean::cnstr_set(x_45, 1, x_23);
lean::cnstr_set(x_45, 2, x_43);
lean::cnstr_set(x_45, 3, x_42);
return x_45;
}
else
{
obj* x_46; 
x_46 = lean::cnstr_get(x_32, 0);
lean::inc(x_46);
lean::dec(x_32);
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
lean::cnstr_set(x_55, 1, x_23);
lean::cnstr_set(x_55, 2, x_53);
lean::cnstr_set(x_55, 3, x_52);
return x_55;
}
case 3:
{
obj* x_56; obj* x_57; obj* x_59; 
x_56 = lean::box(0);
x_57 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_59, 0, x_5);
lean::cnstr_set(x_59, 1, x_23);
lean::cnstr_set(x_59, 2, x_57);
lean::cnstr_set(x_59, 3, x_56);
return x_59;
}
default:
{
obj* x_61; obj* x_62; obj* x_64; 
lean::dec(x_46);
x_61 = lean::box(0);
x_62 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_62);
x_64 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_64, 0, x_5);
lean::cnstr_set(x_64, 1, x_23);
lean::cnstr_set(x_64, 2, x_62);
lean::cnstr_set(x_64, 3, x_61);
return x_64;
}
}
}
}
else
{
obj* x_65; obj* x_67; obj* x_68; obj* x_71; obj* x_73; 
x_65 = lean::cnstr_get(x_41, 0);
lean::inc(x_65);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_67 = x_41;
} else {
 lean::dec(x_41);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
lean::dec(x_65);
x_71 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__2;
lean::inc(x_71);
x_73 = l_list_map___main___rarg(x_71, x_68);
if (lean::obj_tag(x_32) == 0)
{
obj* x_75; obj* x_76; 
lean::dec(x_67);
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_76, 0, x_5);
lean::cnstr_set(x_76, 1, x_23);
lean::cnstr_set(x_76, 2, x_73);
lean::cnstr_set(x_76, 3, x_75);
return x_76;
}
else
{
obj* x_77; 
x_77 = lean::cnstr_get(x_32, 0);
lean::inc(x_77);
lean::dec(x_32);
switch (lean::obj_tag(x_77)) {
case 0:
{
obj* x_80; obj* x_83; obj* x_84; 
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
lean::dec(x_77);
if (lean::is_scalar(x_67)) {
 x_83 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_83 = x_67;
}
lean::cnstr_set(x_83, 0, x_80);
x_84 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_84, 0, x_5);
lean::cnstr_set(x_84, 1, x_23);
lean::cnstr_set(x_84, 2, x_73);
lean::cnstr_set(x_84, 3, x_83);
return x_84;
}
case 3:
{
obj* x_86; obj* x_87; 
lean::dec(x_67);
x_86 = lean::box(0);
x_87 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_87, 0, x_5);
lean::cnstr_set(x_87, 1, x_23);
lean::cnstr_set(x_87, 2, x_73);
lean::cnstr_set(x_87, 3, x_86);
return x_87;
}
default:
{
obj* x_90; obj* x_91; 
lean::dec(x_67);
lean::dec(x_77);
x_90 = lean::box(0);
x_91 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_91, 0, x_5);
lean::cnstr_set(x_91, 1, x_23);
lean::cnstr_set(x_91, 2, x_73);
lean::cnstr_set(x_91, 3, x_90);
return x_91;
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
obj* x_5; 
x_5 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__3;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
else
{
obj* x_19; obj* x_21; obj* x_24; 
x_19 = lean::cnstr_get(x_10, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_10, 1);
lean::inc(x_21);
lean::dec(x_10);
x_24 = l_lean_parser_syntax_as__node___main(x_19);
if (lean::obj_tag(x_24) == 0)
{
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; 
x_25 = lean::box(3);
x_1 = x_21;
x_2 = x_25;
goto lbl_3;
}
else
{
obj* x_26; obj* x_28; 
x_26 = lean::cnstr_get(x_21, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_21, 1);
lean::inc(x_28);
lean::dec(x_21);
x_1 = x_28;
x_2 = x_26;
goto lbl_3;
}
}
else
{
obj* x_31; obj* x_34; obj* x_37; 
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = l_list_append___rarg(x_34, x_21);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::box(3);
x_1 = x_37;
x_2 = x_38;
goto lbl_3;
}
else
{
obj* x_39; obj* x_41; 
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_37, 1);
lean::inc(x_41);
lean::dec(x_37);
x_1 = x_41;
x_2 = x_39;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_44; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_46; obj* x_49; 
x_46 = lean::cnstr_get(x_2, 0);
lean::inc(x_46);
lean::dec(x_2);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_46);
x_44 = x_49;
goto lbl_45;
}
case 3:
{
obj* x_50; 
x_50 = lean::box(0);
x_44 = x_50;
goto lbl_45;
}
default:
{
obj* x_52; 
lean::dec(x_2);
x_52 = lean::box(0);
x_44 = x_52;
goto lbl_45;
}
}
lbl_45:
{
obj* x_53; obj* x_54; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_56; 
x_56 = lean::box(3);
x_53 = x_1;
x_54 = x_56;
goto lbl_55;
}
else
{
obj* x_57; obj* x_59; 
x_57 = lean::cnstr_get(x_1, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_1, 1);
lean::inc(x_59);
lean::dec(x_1);
x_53 = x_59;
x_54 = x_57;
goto lbl_55;
}
lbl_55:
{
obj* x_62; 
switch (lean::obj_tag(x_54)) {
case 0:
{
obj* x_64; obj* x_67; 
x_64 = lean::cnstr_get(x_54, 0);
lean::inc(x_64);
lean::dec(x_54);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_64);
x_62 = x_67;
goto lbl_63;
}
case 3:
{
obj* x_68; 
x_68 = lean::box(0);
x_62 = x_68;
goto lbl_63;
}
default:
{
obj* x_70; 
lean::dec(x_54);
x_70 = lean::box(0);
x_62 = x_70;
goto lbl_63;
}
}
lbl_63:
{
obj* x_71; obj* x_72; 
if (lean::obj_tag(x_53) == 0)
{
obj* x_74; 
x_74 = lean::box(3);
x_71 = x_53;
x_72 = x_74;
goto lbl_73;
}
else
{
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_53, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_53, 1);
lean::inc(x_77);
lean::dec(x_53);
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
if (lean::obj_tag(x_71) == 0)
{
obj* x_81; obj* x_82; obj* x_84; 
x_81 = lean::box(0);
x_82 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_84, 0, x_44);
lean::cnstr_set(x_84, 1, x_62);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_81);
return x_84;
}
else
{
obj* x_85; 
x_85 = lean::cnstr_get(x_71, 0);
lean::inc(x_85);
lean::dec(x_71);
switch (lean::obj_tag(x_85)) {
case 0:
{
obj* x_88; obj* x_91; obj* x_92; obj* x_94; 
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
lean::dec(x_85);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_88);
x_92 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_94, 0, x_44);
lean::cnstr_set(x_94, 1, x_62);
lean::cnstr_set(x_94, 2, x_92);
lean::cnstr_set(x_94, 3, x_91);
return x_94;
}
case 3:
{
obj* x_95; obj* x_96; obj* x_98; 
x_95 = lean::box(0);
x_96 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_96);
x_98 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_98, 0, x_44);
lean::cnstr_set(x_98, 1, x_62);
lean::cnstr_set(x_98, 2, x_96);
lean::cnstr_set(x_98, 3, x_95);
return x_98;
}
default:
{
obj* x_100; obj* x_101; obj* x_103; 
lean::dec(x_85);
x_100 = lean::box(0);
x_101 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__1;
lean::inc(x_101);
x_103 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_103, 0, x_44);
lean::cnstr_set(x_103, 1, x_62);
lean::cnstr_set(x_103, 2, x_101);
lean::cnstr_set(x_103, 3, x_100);
return x_103;
}
}
}
}
else
{
obj* x_104; obj* x_106; obj* x_107; obj* x_110; obj* x_112; 
x_104 = lean::cnstr_get(x_80, 0);
lean::inc(x_104);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 x_106 = x_80;
} else {
 lean::dec(x_80);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_104, 1);
lean::inc(x_107);
lean::dec(x_104);
x_110 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__1___closed__2;
lean::inc(x_110);
x_112 = l_list_map___main___rarg(x_110, x_107);
if (lean::obj_tag(x_71) == 0)
{
obj* x_114; obj* x_115; 
lean::dec(x_106);
x_114 = lean::box(0);
x_115 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_115, 0, x_44);
lean::cnstr_set(x_115, 1, x_62);
lean::cnstr_set(x_115, 2, x_112);
lean::cnstr_set(x_115, 3, x_114);
return x_115;
}
else
{
obj* x_116; 
x_116 = lean::cnstr_get(x_71, 0);
lean::inc(x_116);
lean::dec(x_71);
switch (lean::obj_tag(x_116)) {
case 0:
{
obj* x_119; obj* x_122; obj* x_123; 
x_119 = lean::cnstr_get(x_116, 0);
lean::inc(x_119);
lean::dec(x_116);
if (lean::is_scalar(x_106)) {
 x_122 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_122 = x_106;
}
lean::cnstr_set(x_122, 0, x_119);
x_123 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_123, 0, x_44);
lean::cnstr_set(x_123, 1, x_62);
lean::cnstr_set(x_123, 2, x_112);
lean::cnstr_set(x_123, 3, x_122);
return x_123;
}
case 3:
{
obj* x_125; obj* x_126; 
lean::dec(x_106);
x_125 = lean::box(0);
x_126 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_126, 0, x_44);
lean::cnstr_set(x_126, 1, x_62);
lean::cnstr_set(x_126, 2, x_112);
lean::cnstr_set(x_126, 3, x_125);
return x_126;
}
default:
{
obj* x_129; obj* x_130; 
lean::dec(x_106);
lean::dec(x_116);
x_129 = lean::box(0);
x_130 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_130, 0, x_44);
lean::cnstr_set(x_130, 1, x_62);
lean::cnstr_set(x_130, 2, x_112);
lean::cnstr_set(x_130, 3, x_129);
return x_130;
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
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_37; 
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
x_14 = l_option_get__or__else___main___rarg(x_12, x_13);
lean::inc(x_10);
x_16 = l_option_map___rarg(x_10, x_3);
x_17 = l_option_get__or__else___main___rarg(x_16, x_13);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_14);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_parser_no__kind;
lean::inc(x_21);
x_23 = l_lean_parser_syntax_mk__node(x_21, x_20);
x_24 = l_lean_parser_command_open__spec_renaming_has__view_x_27___lambda__2___closed__1;
lean::inc(x_24);
x_26 = l_list_map___main___rarg(x_24, x_5);
lean::inc(x_21);
x_28 = l_lean_parser_syntax_mk__node(x_21, x_26);
lean::inc(x_10);
x_30 = l_option_map___rarg(x_10, x_7);
x_31 = l_option_get__or__else___main___rarg(x_30, x_13);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_18);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_28);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_23);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_lean_parser_command_open__spec_renaming;
lean::inc(x_35);
x_37 = l_lean_parser_syntax_mk__node(x_35, x_34);
return x_37;
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
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__1(x_4);
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
obj* x_12; obj* x_14; 
x_12 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_12);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
default:
{
obj* x_16; obj* x_18; 
lean::dec(x_2);
x_16 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_16);
if (lean::is_scalar(x_6)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_6;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
x_8 = l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__2(x_4);
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_14; obj* x_15; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_17; 
x_17 = lean::box(3);
x_14 = x_0;
x_15 = x_17;
goto lbl_16;
}
else
{
obj* x_18; obj* x_20; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
lean::dec(x_0);
x_14 = x_20;
x_15 = x_18;
goto lbl_16;
}
lbl_16:
{
obj* x_23; 
switch (lean::obj_tag(x_15)) {
case 0:
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_15, 0);
lean::inc(x_25);
lean::dec(x_15);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
x_23 = x_28;
goto lbl_24;
}
case 3:
{
obj* x_29; 
x_29 = lean::box(0);
x_23 = x_29;
goto lbl_24;
}
default:
{
obj* x_31; 
lean::dec(x_15);
x_31 = lean::box(0);
x_23 = x_31;
goto lbl_24;
}
}
lbl_24:
{
obj* x_32; obj* x_33; 
if (lean::obj_tag(x_14) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_32 = x_14;
x_33 = x_35;
goto lbl_34;
}
else
{
obj* x_36; obj* x_38; 
x_36 = lean::cnstr_get(x_14, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_14, 1);
lean::inc(x_38);
lean::dec(x_14);
x_32 = x_38;
x_33 = x_36;
goto lbl_34;
}
lbl_34:
{
obj* x_41; 
x_41 = l_lean_parser_syntax_as__node___main(x_33);
if (lean::obj_tag(x_41) == 0)
{
if (lean::obj_tag(x_32) == 0)
{
obj* x_42; obj* x_43; obj* x_45; 
x_42 = lean::box(0);
x_43 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_45, 0, x_5);
lean::cnstr_set(x_45, 1, x_23);
lean::cnstr_set(x_45, 2, x_43);
lean::cnstr_set(x_45, 3, x_42);
return x_45;
}
else
{
obj* x_46; 
x_46 = lean::cnstr_get(x_32, 0);
lean::inc(x_46);
lean::dec(x_32);
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
lean::cnstr_set(x_55, 1, x_23);
lean::cnstr_set(x_55, 2, x_53);
lean::cnstr_set(x_55, 3, x_52);
return x_55;
}
case 3:
{
obj* x_56; obj* x_57; obj* x_59; 
x_56 = lean::box(0);
x_57 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_59, 0, x_5);
lean::cnstr_set(x_59, 1, x_23);
lean::cnstr_set(x_59, 2, x_57);
lean::cnstr_set(x_59, 3, x_56);
return x_59;
}
default:
{
obj* x_61; obj* x_62; obj* x_64; 
lean::dec(x_46);
x_61 = lean::box(0);
x_62 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_62);
x_64 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_64, 0, x_5);
lean::cnstr_set(x_64, 1, x_23);
lean::cnstr_set(x_64, 2, x_62);
lean::cnstr_set(x_64, 3, x_61);
return x_64;
}
}
}
}
else
{
obj* x_65; obj* x_67; obj* x_68; obj* x_71; 
x_65 = lean::cnstr_get(x_41, 0);
lean::inc(x_65);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_67 = x_41;
} else {
 lean::dec(x_41);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
lean::dec(x_65);
x_71 = l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__1(x_68);
if (lean::obj_tag(x_32) == 0)
{
obj* x_73; obj* x_74; 
lean::dec(x_67);
x_73 = lean::box(0);
x_74 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_74, 0, x_5);
lean::cnstr_set(x_74, 1, x_23);
lean::cnstr_set(x_74, 2, x_71);
lean::cnstr_set(x_74, 3, x_73);
return x_74;
}
else
{
obj* x_75; 
x_75 = lean::cnstr_get(x_32, 0);
lean::inc(x_75);
lean::dec(x_32);
switch (lean::obj_tag(x_75)) {
case 0:
{
obj* x_78; obj* x_81; obj* x_82; 
x_78 = lean::cnstr_get(x_75, 0);
lean::inc(x_78);
lean::dec(x_75);
if (lean::is_scalar(x_67)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_67;
}
lean::cnstr_set(x_81, 0, x_78);
x_82 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_82, 0, x_5);
lean::cnstr_set(x_82, 1, x_23);
lean::cnstr_set(x_82, 2, x_71);
lean::cnstr_set(x_82, 3, x_81);
return x_82;
}
case 3:
{
obj* x_84; obj* x_85; 
lean::dec(x_67);
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_85, 0, x_5);
lean::cnstr_set(x_85, 1, x_23);
lean::cnstr_set(x_85, 2, x_71);
lean::cnstr_set(x_85, 3, x_84);
return x_85;
}
default:
{
obj* x_88; obj* x_89; 
lean::dec(x_67);
lean::dec(x_75);
x_88 = lean::box(0);
x_89 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_89, 0, x_5);
lean::cnstr_set(x_89, 1, x_23);
lean::cnstr_set(x_89, 2, x_71);
lean::cnstr_set(x_89, 3, x_88);
return x_89;
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
obj* x_5; 
x_5 = l_lean_parser_command_open__spec_hiding_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_19 = x_24;
goto lbl_20;
}
case 3:
{
obj* x_25; 
x_25 = lean::box(0);
x_19 = x_25;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
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
case 3:
{
obj* x_43; 
x_43 = lean::box(0);
x_37 = x_43;
goto lbl_38;
}
default:
{
obj* x_45; 
lean::dec(x_29);
x_45 = lean::box(0);
x_37 = x_45;
goto lbl_38;
}
}
lbl_38:
{
obj* x_46; obj* x_47; 
if (lean::obj_tag(x_28) == 0)
{
obj* x_49; 
x_49 = lean::box(3);
x_46 = x_28;
x_47 = x_49;
goto lbl_48;
}
else
{
obj* x_50; obj* x_52; 
x_50 = lean::cnstr_get(x_28, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_28, 1);
lean::inc(x_52);
lean::dec(x_28);
x_46 = x_52;
x_47 = x_50;
goto lbl_48;
}
lbl_48:
{
obj* x_55; 
x_55 = l_lean_parser_syntax_as__node___main(x_47);
if (lean::obj_tag(x_55) == 0)
{
if (lean::obj_tag(x_46) == 0)
{
obj* x_56; obj* x_57; obj* x_59; 
x_56 = lean::box(0);
x_57 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_59, 0, x_19);
lean::cnstr_set(x_59, 1, x_37);
lean::cnstr_set(x_59, 2, x_57);
lean::cnstr_set(x_59, 3, x_56);
return x_59;
}
else
{
obj* x_60; 
x_60 = lean::cnstr_get(x_46, 0);
lean::inc(x_60);
lean::dec(x_46);
switch (lean::obj_tag(x_60)) {
case 0:
{
obj* x_63; obj* x_66; obj* x_67; obj* x_69; 
x_63 = lean::cnstr_get(x_60, 0);
lean::inc(x_63);
lean::dec(x_60);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_63);
x_67 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_19);
lean::cnstr_set(x_69, 1, x_37);
lean::cnstr_set(x_69, 2, x_67);
lean::cnstr_set(x_69, 3, x_66);
return x_69;
}
case 3:
{
obj* x_70; obj* x_71; obj* x_73; 
x_70 = lean::box(0);
x_71 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_71);
x_73 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_73, 0, x_19);
lean::cnstr_set(x_73, 1, x_37);
lean::cnstr_set(x_73, 2, x_71);
lean::cnstr_set(x_73, 3, x_70);
return x_73;
}
default:
{
obj* x_75; obj* x_76; obj* x_78; 
lean::dec(x_60);
x_75 = lean::box(0);
x_76 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_76);
x_78 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_78, 0, x_19);
lean::cnstr_set(x_78, 1, x_37);
lean::cnstr_set(x_78, 2, x_76);
lean::cnstr_set(x_78, 3, x_75);
return x_78;
}
}
}
}
else
{
obj* x_79; obj* x_81; obj* x_82; obj* x_85; 
x_79 = lean::cnstr_get(x_55, 0);
lean::inc(x_79);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_81 = x_55;
} else {
 lean::dec(x_55);
 x_81 = lean::box(0);
}
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
x_85 = l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__1(x_82);
if (lean::obj_tag(x_46) == 0)
{
obj* x_87; obj* x_88; 
lean::dec(x_81);
x_87 = lean::box(0);
x_88 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_88, 0, x_19);
lean::cnstr_set(x_88, 1, x_37);
lean::cnstr_set(x_88, 2, x_85);
lean::cnstr_set(x_88, 3, x_87);
return x_88;
}
else
{
obj* x_89; 
x_89 = lean::cnstr_get(x_46, 0);
lean::inc(x_89);
lean::dec(x_46);
switch (lean::obj_tag(x_89)) {
case 0:
{
obj* x_92; obj* x_95; obj* x_96; 
x_92 = lean::cnstr_get(x_89, 0);
lean::inc(x_92);
lean::dec(x_89);
if (lean::is_scalar(x_81)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_81;
}
lean::cnstr_set(x_95, 0, x_92);
x_96 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_96, 0, x_19);
lean::cnstr_set(x_96, 1, x_37);
lean::cnstr_set(x_96, 2, x_85);
lean::cnstr_set(x_96, 3, x_95);
return x_96;
}
case 3:
{
obj* x_98; obj* x_99; 
lean::dec(x_81);
x_98 = lean::box(0);
x_99 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_99, 0, x_19);
lean::cnstr_set(x_99, 1, x_37);
lean::cnstr_set(x_99, 2, x_85);
lean::cnstr_set(x_99, 3, x_98);
return x_99;
}
default:
{
obj* x_102; obj* x_103; 
lean::dec(x_89);
lean::dec(x_81);
x_102 = lean::box(0);
x_103 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_103, 0, x_19);
lean::cnstr_set(x_103, 1, x_37);
lean::cnstr_set(x_103, 2, x_85);
lean::cnstr_set(x_103, 3, x_102);
return x_103;
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
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; 
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
x_14 = l_option_get__or__else___main___rarg(x_12, x_13);
lean::inc(x_10);
x_16 = l_option_map___rarg(x_10, x_3);
x_17 = l_option_get__or__else___main___rarg(x_16, x_13);
x_18 = l_list_map___main___at_lean_parser_command_open__spec_hiding_has__view_x_27___spec__2(x_5);
x_19 = l_lean_parser_no__kind;
lean::inc(x_19);
x_21 = l_lean_parser_syntax_mk__node(x_19, x_18);
lean::inc(x_10);
x_23 = l_option_map___rarg(x_10, x_7);
x_24 = l_option_get__or__else___main___rarg(x_23, x_13);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_21);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_17);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_14);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_command_open__spec_hiding;
lean::inc(x_30);
x_32 = l_lean_parser_syntax_mk__node(x_30, x_29);
return x_32;
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
case 3:
{
obj* x_10; 
x_10 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_10);
x_5 = x_10;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_13);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_15; obj* x_16; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_18; 
x_18 = lean::box(3);
x_15 = x_0;
x_16 = x_18;
goto lbl_17;
}
else
{
obj* x_19; obj* x_21; 
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::dec(x_0);
x_15 = x_21;
x_16 = x_19;
goto lbl_17;
}
lbl_17:
{
obj* x_24; obj* x_26; 
x_26 = l_lean_parser_syntax_as__node___main(x_16);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; 
x_27 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_27);
x_24 = x_27;
goto lbl_25;
}
else
{
obj* x_29; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 x_31 = x_26;
} else {
 lean::dec(x_26);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_32) == 0)
{
obj* x_36; 
lean::dec(x_31);
x_36 = lean::box(0);
x_24 = x_36;
goto lbl_25;
}
else
{
obj* x_37; obj* x_39; 
x_37 = lean::cnstr_get(x_32, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_32, 1);
lean::inc(x_39);
lean::dec(x_32);
if (lean::obj_tag(x_39) == 0)
{
obj* x_42; obj* x_43; obj* x_45; obj* x_46; 
x_42 = l_lean_parser_command_open__spec_as_has__view;
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::apply_1(x_43, x_37);
if (lean::is_scalar(x_31)) {
 x_46 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_46 = x_31;
}
lean::cnstr_set(x_46, 0, x_45);
x_24 = x_46;
goto lbl_25;
}
else
{
obj* x_50; 
lean::dec(x_39);
lean::dec(x_37);
lean::dec(x_31);
x_50 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_50);
x_24 = x_50;
goto lbl_25;
}
}
}
lbl_25:
{
obj* x_52; obj* x_53; 
if (lean::obj_tag(x_15) == 0)
{
obj* x_55; 
x_55 = lean::box(3);
x_52 = x_15;
x_53 = x_55;
goto lbl_54;
}
else
{
obj* x_56; obj* x_58; 
x_56 = lean::cnstr_get(x_15, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_15, 1);
lean::inc(x_58);
lean::dec(x_15);
x_52 = x_58;
x_53 = x_56;
goto lbl_54;
}
lbl_54:
{
obj* x_61; obj* x_63; 
x_63 = l_lean_parser_syntax_as__node___main(x_53);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; 
x_64 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3;
lean::inc(x_64);
x_61 = x_64;
goto lbl_62;
}
else
{
obj* x_66; obj* x_68; obj* x_69; 
x_66 = lean::cnstr_get(x_63, 0);
lean::inc(x_66);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 x_68 = x_63;
} else {
 lean::dec(x_63);
 x_68 = lean::box(0);
}
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
lean::dec(x_66);
if (lean::obj_tag(x_69) == 0)
{
obj* x_73; 
lean::dec(x_68);
x_73 = lean::box(0);
x_61 = x_73;
goto lbl_62;
}
else
{
obj* x_74; obj* x_76; 
x_74 = lean::cnstr_get(x_69, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_69, 1);
lean::inc(x_76);
lean::dec(x_69);
if (lean::obj_tag(x_76) == 0)
{
obj* x_79; obj* x_80; obj* x_82; obj* x_83; 
x_79 = l_lean_parser_command_open__spec_only_has__view;
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::apply_1(x_80, x_74);
if (lean::is_scalar(x_68)) {
 x_83 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_83 = x_68;
}
lean::cnstr_set(x_83, 0, x_82);
x_61 = x_83;
goto lbl_62;
}
else
{
obj* x_87; 
lean::dec(x_68);
lean::dec(x_74);
lean::dec(x_76);
x_87 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3;
lean::inc(x_87);
x_61 = x_87;
goto lbl_62;
}
}
}
lbl_62:
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_95; 
if (lean::obj_tag(x_52) == 0)
{
obj* x_97; 
x_97 = lean::box(3);
x_94 = x_52;
x_95 = x_97;
goto lbl_96;
}
else
{
obj* x_98; obj* x_100; 
x_98 = lean::cnstr_get(x_52, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_52, 1);
lean::inc(x_100);
lean::dec(x_52);
x_94 = x_100;
x_95 = x_98;
goto lbl_96;
}
lbl_90:
{
obj* x_103; obj* x_104; 
x_103 = lean::box(3);
x_104 = l_lean_parser_syntax_as__node___main(x_103);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_107; 
x_105 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_105);
x_107 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_107, 0, x_5);
lean::cnstr_set(x_107, 1, x_24);
lean::cnstr_set(x_107, 2, x_61);
lean::cnstr_set(x_107, 3, x_89);
lean::cnstr_set(x_107, 4, x_105);
return x_107;
}
else
{
obj* x_108; obj* x_110; obj* x_111; 
x_108 = lean::cnstr_get(x_104, 0);
lean::inc(x_108);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 x_110 = x_104;
} else {
 lean::dec(x_104);
 x_110 = lean::box(0);
}
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
lean::dec(x_108);
if (lean::obj_tag(x_111) == 0)
{
obj* x_115; obj* x_116; 
lean::dec(x_110);
x_115 = lean::box(0);
x_116 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_116, 0, x_5);
lean::cnstr_set(x_116, 1, x_24);
lean::cnstr_set(x_116, 2, x_61);
lean::cnstr_set(x_116, 3, x_89);
lean::cnstr_set(x_116, 4, x_115);
return x_116;
}
else
{
obj* x_117; obj* x_119; 
x_117 = lean::cnstr_get(x_111, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_111, 1);
lean::inc(x_119);
lean::dec(x_111);
if (lean::obj_tag(x_119) == 0)
{
obj* x_122; obj* x_123; obj* x_125; obj* x_126; obj* x_127; 
x_122 = l_lean_parser_command_open__spec_hiding_has__view;
x_123 = lean::cnstr_get(x_122, 0);
lean::inc(x_123);
x_125 = lean::apply_1(x_123, x_117);
if (lean::is_scalar(x_110)) {
 x_126 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_126 = x_110;
}
lean::cnstr_set(x_126, 0, x_125);
x_127 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_127, 0, x_5);
lean::cnstr_set(x_127, 1, x_24);
lean::cnstr_set(x_127, 2, x_61);
lean::cnstr_set(x_127, 3, x_89);
lean::cnstr_set(x_127, 4, x_126);
return x_127;
}
else
{
obj* x_131; obj* x_133; 
lean::dec(x_119);
lean::dec(x_117);
lean::dec(x_110);
x_131 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_131);
x_133 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_133, 0, x_5);
lean::cnstr_set(x_133, 1, x_24);
lean::cnstr_set(x_133, 2, x_61);
lean::cnstr_set(x_133, 3, x_89);
lean::cnstr_set(x_133, 4, x_131);
return x_133;
}
}
}
}
lbl_93:
{
obj* x_134; 
x_134 = l_lean_parser_syntax_as__node___main(x_92);
if (lean::obj_tag(x_134) == 0)
{
obj* x_135; obj* x_137; 
x_135 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_135);
x_137 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_137, 0, x_5);
lean::cnstr_set(x_137, 1, x_24);
lean::cnstr_set(x_137, 2, x_61);
lean::cnstr_set(x_137, 3, x_91);
lean::cnstr_set(x_137, 4, x_135);
return x_137;
}
else
{
obj* x_138; obj* x_140; obj* x_141; 
x_138 = lean::cnstr_get(x_134, 0);
lean::inc(x_138);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 x_140 = x_134;
} else {
 lean::dec(x_134);
 x_140 = lean::box(0);
}
x_141 = lean::cnstr_get(x_138, 1);
lean::inc(x_141);
lean::dec(x_138);
if (lean::obj_tag(x_141) == 0)
{
obj* x_145; obj* x_146; 
lean::dec(x_140);
x_145 = lean::box(0);
x_146 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_146, 0, x_5);
lean::cnstr_set(x_146, 1, x_24);
lean::cnstr_set(x_146, 2, x_61);
lean::cnstr_set(x_146, 3, x_91);
lean::cnstr_set(x_146, 4, x_145);
return x_146;
}
else
{
obj* x_147; obj* x_149; 
x_147 = lean::cnstr_get(x_141, 0);
lean::inc(x_147);
x_149 = lean::cnstr_get(x_141, 1);
lean::inc(x_149);
lean::dec(x_141);
if (lean::obj_tag(x_149) == 0)
{
obj* x_152; obj* x_153; obj* x_155; obj* x_156; obj* x_157; 
x_152 = l_lean_parser_command_open__spec_hiding_has__view;
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_155 = lean::apply_1(x_153, x_147);
if (lean::is_scalar(x_140)) {
 x_156 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_156 = x_140;
}
lean::cnstr_set(x_156, 0, x_155);
x_157 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_157, 0, x_5);
lean::cnstr_set(x_157, 1, x_24);
lean::cnstr_set(x_157, 2, x_61);
lean::cnstr_set(x_157, 3, x_91);
lean::cnstr_set(x_157, 4, x_156);
return x_157;
}
else
{
obj* x_161; obj* x_163; 
lean::dec(x_140);
lean::dec(x_147);
lean::dec(x_149);
x_161 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_161);
x_163 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_163, 0, x_5);
lean::cnstr_set(x_163, 1, x_24);
lean::cnstr_set(x_163, 2, x_61);
lean::cnstr_set(x_163, 3, x_91);
lean::cnstr_set(x_163, 4, x_161);
return x_163;
}
}
}
}
lbl_96:
{
obj* x_164; 
x_164 = l_lean_parser_syntax_as__node___main(x_95);
if (lean::obj_tag(x_164) == 0)
{
if (lean::obj_tag(x_94) == 0)
{
obj* x_165; 
x_165 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_165);
x_89 = x_165;
goto lbl_90;
}
else
{
obj* x_167; obj* x_170; 
x_167 = lean::cnstr_get(x_94, 0);
lean::inc(x_167);
lean::dec(x_94);
x_170 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_170);
x_91 = x_170;
x_92 = x_167;
goto lbl_93;
}
}
else
{
obj* x_172; obj* x_174; obj* x_175; 
x_172 = lean::cnstr_get(x_164, 0);
lean::inc(x_172);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 x_174 = x_164;
} else {
 lean::dec(x_164);
 x_174 = lean::box(0);
}
x_175 = lean::cnstr_get(x_172, 1);
lean::inc(x_175);
lean::dec(x_172);
if (lean::obj_tag(x_175) == 0)
{
obj* x_179; 
lean::dec(x_174);
x_179 = lean::box(0);
if (lean::obj_tag(x_94) == 0)
{
x_89 = x_179;
goto lbl_90;
}
else
{
obj* x_180; 
x_180 = lean::cnstr_get(x_94, 0);
lean::inc(x_180);
lean::dec(x_94);
x_91 = x_179;
x_92 = x_180;
goto lbl_93;
}
}
else
{
obj* x_183; obj* x_185; 
x_183 = lean::cnstr_get(x_175, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_175, 1);
lean::inc(x_185);
lean::dec(x_175);
if (lean::obj_tag(x_185) == 0)
{
obj* x_188; obj* x_189; obj* x_191; obj* x_192; 
x_188 = l_lean_parser_command_open__spec_renaming_has__view;
x_189 = lean::cnstr_get(x_188, 0);
lean::inc(x_189);
x_191 = lean::apply_1(x_189, x_183);
if (lean::is_scalar(x_174)) {
 x_192 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_192 = x_174;
}
lean::cnstr_set(x_192, 0, x_191);
if (lean::obj_tag(x_94) == 0)
{
x_89 = x_192;
goto lbl_90;
}
else
{
obj* x_193; 
x_193 = lean::cnstr_get(x_94, 0);
lean::inc(x_193);
lean::dec(x_94);
x_91 = x_192;
x_92 = x_193;
goto lbl_93;
}
}
else
{
lean::dec(x_185);
lean::dec(x_183);
lean::dec(x_174);
if (lean::obj_tag(x_94) == 0)
{
obj* x_199; 
x_199 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_199);
x_89 = x_199;
goto lbl_90;
}
else
{
obj* x_201; obj* x_204; 
x_201 = lean::cnstr_get(x_94, 0);
lean::inc(x_201);
lean::dec(x_94);
x_204 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_204);
x_91 = x_204;
x_92 = x_201;
goto lbl_93;
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
obj* x_5; 
x_5 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__5;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_21; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_19 = x_21;
goto lbl_20;
}
case 3:
{
obj* x_24; 
x_24 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_24);
x_19 = x_24;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_27);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
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
x_40 = l_lean_parser_syntax_as__node___main(x_30);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; 
x_41 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_41);
x_38 = x_41;
goto lbl_39;
}
else
{
obj* x_43; obj* x_45; obj* x_46; 
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_45 = x_40;
} else {
 lean::dec(x_40);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
if (lean::obj_tag(x_46) == 0)
{
obj* x_50; 
lean::dec(x_45);
x_50 = lean::box(0);
x_38 = x_50;
goto lbl_39;
}
else
{
obj* x_51; obj* x_53; 
x_51 = lean::cnstr_get(x_46, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_46, 1);
lean::inc(x_53);
lean::dec(x_46);
if (lean::obj_tag(x_53) == 0)
{
obj* x_56; obj* x_57; obj* x_59; obj* x_60; 
x_56 = l_lean_parser_command_open__spec_as_has__view;
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::apply_1(x_57, x_51);
if (lean::is_scalar(x_45)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_45;
}
lean::cnstr_set(x_60, 0, x_59);
x_38 = x_60;
goto lbl_39;
}
else
{
obj* x_64; 
lean::dec(x_53);
lean::dec(x_45);
lean::dec(x_51);
x_64 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_64);
x_38 = x_64;
goto lbl_39;
}
}
}
lbl_39:
{
obj* x_66; obj* x_67; 
if (lean::obj_tag(x_29) == 0)
{
obj* x_69; 
x_69 = lean::box(3);
x_66 = x_29;
x_67 = x_69;
goto lbl_68;
}
else
{
obj* x_70; obj* x_72; 
x_70 = lean::cnstr_get(x_29, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_29, 1);
lean::inc(x_72);
lean::dec(x_29);
x_66 = x_72;
x_67 = x_70;
goto lbl_68;
}
lbl_68:
{
obj* x_75; obj* x_77; 
x_77 = l_lean_parser_syntax_as__node___main(x_67);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; 
x_78 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3;
lean::inc(x_78);
x_75 = x_78;
goto lbl_76;
}
else
{
obj* x_80; obj* x_82; obj* x_83; 
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 x_82 = x_77;
} else {
 lean::dec(x_77);
 x_82 = lean::box(0);
}
x_83 = lean::cnstr_get(x_80, 1);
lean::inc(x_83);
lean::dec(x_80);
if (lean::obj_tag(x_83) == 0)
{
obj* x_87; 
lean::dec(x_82);
x_87 = lean::box(0);
x_75 = x_87;
goto lbl_76;
}
else
{
obj* x_88; obj* x_90; 
x_88 = lean::cnstr_get(x_83, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_83, 1);
lean::inc(x_90);
lean::dec(x_83);
if (lean::obj_tag(x_90) == 0)
{
obj* x_93; obj* x_94; obj* x_96; obj* x_97; 
x_93 = l_lean_parser_command_open__spec_only_has__view;
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_96 = lean::apply_1(x_94, x_88);
if (lean::is_scalar(x_82)) {
 x_97 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_97 = x_82;
}
lean::cnstr_set(x_97, 0, x_96);
x_75 = x_97;
goto lbl_76;
}
else
{
obj* x_101; 
lean::dec(x_88);
lean::dec(x_90);
lean::dec(x_82);
x_101 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__3;
lean::inc(x_101);
x_75 = x_101;
goto lbl_76;
}
}
}
lbl_76:
{
obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_109; 
if (lean::obj_tag(x_66) == 0)
{
obj* x_111; 
x_111 = lean::box(3);
x_108 = x_66;
x_109 = x_111;
goto lbl_110;
}
else
{
obj* x_112; obj* x_114; 
x_112 = lean::cnstr_get(x_66, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_66, 1);
lean::inc(x_114);
lean::dec(x_66);
x_108 = x_114;
x_109 = x_112;
goto lbl_110;
}
lbl_104:
{
obj* x_117; obj* x_118; 
x_117 = lean::box(3);
x_118 = l_lean_parser_syntax_as__node___main(x_117);
if (lean::obj_tag(x_118) == 0)
{
obj* x_119; obj* x_121; 
x_119 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_119);
x_121 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_121, 0, x_19);
lean::cnstr_set(x_121, 1, x_38);
lean::cnstr_set(x_121, 2, x_75);
lean::cnstr_set(x_121, 3, x_103);
lean::cnstr_set(x_121, 4, x_119);
return x_121;
}
else
{
obj* x_122; obj* x_124; obj* x_125; 
x_122 = lean::cnstr_get(x_118, 0);
lean::inc(x_122);
if (lean::is_exclusive(x_118)) {
 lean::cnstr_release(x_118, 0);
 x_124 = x_118;
} else {
 lean::dec(x_118);
 x_124 = lean::box(0);
}
x_125 = lean::cnstr_get(x_122, 1);
lean::inc(x_125);
lean::dec(x_122);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_130; 
lean::dec(x_124);
x_129 = lean::box(0);
x_130 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_130, 0, x_19);
lean::cnstr_set(x_130, 1, x_38);
lean::cnstr_set(x_130, 2, x_75);
lean::cnstr_set(x_130, 3, x_103);
lean::cnstr_set(x_130, 4, x_129);
return x_130;
}
else
{
obj* x_131; obj* x_133; 
x_131 = lean::cnstr_get(x_125, 0);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_125, 1);
lean::inc(x_133);
lean::dec(x_125);
if (lean::obj_tag(x_133) == 0)
{
obj* x_136; obj* x_137; obj* x_139; obj* x_140; obj* x_141; 
x_136 = l_lean_parser_command_open__spec_hiding_has__view;
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
x_139 = lean::apply_1(x_137, x_131);
if (lean::is_scalar(x_124)) {
 x_140 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_140 = x_124;
}
lean::cnstr_set(x_140, 0, x_139);
x_141 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_141, 0, x_19);
lean::cnstr_set(x_141, 1, x_38);
lean::cnstr_set(x_141, 2, x_75);
lean::cnstr_set(x_141, 3, x_103);
lean::cnstr_set(x_141, 4, x_140);
return x_141;
}
else
{
obj* x_145; obj* x_147; 
lean::dec(x_133);
lean::dec(x_131);
lean::dec(x_124);
x_145 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_145);
x_147 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_147, 0, x_19);
lean::cnstr_set(x_147, 1, x_38);
lean::cnstr_set(x_147, 2, x_75);
lean::cnstr_set(x_147, 3, x_103);
lean::cnstr_set(x_147, 4, x_145);
return x_147;
}
}
}
}
lbl_107:
{
obj* x_148; 
x_148 = l_lean_parser_syntax_as__node___main(x_106);
if (lean::obj_tag(x_148) == 0)
{
obj* x_149; obj* x_151; 
x_149 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_149);
x_151 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_151, 0, x_19);
lean::cnstr_set(x_151, 1, x_38);
lean::cnstr_set(x_151, 2, x_75);
lean::cnstr_set(x_151, 3, x_105);
lean::cnstr_set(x_151, 4, x_149);
return x_151;
}
else
{
obj* x_152; obj* x_154; obj* x_155; 
x_152 = lean::cnstr_get(x_148, 0);
lean::inc(x_152);
if (lean::is_exclusive(x_148)) {
 lean::cnstr_release(x_148, 0);
 x_154 = x_148;
} else {
 lean::dec(x_148);
 x_154 = lean::box(0);
}
x_155 = lean::cnstr_get(x_152, 1);
lean::inc(x_155);
lean::dec(x_152);
if (lean::obj_tag(x_155) == 0)
{
obj* x_159; obj* x_160; 
lean::dec(x_154);
x_159 = lean::box(0);
x_160 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_160, 0, x_19);
lean::cnstr_set(x_160, 1, x_38);
lean::cnstr_set(x_160, 2, x_75);
lean::cnstr_set(x_160, 3, x_105);
lean::cnstr_set(x_160, 4, x_159);
return x_160;
}
else
{
obj* x_161; obj* x_163; 
x_161 = lean::cnstr_get(x_155, 0);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_155, 1);
lean::inc(x_163);
lean::dec(x_155);
if (lean::obj_tag(x_163) == 0)
{
obj* x_166; obj* x_167; obj* x_169; obj* x_170; obj* x_171; 
x_166 = l_lean_parser_command_open__spec_hiding_has__view;
x_167 = lean::cnstr_get(x_166, 0);
lean::inc(x_167);
x_169 = lean::apply_1(x_167, x_161);
if (lean::is_scalar(x_154)) {
 x_170 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_170 = x_154;
}
lean::cnstr_set(x_170, 0, x_169);
x_171 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_171, 0, x_19);
lean::cnstr_set(x_171, 1, x_38);
lean::cnstr_set(x_171, 2, x_75);
lean::cnstr_set(x_171, 3, x_105);
lean::cnstr_set(x_171, 4, x_170);
return x_171;
}
else
{
obj* x_175; obj* x_177; 
lean::dec(x_154);
lean::dec(x_161);
lean::dec(x_163);
x_175 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_175);
x_177 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_177, 0, x_19);
lean::cnstr_set(x_177, 1, x_38);
lean::cnstr_set(x_177, 2, x_75);
lean::cnstr_set(x_177, 3, x_105);
lean::cnstr_set(x_177, 4, x_175);
return x_177;
}
}
}
}
lbl_110:
{
obj* x_178; 
x_178 = l_lean_parser_syntax_as__node___main(x_109);
if (lean::obj_tag(x_178) == 0)
{
if (lean::obj_tag(x_108) == 0)
{
obj* x_179; 
x_179 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_179);
x_103 = x_179;
goto lbl_104;
}
else
{
obj* x_181; obj* x_184; 
x_181 = lean::cnstr_get(x_108, 0);
lean::inc(x_181);
lean::dec(x_108);
x_184 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_184);
x_105 = x_184;
x_106 = x_181;
goto lbl_107;
}
}
else
{
obj* x_186; obj* x_188; obj* x_189; 
x_186 = lean::cnstr_get(x_178, 0);
lean::inc(x_186);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 x_188 = x_178;
} else {
 lean::dec(x_178);
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
if (lean::obj_tag(x_108) == 0)
{
x_103 = x_193;
goto lbl_104;
}
else
{
obj* x_194; 
x_194 = lean::cnstr_get(x_108, 0);
lean::inc(x_194);
lean::dec(x_108);
x_105 = x_193;
x_106 = x_194;
goto lbl_107;
}
}
else
{
obj* x_197; obj* x_199; 
x_197 = lean::cnstr_get(x_189, 0);
lean::inc(x_197);
x_199 = lean::cnstr_get(x_189, 1);
lean::inc(x_199);
lean::dec(x_189);
if (lean::obj_tag(x_199) == 0)
{
obj* x_202; obj* x_203; obj* x_205; obj* x_206; 
x_202 = l_lean_parser_command_open__spec_renaming_has__view;
x_203 = lean::cnstr_get(x_202, 0);
lean::inc(x_203);
x_205 = lean::apply_1(x_203, x_197);
if (lean::is_scalar(x_188)) {
 x_206 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_206 = x_188;
}
lean::cnstr_set(x_206, 0, x_205);
if (lean::obj_tag(x_108) == 0)
{
x_103 = x_206;
goto lbl_104;
}
else
{
obj* x_207; 
x_207 = lean::cnstr_get(x_108, 0);
lean::inc(x_207);
lean::dec(x_108);
x_105 = x_206;
x_106 = x_207;
goto lbl_107;
}
}
else
{
lean::dec(x_199);
lean::dec(x_197);
lean::dec(x_188);
if (lean::obj_tag(x_108) == 0)
{
obj* x_213; 
x_213 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_213);
x_103 = x_213;
goto lbl_104;
}
else
{
obj* x_215; obj* x_218; 
x_215 = lean::cnstr_get(x_108, 0);
lean::inc(x_215);
lean::dec(x_108);
x_218 = l_lean_parser_command_open__spec_has__view_x_27___lambda__1___closed__2;
lean::inc(x_218);
x_105 = x_218;
x_106 = x_215;
goto lbl_107;
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
obj* x_16; 
x_16 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_16);
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; 
x_18 = lean::cnstr_get(x_3, 0);
lean::inc(x_18);
lean::dec(x_3);
x_21 = l_lean_parser_command_open__spec_as_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_18);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_13);
x_26 = l_lean_parser_no__kind;
lean::inc(x_26);
x_28 = l_lean_parser_syntax_mk__node(x_26, x_25);
x_14 = x_28;
goto lbl_15;
}
lbl_15:
{
obj* x_29; obj* x_31; obj* x_32; 
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_34; 
x_34 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_34);
x_29 = x_34;
goto lbl_30;
}
else
{
obj* x_36; obj* x_39; 
x_36 = lean::cnstr_get(x_7, 0);
lean::inc(x_36);
lean::dec(x_7);
x_39 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_39);
x_31 = x_39;
x_32 = x_36;
goto lbl_33;
}
}
else
{
obj* x_41; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_51; 
x_41 = lean::cnstr_get(x_5, 0);
lean::inc(x_41);
lean::dec(x_5);
x_44 = l_lean_parser_command_open__spec_only_has__view;
x_45 = lean::cnstr_get(x_44, 1);
lean::inc(x_45);
x_47 = lean::apply_1(x_45, x_41);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_13);
x_49 = l_lean_parser_no__kind;
lean::inc(x_49);
x_51 = l_lean_parser_syntax_mk__node(x_49, x_48);
if (lean::obj_tag(x_7) == 0)
{
x_29 = x_51;
goto lbl_30;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_7, 0);
lean::inc(x_52);
lean::dec(x_7);
x_31 = x_51;
x_32 = x_52;
goto lbl_33;
}
}
lbl_30:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_62; 
x_55 = l_lean_parser_term_binder__content_has__view_x_27___lambda__2___closed__2;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_29);
lean::cnstr_set(x_57, 1, x_55);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_14);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_12);
lean::cnstr_set(x_59, 1, x_58);
x_60 = l_lean_parser_command_open__spec;
lean::inc(x_60);
x_62 = l_lean_parser_syntax_mk__node(x_60, x_59);
return x_62;
}
else
{
obj* x_63; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_83; 
x_63 = lean::cnstr_get(x_9, 0);
lean::inc(x_63);
lean::dec(x_9);
x_66 = l_lean_parser_command_open__spec_hiding_has__view;
x_67 = lean::cnstr_get(x_66, 1);
lean::inc(x_67);
x_69 = lean::apply_1(x_67, x_63);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_13);
x_71 = l_lean_parser_no__kind;
lean::inc(x_71);
x_73 = l_lean_parser_syntax_mk__node(x_71, x_70);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_13);
x_75 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set(x_77, 1, x_74);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_29);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_14);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_12);
lean::cnstr_set(x_80, 1, x_79);
x_81 = l_lean_parser_command_open__spec;
lean::inc(x_81);
x_83 = l_lean_parser_syntax_mk__node(x_81, x_80);
return x_83;
}
}
lbl_33:
{
obj* x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_91; 
x_84 = l_lean_parser_command_open__spec_renaming_has__view;
x_85 = lean::cnstr_get(x_84, 1);
lean::inc(x_85);
x_87 = lean::apply_1(x_85, x_32);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_13);
x_89 = l_lean_parser_no__kind;
lean::inc(x_89);
x_91 = l_lean_parser_syntax_mk__node(x_89, x_88);
if (lean::obj_tag(x_9) == 0)
{
obj* x_92; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_100; 
x_92 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_91);
lean::cnstr_set(x_94, 1, x_92);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_31);
lean::cnstr_set(x_95, 1, x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_14);
lean::cnstr_set(x_96, 1, x_95);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_12);
lean::cnstr_set(x_97, 1, x_96);
x_98 = l_lean_parser_command_open__spec;
lean::inc(x_98);
x_100 = l_lean_parser_syntax_mk__node(x_98, x_97);
return x_100;
}
else
{
obj* x_101; obj* x_104; obj* x_105; obj* x_107; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_118; 
x_101 = lean::cnstr_get(x_9, 0);
lean::inc(x_101);
lean::dec(x_9);
x_104 = l_lean_parser_command_open__spec_hiding_has__view;
x_105 = lean::cnstr_get(x_104, 1);
lean::inc(x_105);
x_107 = lean::apply_1(x_105, x_101);
x_108 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_13);
lean::inc(x_89);
x_110 = l_lean_parser_syntax_mk__node(x_89, x_108);
x_111 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_13);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_91);
lean::cnstr_set(x_112, 1, x_111);
x_113 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_113, 0, x_31);
lean::cnstr_set(x_113, 1, x_112);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_14);
lean::cnstr_set(x_114, 1, x_113);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_12);
lean::cnstr_set(x_115, 1, x_114);
x_116 = l_lean_parser_command_open__spec;
lean::inc(x_116);
x_118 = l_lean_parser_syntax_mk__node(x_116, x_115);
return x_118;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_102; obj* x_107; 
x_0 = lean::mk_string("as");
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
lean::inc(x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_6);
lean::inc(x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_lean_parser_command_open__spec_as;
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::mk_string("(");
x_17 = l_string_trim(x_16);
lean::inc(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_17);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_20, 0, x_17);
lean::closure_set(x_20, 1, x_4);
lean::closure_set(x_20, 2, x_19);
lean::inc(x_9);
lean::inc(x_20);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_9);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_24, 0, x_23);
lean::inc(x_7);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__2), 5, 1);
lean::closure_set(x_26, 0, x_7);
x_27 = lean::mk_string(")");
x_28 = l_string_trim(x_27);
lean::inc(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_30, 0, x_28);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_31, 0, x_28);
lean::closure_set(x_31, 1, x_4);
lean::closure_set(x_31, 2, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_6);
lean::inc(x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_26);
lean::cnstr_set(x_34, 1, x_32);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_24);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_lean_parser_command_open__spec_only;
lean::inc(x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_38, 0, x_36);
lean::closure_set(x_38, 1, x_35);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_39, 0, x_38);
x_40 = lean::mk_string("renaming");
x_41 = l_string_trim(x_40);
lean::inc(x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_43, 0, x_41);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_44, 0, x_41);
lean::closure_set(x_44, 1, x_4);
lean::closure_set(x_44, 2, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_6);
lean::inc(x_20);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_45);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_48, 0, x_47);
x_49 = lean::mk_string("->");
x_50 = l_string_trim(x_49);
lean::inc(x_50);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_52, 0, x_50);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_53, 0, x_50);
lean::closure_set(x_53, 1, x_4);
lean::closure_set(x_53, 2, x_52);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_9);
lean::inc(x_7);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_7);
lean::cnstr_set(x_56, 1, x_54);
x_57 = l_lean_parser_command_open__spec_renaming_item;
lean::inc(x_57);
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_59, 0, x_57);
lean::closure_set(x_59, 1, x_56);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_60, 0, x_59);
lean::inc(x_32);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_32);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_48);
lean::cnstr_set(x_63, 1, x_62);
x_64 = l_lean_parser_command_open__spec_renaming;
lean::inc(x_64);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_66, 0, x_64);
lean::closure_set(x_66, 1, x_63);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_67, 0, x_66);
x_68 = lean::mk_string("hiding");
x_69 = l_string_trim(x_68);
lean::inc(x_69);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_71, 0, x_69);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_72, 0, x_69);
lean::closure_set(x_72, 1, x_4);
lean::closure_set(x_72, 2, x_71);
lean::inc(x_7);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_74, 0, x_7);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_32);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_72);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_20);
lean::cnstr_set(x_77, 1, x_76);
x_78 = l_lean_parser_command_open__spec_hiding;
lean::inc(x_78);
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_80, 0, x_78);
lean::closure_set(x_80, 1, x_77);
x_81 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_6);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_67);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_39);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_15);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_7);
lean::cnstr_set(x_86, 1, x_85);
x_87 = l_lean_parser_command_open__spec;
lean::inc(x_86);
lean::inc(x_87);
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_90, 0, x_87);
lean::closure_set(x_90, 1, x_86);
x_91 = l_lean_parser_command__parser__m_monad___closed__1;
x_92 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_93 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_94 = l_lean_parser_command__parser__m_alternative___closed__1;
x_95 = l_lean_parser_command_open__spec_has__view;
lean::inc(x_95);
lean::inc(x_87);
lean::inc(x_94);
lean::inc(x_93);
lean::inc(x_92);
lean::inc(x_91);
x_102 = l_lean_parser_combinators_node_view___rarg(x_91, x_92, x_93, x_94, x_87, x_86, x_95);
lean::inc(x_94);
lean::inc(x_93);
lean::inc(x_92);
lean::inc(x_91);
x_107 = l_lean_parser_combinators_many1_view___rarg(x_91, x_92, x_93, x_94, x_90, x_102);
return x_107;
}
}
obj* _init_l_lean_parser_command_open__spec_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_0 = lean::box(0);
x_1 = lean::mk_string("as");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_lean_parser_symbol_tokens___rarg(x_1, x_2);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
lean::inc(x_4);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_3, x_4);
x_7 = l_lean_parser_tokens___rarg(x_6);
x_8 = l_lean_parser_tokens___rarg(x_7);
x_9 = lean::mk_string("(");
x_10 = l_lean_parser_symbol_tokens___rarg(x_9, x_2);
lean::inc(x_4);
lean::inc(x_10);
x_13 = l_lean_parser_list_cons_tokens___rarg(x_10, x_4);
x_14 = l_lean_parser_tokens___rarg(x_13);
x_15 = l_lean_parser_tokens___rarg(x_14);
x_16 = l_lean_parser_tokens___rarg(x_0);
x_17 = lean::mk_string(")");
x_18 = l_lean_parser_symbol_tokens___rarg(x_17, x_2);
x_19 = l_lean_parser_list_cons_tokens___rarg(x_18, x_0);
lean::inc(x_19);
x_21 = l_lean_parser_list_cons_tokens___rarg(x_16, x_19);
lean::inc(x_21);
x_23 = l_lean_parser_list_cons_tokens___rarg(x_15, x_21);
x_24 = l_lean_parser_tokens___rarg(x_23);
x_25 = l_lean_parser_tokens___rarg(x_24);
x_26 = lean::mk_string("renaming");
x_27 = l_lean_parser_symbol_tokens___rarg(x_26, x_2);
x_28 = l_lean_parser_list_cons_tokens___rarg(x_27, x_0);
lean::inc(x_10);
x_30 = l_lean_parser_list_cons_tokens___rarg(x_10, x_28);
x_31 = l_lean_parser_tokens___rarg(x_30);
x_32 = l_lean_parser_tokens___rarg(x_31);
x_33 = lean::mk_string("->");
x_34 = l_lean_parser_symbol_tokens___rarg(x_33, x_2);
x_35 = l_lean_parser_list_cons_tokens___rarg(x_34, x_4);
x_36 = l_lean_parser_list_cons_tokens___rarg(x_0, x_35);
x_37 = l_lean_parser_tokens___rarg(x_36);
x_38 = l_lean_parser_tokens___rarg(x_37);
x_39 = l_lean_parser_list_cons_tokens___rarg(x_38, x_19);
x_40 = l_lean_parser_list_cons_tokens___rarg(x_32, x_39);
x_41 = l_lean_parser_tokens___rarg(x_40);
x_42 = l_lean_parser_tokens___rarg(x_41);
x_43 = lean::mk_string("hiding");
x_44 = l_lean_parser_symbol_tokens___rarg(x_43, x_2);
x_45 = l_lean_parser_list_cons_tokens___rarg(x_44, x_21);
x_46 = l_lean_parser_list_cons_tokens___rarg(x_10, x_45);
x_47 = l_lean_parser_tokens___rarg(x_46);
x_48 = l_lean_parser_tokens___rarg(x_47);
x_49 = l_lean_parser_list_cons_tokens___rarg(x_48, x_0);
x_50 = l_lean_parser_list_cons_tokens___rarg(x_42, x_49);
x_51 = l_lean_parser_list_cons_tokens___rarg(x_25, x_50);
x_52 = l_lean_parser_list_cons_tokens___rarg(x_8, x_51);
x_53 = l_lean_parser_list_cons_tokens___rarg(x_0, x_52);
x_54 = l_lean_parser_tokens___rarg(x_53);
x_55 = l_lean_parser_tokens___rarg(x_54);
return x_55;
}
}
obj* _init_l_lean_parser_command_open__spec_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_89; 
x_0 = lean::mk_string("as");
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
lean::inc(x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_6);
lean::inc(x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_lean_parser_command_open__spec_as;
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::mk_string("(");
x_17 = l_string_trim(x_16);
lean::inc(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_17);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_20, 0, x_17);
lean::closure_set(x_20, 1, x_4);
lean::closure_set(x_20, 2, x_19);
lean::inc(x_9);
lean::inc(x_20);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_9);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_24, 0, x_23);
lean::inc(x_7);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__2), 5, 1);
lean::closure_set(x_26, 0, x_7);
x_27 = lean::mk_string(")");
x_28 = l_string_trim(x_27);
lean::inc(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_30, 0, x_28);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_31, 0, x_28);
lean::closure_set(x_31, 1, x_4);
lean::closure_set(x_31, 2, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_6);
lean::inc(x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_26);
lean::cnstr_set(x_34, 1, x_32);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_24);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_lean_parser_command_open__spec_only;
lean::inc(x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_38, 0, x_36);
lean::closure_set(x_38, 1, x_35);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_39, 0, x_38);
x_40 = lean::mk_string("renaming");
x_41 = l_string_trim(x_40);
lean::inc(x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_43, 0, x_41);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_44, 0, x_41);
lean::closure_set(x_44, 1, x_4);
lean::closure_set(x_44, 2, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_6);
lean::inc(x_20);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_45);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_48, 0, x_47);
x_49 = lean::mk_string("->");
x_50 = l_string_trim(x_49);
lean::inc(x_50);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_52, 0, x_50);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_53, 0, x_50);
lean::closure_set(x_53, 1, x_4);
lean::closure_set(x_53, 2, x_52);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_9);
lean::inc(x_7);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_7);
lean::cnstr_set(x_56, 1, x_54);
x_57 = l_lean_parser_command_open__spec_renaming_item;
lean::inc(x_57);
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_59, 0, x_57);
lean::closure_set(x_59, 1, x_56);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_60, 0, x_59);
lean::inc(x_32);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_32);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_48);
lean::cnstr_set(x_63, 1, x_62);
x_64 = l_lean_parser_command_open__spec_renaming;
lean::inc(x_64);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_66, 0, x_64);
lean::closure_set(x_66, 1, x_63);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_67, 0, x_66);
x_68 = lean::mk_string("hiding");
x_69 = l_string_trim(x_68);
lean::inc(x_69);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_71, 0, x_69);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_72, 0, x_69);
lean::closure_set(x_72, 1, x_4);
lean::closure_set(x_72, 2, x_71);
lean::inc(x_7);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_74, 0, x_7);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_32);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_72);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_20);
lean::cnstr_set(x_77, 1, x_76);
x_78 = l_lean_parser_command_open__spec_hiding;
lean::inc(x_78);
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_80, 0, x_78);
lean::closure_set(x_80, 1, x_77);
x_81 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_6);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_67);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_39);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_15);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_7);
lean::cnstr_set(x_86, 1, x_85);
x_87 = l_lean_parser_command_open__spec;
lean::inc(x_87);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_89, 0, x_87);
lean::closure_set(x_89, 1, x_86);
return x_89;
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
obj* x_5; obj* x_7; 
x_5 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
else
{
obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_14);
x_16 = l_list_map___main___rarg(x_14, x_11);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
obj* x_7; 
x_7 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3;
lean::inc(x_7);
return x_7;
}
else
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_11 = x_6;
} else {
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::obj_tag(x_12) == 0)
{
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; 
x_16 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3;
lean::inc(x_16);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_21 = lean::box(0);
x_3 = x_21;
x_4 = x_18;
goto lbl_5;
}
}
else
{
obj* x_22; obj* x_24; 
x_22 = lean::cnstr_get(x_12, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_12, 1);
lean::inc(x_24);
lean::dec(x_12);
switch (lean::obj_tag(x_22)) {
case 0:
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
lean::dec(x_22);
if (lean::is_scalar(x_11)) {
 x_30 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_30 = x_11;
}
lean::cnstr_set(x_30, 0, x_27);
if (lean::obj_tag(x_24) == 0)
{
x_1 = x_30;
goto lbl_2;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
x_3 = x_30;
x_4 = x_31;
goto lbl_5;
}
}
case 3:
{
lean::dec(x_11);
if (lean::obj_tag(x_24) == 0)
{
obj* x_35; 
x_35 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3;
lean::inc(x_35);
return x_35;
}
else
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_24, 0);
lean::inc(x_37);
lean::dec(x_24);
x_40 = lean::box(0);
x_3 = x_40;
x_4 = x_37;
goto lbl_5;
}
}
default:
{
lean::dec(x_11);
lean::dec(x_22);
if (lean::obj_tag(x_24) == 0)
{
obj* x_43; 
x_43 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__3;
lean::inc(x_43);
return x_43;
}
else
{
obj* x_45; obj* x_48; 
x_45 = lean::cnstr_get(x_24, 0);
lean::inc(x_45);
lean::dec(x_24);
x_48 = lean::box(0);
x_3 = x_48;
x_4 = x_45;
goto lbl_5;
}
}
}
}
}
lbl_2:
{
obj* x_49; obj* x_50; 
x_49 = lean::box(3);
x_50 = l_lean_parser_syntax_as__node___main(x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; 
x_51 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_1);
lean::cnstr_set(x_53, 1, x_51);
return x_53;
}
else
{
obj* x_54; obj* x_57; obj* x_60; obj* x_62; obj* x_63; 
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
lean::dec(x_50);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
x_60 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_60);
x_62 = l_list_map___main___rarg(x_60, x_57);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_1);
lean::cnstr_set(x_63, 1, x_62);
return x_63;
}
}
lbl_5:
{
obj* x_64; 
x_64 = l_lean_parser_syntax_as__node___main(x_4);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_67; 
x_65 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_3);
lean::cnstr_set(x_67, 1, x_65);
return x_67;
}
else
{
obj* x_68; obj* x_71; obj* x_74; obj* x_76; obj* x_77; 
x_68 = lean::cnstr_get(x_64, 0);
lean::inc(x_68);
lean::dec(x_64);
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
x_74 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_74);
x_76 = l_list_map___main___rarg(x_74, x_71);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_3);
lean::cnstr_set(x_77, 1, x_76);
return x_77;
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
obj* x_5; obj* x_7; 
x_5 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
else
{
obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_14);
x_16 = l_list_map___main___rarg(x_14, x_11);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
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
obj* x_7; 
x_7 = l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1;
lean::inc(x_7);
return x_7;
}
else
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_11 = x_6;
} else {
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::obj_tag(x_12) == 0)
{
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; 
x_16 = l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1;
lean::inc(x_16);
return x_16;
}
else
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_21 = lean::box(0);
x_3 = x_21;
x_4 = x_18;
goto lbl_5;
}
}
else
{
obj* x_22; obj* x_24; 
x_22 = lean::cnstr_get(x_12, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_12, 1);
lean::inc(x_24);
lean::dec(x_12);
switch (lean::obj_tag(x_22)) {
case 0:
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
lean::dec(x_22);
if (lean::is_scalar(x_11)) {
 x_30 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_30 = x_11;
}
lean::cnstr_set(x_30, 0, x_27);
if (lean::obj_tag(x_24) == 0)
{
x_1 = x_30;
goto lbl_2;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
x_3 = x_30;
x_4 = x_31;
goto lbl_5;
}
}
case 3:
{
lean::dec(x_11);
if (lean::obj_tag(x_24) == 0)
{
obj* x_35; 
x_35 = l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1;
lean::inc(x_35);
return x_35;
}
else
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_24, 0);
lean::inc(x_37);
lean::dec(x_24);
x_40 = lean::box(0);
x_3 = x_40;
x_4 = x_37;
goto lbl_5;
}
}
default:
{
lean::dec(x_11);
lean::dec(x_22);
if (lean::obj_tag(x_24) == 0)
{
obj* x_43; 
x_43 = l_lean_parser_command_export_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
return x_43;
}
else
{
obj* x_45; obj* x_48; 
x_45 = lean::cnstr_get(x_24, 0);
lean::inc(x_45);
lean::dec(x_24);
x_48 = lean::box(0);
x_3 = x_48;
x_4 = x_45;
goto lbl_5;
}
}
}
}
}
lbl_2:
{
obj* x_49; obj* x_50; 
x_49 = lean::box(3);
x_50 = l_lean_parser_syntax_as__node___main(x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; 
x_51 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_1);
lean::cnstr_set(x_53, 1, x_51);
return x_53;
}
else
{
obj* x_54; obj* x_57; obj* x_60; obj* x_62; obj* x_63; 
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
lean::dec(x_50);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
x_60 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_60);
x_62 = l_list_map___main___rarg(x_60, x_57);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_1);
lean::cnstr_set(x_63, 1, x_62);
return x_63;
}
}
lbl_5:
{
obj* x_64; 
x_64 = l_lean_parser_syntax_as__node___main(x_4);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_67; 
x_65 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__1;
lean::inc(x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_3);
lean::cnstr_set(x_67, 1, x_65);
return x_67;
}
else
{
obj* x_68; obj* x_71; obj* x_74; obj* x_76; obj* x_77; 
x_68 = lean::cnstr_get(x_64, 0);
lean::inc(x_68);
lean::dec(x_64);
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
x_74 = l_lean_parser_command_open_has__view_x_27___lambda__1___closed__2;
lean::inc(x_74);
x_76 = l_list_map___main___rarg(x_74, x_71);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_3);
lean::cnstr_set(x_77, 1, x_76);
return x_77;
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; 
x_21 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_26 = x_20;
} else {
 lean::dec(x_20);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_26);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
else
{
obj* x_33; obj* x_35; 
x_33 = lean::cnstr_get(x_27, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_27, 1);
lean::inc(x_35);
lean::dec(x_27);
if (lean::obj_tag(x_35) == 0)
{
switch (lean::obj_tag(x_33)) {
case 1:
{
obj* x_38; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_33, 0);
lean::inc(x_38);
lean::dec(x_33);
if (lean::is_scalar(x_26)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_26;
}
lean::cnstr_set(x_41, 0, x_38);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_5);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
case 3:
{
obj* x_44; obj* x_46; 
lean::dec(x_26);
x_44 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_44);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_5);
lean::cnstr_set(x_46, 1, x_44);
return x_46;
}
default:
{
obj* x_49; obj* x_51; 
lean::dec(x_33);
lean::dec(x_26);
x_49 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_5);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
obj* x_55; obj* x_57; 
lean::dec(x_33);
lean::dec(x_35);
lean::dec(x_26);
x_55 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_5);
lean::cnstr_set(x_57, 1, x_55);
return x_57;
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
obj* x_5; 
x_5 = l_lean_parser_command_section_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_19 = x_24;
goto lbl_20;
}
case 3:
{
obj* x_25; 
x_25 = lean::box(0);
x_19 = x_25;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
{
obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
lean::dec(x_1);
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_34; 
x_34 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_37; 
x_35 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_19);
lean::cnstr_set(x_37, 1, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_41; 
x_38 = lean::cnstr_get(x_34, 0);
lean::inc(x_38);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 x_40 = x_34;
} else {
 lean::dec(x_34);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_40);
x_45 = lean::box(0);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_19);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
else
{
obj* x_47; obj* x_49; 
x_47 = lean::cnstr_get(x_41, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_41, 1);
lean::inc(x_49);
lean::dec(x_41);
if (lean::obj_tag(x_49) == 0)
{
switch (lean::obj_tag(x_47)) {
case 1:
{
obj* x_52; obj* x_55; obj* x_56; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
lean::dec(x_47);
if (lean::is_scalar(x_40)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_40;
}
lean::cnstr_set(x_55, 0, x_52);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_19);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
case 3:
{
obj* x_58; obj* x_60; 
lean::dec(x_40);
x_58 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_19);
lean::cnstr_set(x_60, 1, x_58);
return x_60;
}
default:
{
obj* x_63; obj* x_65; 
lean::dec(x_40);
lean::dec(x_47);
x_63 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_19);
lean::cnstr_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
obj* x_69; obj* x_71; 
lean::dec(x_40);
lean::dec(x_47);
lean::dec(x_49);
x_69 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_19);
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
obj* x_11; obj* x_13; obj* x_14; obj* x_16; 
x_11 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_lean_parser_command_section;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; 
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
lean::dec(x_3);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_17);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = l_lean_parser_no__kind;
lean::inc(x_23);
x_25 = l_lean_parser_syntax_mk__node(x_23, x_22);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_20);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_10);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_lean_parser_command_section;
lean::inc(x_28);
x_30 = l_lean_parser_syntax_mk__node(x_28, x_27);
return x_30;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::mk_string("section");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_tokens___rarg(x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_4, x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_2, x_5);
x_7 = l_lean_parser_tokens___rarg(x_6);
return x_7;
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_14; obj* x_16; 
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
case 3:
{
obj* x_24; obj* x_26; 
x_24 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_24);
return x_26;
}
default:
{
obj* x_28; obj* x_30; 
lean::dec(x_17);
x_28 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
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
obj* x_5; 
x_5 = l_lean_parser_command_namespace_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_19 = x_24;
goto lbl_20;
}
case 3:
{
obj* x_25; 
x_25 = lean::box(0);
x_19 = x_25;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_28; obj* x_30; 
x_28 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_19);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
lean::dec(x_1);
switch (lean::obj_tag(x_31)) {
case 1:
{
obj* x_34; obj* x_37; 
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_19);
lean::cnstr_set(x_37, 1, x_34);
return x_37;
}
case 3:
{
obj* x_38; obj* x_40; 
x_38 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_19);
lean::cnstr_set(x_40, 1, x_38);
return x_40;
}
default:
{
obj* x_42; obj* x_44; 
lean::dec(x_31);
x_42 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_19);
lean::cnstr_set(x_44, 1, x_42);
return x_44;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::mk_string("namespace");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_3, x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_2, x_4);
x_6 = l_lean_parser_tokens___rarg(x_5);
return x_6;
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
obj* x_9; obj* x_11; 
x_9 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__1;
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
else
{
obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_lean_parser_term_binder_has__view;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::apply_1(x_16, x_12);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_8);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
case 3:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_20; 
x_20 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__2;
lean::inc(x_20);
return x_20;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_0, 0);
lean::inc(x_22);
lean::dec(x_0);
x_25 = lean::box(0);
x_26 = l_lean_parser_term_binder_has__view;
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::apply_1(x_27, x_22);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_25);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
default:
{
lean::dec(x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_32; 
x_32 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__2;
lean::inc(x_32);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_41; obj* x_42; 
x_34 = lean::cnstr_get(x_0, 0);
lean::inc(x_34);
lean::dec(x_0);
x_37 = lean::box(0);
x_38 = l_lean_parser_term_binder_has__view;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::apply_1(x_39, x_34);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
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
obj* x_5; 
x_5 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__3;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
if (lean::obj_tag(x_1) == 0)
{
obj* x_23; obj* x_25; 
x_23 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__1;
lean::inc(x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_23);
return x_25;
}
else
{
obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_33; 
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
lean::dec(x_1);
x_29 = l_lean_parser_term_binder_has__view;
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::apply_1(x_30, x_26);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_22);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
case 3:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_34; 
x_34 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__2;
lean::inc(x_34);
return x_34;
}
else
{
obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
lean::dec(x_1);
x_39 = lean::box(0);
x_40 = l_lean_parser_term_binder_has__view;
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::apply_1(x_41, x_36);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
default:
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_46; 
x_46 = l_lean_parser_command_variable_has__view_x_27___lambda__1___closed__2;
lean::inc(x_46);
return x_46;
}
else
{
obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
lean::dec(x_1);
x_51 = lean::box(0);
x_52 = l_lean_parser_term_binder_has__view;
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::apply_1(x_53, x_48);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_51);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
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
obj* x_9; obj* x_11; 
x_9 = l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__2;
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
else
{
obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_lean_parser_term_bracketed__binders_has__view;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::apply_1(x_16, x_12);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_8);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
case 3:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_20; 
x_20 = l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__1;
lean::inc(x_20);
return x_20;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_0, 0);
lean::inc(x_22);
lean::dec(x_0);
x_25 = lean::box(0);
x_26 = l_lean_parser_term_bracketed__binders_has__view;
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::apply_1(x_27, x_22);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_25);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
default:
{
lean::dec(x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_32; 
x_32 = l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__1;
lean::inc(x_32);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_41; obj* x_42; 
x_34 = lean::cnstr_get(x_0, 0);
lean::inc(x_34);
lean::dec(x_0);
x_37 = lean::box(0);
x_38 = l_lean_parser_term_bracketed__binders_has__view;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::apply_1(x_39, x_34);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
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
obj* x_5; 
x_5 = l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__2;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
if (lean::obj_tag(x_1) == 0)
{
obj* x_23; obj* x_25; 
x_23 = l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__2;
lean::inc(x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_23);
return x_25;
}
else
{
obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_33; 
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
lean::dec(x_1);
x_29 = l_lean_parser_term_bracketed__binders_has__view;
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::apply_1(x_30, x_26);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_22);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
case 3:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_34; 
x_34 = l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__1;
lean::inc(x_34);
return x_34;
}
else
{
obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
lean::dec(x_1);
x_39 = lean::box(0);
x_40 = l_lean_parser_term_bracketed__binders_has__view;
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::apply_1(x_41, x_36);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
default:
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_46; 
x_46 = l_lean_parser_command_variables_has__view_x_27___lambda__1___closed__1;
lean::inc(x_46);
return x_46;
}
else
{
obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
lean::dec(x_1);
x_51 = lean::box(0);
x_52 = l_lean_parser_term_bracketed__binders_has__view;
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::apply_1(x_53, x_48);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_51);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
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
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__1(x_4);
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
obj* x_12; obj* x_14; 
x_12 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_12);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
default:
{
obj* x_16; obj* x_18; 
lean::dec(x_2);
x_16 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_16);
if (lean::is_scalar(x_6)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_6;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
x_8 = l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__2(x_4);
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; 
x_21 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_30; obj* x_31; 
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__1(x_27);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
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
obj* x_5; 
x_5 = l_lean_parser_command_include_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_19 = x_24;
goto lbl_20;
}
case 3:
{
obj* x_25; 
x_25 = lean::box(0);
x_19 = x_25;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
{
obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
lean::dec(x_1);
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_34; 
x_34 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_37; 
x_35 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_19);
lean::cnstr_set(x_37, 1, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_41; obj* x_44; obj* x_45; 
x_38 = lean::cnstr_get(x_34, 0);
lean::inc(x_38);
lean::dec(x_34);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_44 = l_list_map___main___at_lean_parser_command_include_has__view_x_27___spec__1(x_41);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_19);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::mk_string("include ");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_tokens___rarg(x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_4, x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_2, x_5);
x_7 = l_lean_parser_tokens___rarg(x_6);
return x_7;
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
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__1(x_4);
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
obj* x_12; obj* x_14; 
x_12 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_12);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
default:
{
obj* x_16; obj* x_18; 
lean::dec(x_2);
x_16 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_16);
if (lean::is_scalar(x_6)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_6;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
x_8 = l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__2(x_4);
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; 
x_21 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_30; obj* x_31; 
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__1(x_27);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
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
obj* x_5; 
x_5 = l_lean_parser_command_omit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_19 = x_24;
goto lbl_20;
}
case 3:
{
obj* x_25; 
x_25 = lean::box(0);
x_19 = x_25;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
{
obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
lean::dec(x_1);
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_34; 
x_34 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_37; 
x_35 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_19);
lean::cnstr_set(x_37, 1, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_41; obj* x_44; obj* x_45; 
x_38 = lean::cnstr_get(x_34, 0);
lean::inc(x_38);
lean::dec(x_34);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_44 = l_list_map___main___at_lean_parser_command_omit_has__view_x_27___spec__1(x_41);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_19);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::mk_string("omit ");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_tokens___rarg(x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_4, x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_2, x_5);
x_7 = l_lean_parser_tokens___rarg(x_6);
return x_7;
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; 
x_21 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_26 = x_20;
} else {
 lean::dec(x_20);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_26);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
else
{
obj* x_33; obj* x_35; 
x_33 = lean::cnstr_get(x_27, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_27, 1);
lean::inc(x_35);
lean::dec(x_27);
if (lean::obj_tag(x_35) == 0)
{
switch (lean::obj_tag(x_33)) {
case 1:
{
obj* x_38; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_33, 0);
lean::inc(x_38);
lean::dec(x_33);
if (lean::is_scalar(x_26)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_26;
}
lean::cnstr_set(x_41, 0, x_38);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_5);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
case 3:
{
obj* x_44; obj* x_46; 
lean::dec(x_26);
x_44 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_44);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_5);
lean::cnstr_set(x_46, 1, x_44);
return x_46;
}
default:
{
obj* x_49; obj* x_51; 
lean::dec(x_33);
lean::dec(x_26);
x_49 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_5);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
obj* x_55; obj* x_57; 
lean::dec(x_33);
lean::dec(x_35);
lean::dec(x_26);
x_55 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_5);
lean::cnstr_set(x_57, 1, x_55);
return x_57;
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
obj* x_5; 
x_5 = l_lean_parser_command_end_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_19 = x_24;
goto lbl_20;
}
case 3:
{
obj* x_25; 
x_25 = lean::box(0);
x_19 = x_25;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
{
obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
lean::dec(x_1);
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_34; 
x_34 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_37; 
x_35 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_19);
lean::cnstr_set(x_37, 1, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_41; 
x_38 = lean::cnstr_get(x_34, 0);
lean::inc(x_38);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 x_40 = x_34;
} else {
 lean::dec(x_34);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_40);
x_45 = lean::box(0);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_19);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
else
{
obj* x_47; obj* x_49; 
x_47 = lean::cnstr_get(x_41, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_41, 1);
lean::inc(x_49);
lean::dec(x_41);
if (lean::obj_tag(x_49) == 0)
{
switch (lean::obj_tag(x_47)) {
case 1:
{
obj* x_52; obj* x_55; obj* x_56; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
lean::dec(x_47);
if (lean::is_scalar(x_40)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_40;
}
lean::cnstr_set(x_55, 0, x_52);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_19);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
case 3:
{
obj* x_58; obj* x_60; 
lean::dec(x_40);
x_58 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_19);
lean::cnstr_set(x_60, 1, x_58);
return x_60;
}
default:
{
obj* x_63; obj* x_65; 
lean::dec(x_40);
lean::dec(x_47);
x_63 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__4;
lean::inc(x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_19);
lean::cnstr_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
obj* x_69; obj* x_71; 
lean::dec(x_40);
lean::dec(x_47);
lean::dec(x_49);
x_69 = l_lean_parser_command_notation__spec_has__view_x_27___lambda__1___closed__6;
lean::inc(x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_19);
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
obj* x_11; obj* x_13; obj* x_14; obj* x_16; 
x_11 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_lean_parser_command_end;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; 
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
lean::dec(x_3);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_17);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = l_lean_parser_no__kind;
lean::inc(x_23);
x_25 = l_lean_parser_syntax_mk__node(x_23, x_22);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_20);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_10);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_lean_parser_command_end;
lean::inc(x_28);
x_30 = l_lean_parser_syntax_mk__node(x_28, x_27);
return x_30;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::mk_string("end");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_tokens___rarg(x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_4, x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_2, x_5);
x_7 = l_lean_parser_tokens___rarg(x_6);
return x_7;
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
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__1(x_4);
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
obj* x_12; obj* x_14; 
x_12 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_12);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
default:
{
obj* x_16; obj* x_18; 
lean::dec(x_2);
x_16 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_16);
if (lean::is_scalar(x_6)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_6;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
x_8 = l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__2(x_4);
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_14; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_14 = x_17;
goto lbl_15;
}
lbl_15:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; 
x_21 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_30; obj* x_31; 
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__1(x_27);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
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
obj* x_5; 
x_5 = l_lean_parser_command_universes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_19 = x_24;
goto lbl_20;
}
case 3:
{
obj* x_25; 
x_25 = lean::box(0);
x_19 = x_25;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
{
obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
lean::dec(x_1);
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_34; 
x_34 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_37; 
x_35 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_19);
lean::cnstr_set(x_37, 1, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_41; obj* x_44; obj* x_45; 
x_38 = lean::cnstr_get(x_34, 0);
lean::inc(x_38);
lean::dec(x_34);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_44 = l_list_map___main___at_lean_parser_command_universes_has__view_x_27___spec__1(x_41);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_19);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_14; obj* x_16; 
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
case 3:
{
obj* x_24; obj* x_26; 
x_24 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_24);
return x_26;
}
default:
{
obj* x_28; obj* x_30; 
lean::dec(x_17);
x_28 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
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
obj* x_5; 
x_5 = l_lean_parser_command_universe_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_19 = x_24;
goto lbl_20;
}
case 3:
{
obj* x_25; 
x_25 = lean::box(0);
x_19 = x_25;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_28; obj* x_30; 
x_28 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_19);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
lean::dec(x_1);
switch (lean::obj_tag(x_31)) {
case 1:
{
obj* x_34; obj* x_37; 
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_19);
lean::cnstr_set(x_37, 1, x_34);
return x_37;
}
case 3:
{
obj* x_38; obj* x_40; 
x_38 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_19);
lean::cnstr_set(x_40, 1, x_38);
return x_40;
}
default:
{
obj* x_42; obj* x_44; 
lean::dec(x_31);
x_42 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_19);
lean::cnstr_set(x_44, 1, x_42);
return x_44;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::mk_string("universes");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_tokens___rarg(x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_4, x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_2, x_5);
x_7 = l_lean_parser_tokens___rarg(x_6);
x_8 = lean::mk_string("universe");
x_9 = l_lean_parser_symbol_tokens___rarg(x_8, x_1);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_3, x_3);
x_11 = l_lean_parser_list_cons_tokens___rarg(x_9, x_10);
x_12 = l_lean_parser_tokens___rarg(x_11);
x_13 = l_lean_parser_list_cons_tokens___rarg(x_12, x_3);
x_14 = l_lean_parser_list_cons_tokens___rarg(x_7, x_13);
x_15 = l_lean_parser_tokens___rarg(x_14);
return x_15;
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
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_14 = x_9;
} else {
 lean::dec(x_9);
 x_14 = lean::box(0);
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
obj* x_6; 
x_6 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_orelse___at_lean_parser_command_universe_parser___spec__2___rarg), 6, 2);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_7);
x_0 = x_12;
x_1 = x_9;
goto _start;
}
}
}
obj* l_lean_parser_combinators_any__of___at_lean_parser_command_universe_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_10; 
x_5 = lean::box(0);
x_6 = l_lean_parser_combinators_any__of___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_6);
x_10 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__4___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3, x_4);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_16; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_list_foldl___main___at_lean_parser_command_universe_parser___spec__3(x_11, x_13, x_1, x_2, x_3, x_4);
return x_16;
}
}
}
obj* _init_l_lean_parser_command_universe_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_0 = lean::mk_string("universes");
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
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__3), 5, 1);
lean::closure_set(x_8, 0, x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_lean_parser_command_universes;
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_11);
x_15 = lean::mk_string("universe");
x_16 = l_string_trim(x_15);
lean::inc(x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_18, 0, x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_19, 0, x_16);
lean::closure_set(x_19, 1, x_4);
lean::closure_set(x_19, 2, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_6);
lean::cnstr_set(x_20, 1, x_9);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_lean_parser_command_universe;
lean::inc(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_24, 0, x_22);
lean::closure_set(x_24, 1, x_21);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_9);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_14);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
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
obj* x_2; 
x_2 = l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
} else {
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; 
x_11 = l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1;
lean::inc(x_11);
return x_11;
}
else
{
obj* x_13; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_13);
return x_17;
}
}
else
{
obj* x_18; obj* x_20; 
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_7, 1);
lean::inc(x_20);
lean::dec(x_7);
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_23; obj* x_26; 
x_23 = lean::cnstr_get(x_18, 0);
lean::inc(x_23);
lean::dec(x_18);
if (lean::is_scalar(x_6)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_6;
}
lean::cnstr_set(x_26, 0, x_23);
if (lean::obj_tag(x_20) == 0)
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
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_26);
lean::cnstr_set(x_32, 1, x_29);
return x_32;
}
}
case 3:
{
lean::dec(x_6);
if (lean::obj_tag(x_20) == 0)
{
obj* x_34; 
x_34 = l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1;
lean::inc(x_34);
return x_34;
}
else
{
obj* x_36; obj* x_39; obj* x_40; 
x_36 = lean::cnstr_get(x_20, 0);
lean::inc(x_36);
lean::dec(x_20);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_36);
return x_40;
}
}
default:
{
lean::dec(x_6);
lean::dec(x_18);
if (lean::obj_tag(x_20) == 0)
{
obj* x_43; 
x_43 = l_lean_parser_command_check_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
return x_43;
}
else
{
obj* x_45; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_20, 0);
lean::inc(x_45);
lean::dec(x_20);
x_48 = lean::box(0);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
return x_49;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_23; 
x_0 = lean::mk_string("#check");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_6, 0, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_lean_parser_command__parser__m_monad___closed__1;
x_12 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_13 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_14 = l_lean_parser_command__parser__m_alternative___closed__1;
x_15 = l_lean_parser_command_check;
x_16 = l_lean_parser_command_check_has__view;
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
x_23 = l_lean_parser_combinators_node_view___rarg(x_11, x_12, x_13, x_14, x_15, x_10, x_16);
return x_23;
}
}
obj* _init_l_lean_parser_command_check_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("#check");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_6, 0, x_4);
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
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__1(x_4);
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
obj* x_12; obj* x_14; 
x_12 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_12);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
default:
{
obj* x_16; obj* x_18; 
lean::dec(x_2);
x_16 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_16);
if (lean::is_scalar(x_6)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_6;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
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
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = l_lean_parser_command_attr__instance_has__view;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::apply_1(x_8, x_2);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_23; 
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::dec(x_4);
x_19 = l_lean_parser_command_attr__instance_has__view;
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::apply_1(x_20, x_2);
x_23 = l___private_init_lean_parser_combinators_3__sep__by_view__aux___main___at_lean_parser_command_attribute_has__view_x_27___spec__2(x_16);
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_24; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_14, 0);
lean::inc(x_24);
lean::dec(x_14);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_22);
lean::cnstr_set(x_29, 1, x_28);
if (lean::is_scalar(x_6)) {
 x_30 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_30 = x_6;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_23);
return x_30;
}
case 3:
{
obj* x_31; obj* x_33; obj* x_34; 
x_31 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_31);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_22);
lean::cnstr_set(x_33, 1, x_31);
if (lean::is_scalar(x_6)) {
 x_34 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_34 = x_6;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_23);
return x_34;
}
default:
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_14);
x_36 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_22);
lean::cnstr_set(x_38, 1, x_36);
if (lean::is_scalar(x_6)) {
 x_39 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_39 = x_6;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_23);
return x_39;
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
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
x_12 = lean::box(0);
x_13 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__3(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
x_14 = l_lean_parser_command_attr__instance_has__view;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::apply_1(x_15, x_7);
if (lean::is_scalar(x_6)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_6;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_12);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_13);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_20 = lean::cnstr_get(x_9, 0);
lean::inc(x_20);
lean::dec(x_9);
x_23 = l_lean_parser_command_attr__instance_has__view;
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
x_26 = lean::apply_1(x_24, x_7);
x_27 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_27);
x_29 = l_option_map___rarg(x_27, x_20);
x_30 = lean::box(3);
x_31 = l_option_get__or__else___main___rarg(x_29, x_30);
if (lean::is_scalar(x_6)) {
 x_32 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_32 = x_6;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_12);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_26);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_13);
return x_34;
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__4(obj* x_0) {
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
x_8 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__4(x_4);
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
obj* x_8; 
x_8 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_8);
x_5 = x_8;
goto lbl_6;
}
else
{
obj* x_10; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_12 = x_7;
} else {
 lean::dec(x_7);
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
x_5 = x_17;
goto lbl_6;
}
else
{
obj* x_18; obj* x_20; 
x_18 = lean::cnstr_get(x_13, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_13, 1);
lean::inc(x_20);
lean::dec(x_13);
if (lean::obj_tag(x_20) == 0)
{
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_18, 0);
lean::inc(x_23);
lean::dec(x_18);
if (lean::is_scalar(x_12)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_12;
}
lean::cnstr_set(x_26, 0, x_23);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_5 = x_27;
goto lbl_6;
}
case 3:
{
obj* x_29; 
lean::dec(x_12);
x_29 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_29);
x_5 = x_29;
goto lbl_6;
}
default:
{
obj* x_33; 
lean::dec(x_18);
lean::dec(x_12);
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
lean::dec(x_18);
lean::dec(x_20);
lean::dec(x_12);
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
case 3:
{
obj* x_55; 
x_55 = lean::box(0);
x_49 = x_55;
goto lbl_50;
}
default:
{
obj* x_57; 
lean::dec(x_41);
x_57 = lean::box(0);
x_49 = x_57;
goto lbl_50;
}
}
lbl_50:
{
obj* x_58; obj* x_59; 
if (lean::obj_tag(x_40) == 0)
{
obj* x_61; 
x_61 = lean::box(3);
x_58 = x_40;
x_59 = x_61;
goto lbl_60;
}
else
{
obj* x_62; obj* x_64; 
x_62 = lean::cnstr_get(x_40, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_40, 1);
lean::inc(x_64);
lean::dec(x_40);
x_58 = x_64;
x_59 = x_62;
goto lbl_60;
}
lbl_60:
{
obj* x_67; 
switch (lean::obj_tag(x_59)) {
case 0:
{
obj* x_69; obj* x_72; 
x_69 = lean::cnstr_get(x_59, 0);
lean::inc(x_69);
lean::dec(x_59);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_69);
x_67 = x_72;
goto lbl_68;
}
case 3:
{
obj* x_73; 
x_73 = lean::box(0);
x_67 = x_73;
goto lbl_68;
}
default:
{
obj* x_75; 
lean::dec(x_59);
x_75 = lean::box(0);
x_67 = x_75;
goto lbl_68;
}
}
lbl_68:
{
obj* x_76; obj* x_77; 
if (lean::obj_tag(x_58) == 0)
{
obj* x_79; 
x_79 = lean::box(3);
x_76 = x_58;
x_77 = x_79;
goto lbl_78;
}
else
{
obj* x_80; obj* x_82; 
x_80 = lean::cnstr_get(x_58, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_58, 1);
lean::inc(x_82);
lean::dec(x_58);
x_76 = x_82;
x_77 = x_80;
goto lbl_78;
}
lbl_78:
{
obj* x_85; obj* x_87; 
x_87 = l_lean_parser_syntax_as__node___main(x_77);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; 
x_88 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_88);
x_85 = x_88;
goto lbl_86;
}
else
{
obj* x_90; obj* x_93; obj* x_96; 
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
lean::dec(x_87);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l___private_init_lean_parser_combinators_3__sep__by_view__aux___main___at_lean_parser_command_attribute_has__view_x_27___spec__2(x_93);
x_85 = x_96;
goto lbl_86;
}
lbl_86:
{
obj* x_97; obj* x_98; 
if (lean::obj_tag(x_76) == 0)
{
obj* x_100; 
x_100 = lean::box(3);
x_97 = x_76;
x_98 = x_100;
goto lbl_99;
}
else
{
obj* x_101; obj* x_103; 
x_101 = lean::cnstr_get(x_76, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_76, 1);
lean::inc(x_103);
lean::dec(x_76);
x_97 = x_103;
x_98 = x_101;
goto lbl_99;
}
lbl_99:
{
obj* x_106; 
switch (lean::obj_tag(x_98)) {
case 0:
{
obj* x_108; obj* x_111; 
x_108 = lean::cnstr_get(x_98, 0);
lean::inc(x_108);
lean::dec(x_98);
x_111 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_111, 0, x_108);
x_106 = x_111;
goto lbl_107;
}
case 3:
{
obj* x_112; 
x_112 = lean::box(0);
x_106 = x_112;
goto lbl_107;
}
default:
{
obj* x_114; 
lean::dec(x_98);
x_114 = lean::box(0);
x_106 = x_114;
goto lbl_107;
}
}
lbl_107:
{
obj* x_115; 
if (lean::obj_tag(x_97) == 0)
{
obj* x_117; 
x_117 = lean::box(3);
x_115 = x_117;
goto lbl_116;
}
else
{
obj* x_118; 
x_118 = lean::cnstr_get(x_97, 0);
lean::inc(x_118);
lean::dec(x_97);
x_115 = x_118;
goto lbl_116;
}
lbl_116:
{
obj* x_121; 
x_121 = l_lean_parser_syntax_as__node___main(x_115);
if (lean::obj_tag(x_121) == 0)
{
obj* x_122; obj* x_124; 
x_122 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_122);
x_124 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_124, 0, x_5);
lean::cnstr_set(x_124, 1, x_49);
lean::cnstr_set(x_124, 2, x_67);
lean::cnstr_set(x_124, 3, x_85);
lean::cnstr_set(x_124, 4, x_106);
lean::cnstr_set(x_124, 5, x_122);
return x_124;
}
else
{
obj* x_125; obj* x_128; obj* x_131; obj* x_132; 
x_125 = lean::cnstr_get(x_121, 0);
lean::inc(x_125);
lean::dec(x_121);
x_128 = lean::cnstr_get(x_125, 1);
lean::inc(x_128);
lean::dec(x_125);
x_131 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__1(x_128);
x_132 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_132, 0, x_5);
lean::cnstr_set(x_132, 1, x_49);
lean::cnstr_set(x_132, 2, x_67);
lean::cnstr_set(x_132, 3, x_85);
lean::cnstr_set(x_132, 4, x_106);
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
obj* x_5; 
x_5 = l_lean_parser_command_attribute_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
else
{
obj* x_19; obj* x_21; obj* x_24; 
x_19 = lean::cnstr_get(x_10, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_10, 1);
lean::inc(x_21);
lean::dec(x_10);
x_24 = l_lean_parser_syntax_as__node___main(x_19);
if (lean::obj_tag(x_24) == 0)
{
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; 
x_25 = lean::box(3);
x_1 = x_21;
x_2 = x_25;
goto lbl_3;
}
else
{
obj* x_26; obj* x_28; 
x_26 = lean::cnstr_get(x_21, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_21, 1);
lean::inc(x_28);
lean::dec(x_21);
x_1 = x_28;
x_2 = x_26;
goto lbl_3;
}
}
else
{
obj* x_31; obj* x_34; obj* x_37; 
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = l_list_append___rarg(x_34, x_21);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::box(3);
x_1 = x_37;
x_2 = x_38;
goto lbl_3;
}
else
{
obj* x_39; obj* x_41; 
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_37, 1);
lean::inc(x_41);
lean::dec(x_37);
x_1 = x_41;
x_2 = x_39;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_44; obj* x_46; 
x_46 = l_lean_parser_syntax_as__node___main(x_2);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; 
x_47 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_47);
x_44 = x_47;
goto lbl_45;
}
else
{
obj* x_49; obj* x_51; obj* x_52; 
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_51 = x_46;
} else {
 lean::dec(x_46);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
if (lean::obj_tag(x_52) == 0)
{
obj* x_56; 
lean::dec(x_51);
x_56 = lean::box(0);
x_44 = x_56;
goto lbl_45;
}
else
{
obj* x_57; obj* x_59; 
x_57 = lean::cnstr_get(x_52, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_52, 1);
lean::inc(x_59);
lean::dec(x_52);
if (lean::obj_tag(x_59) == 0)
{
switch (lean::obj_tag(x_57)) {
case 0:
{
obj* x_62; obj* x_65; obj* x_66; 
x_62 = lean::cnstr_get(x_57, 0);
lean::inc(x_62);
lean::dec(x_57);
if (lean::is_scalar(x_51)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_51;
}
lean::cnstr_set(x_65, 0, x_62);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_44 = x_66;
goto lbl_45;
}
case 3:
{
obj* x_68; 
lean::dec(x_51);
x_68 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_68);
x_44 = x_68;
goto lbl_45;
}
default:
{
obj* x_72; 
lean::dec(x_51);
lean::dec(x_57);
x_72 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_72);
x_44 = x_72;
goto lbl_45;
}
}
}
else
{
obj* x_77; 
lean::dec(x_51);
lean::dec(x_59);
lean::dec(x_57);
x_77 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
x_44 = x_77;
goto lbl_45;
}
}
}
lbl_45:
{
obj* x_79; obj* x_80; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_82; 
x_82 = lean::box(3);
x_79 = x_1;
x_80 = x_82;
goto lbl_81;
}
else
{
obj* x_83; obj* x_85; 
x_83 = lean::cnstr_get(x_1, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_1, 1);
lean::inc(x_85);
lean::dec(x_1);
x_79 = x_85;
x_80 = x_83;
goto lbl_81;
}
lbl_81:
{
obj* x_88; 
switch (lean::obj_tag(x_80)) {
case 0:
{
obj* x_90; obj* x_93; 
x_90 = lean::cnstr_get(x_80, 0);
lean::inc(x_90);
lean::dec(x_80);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_90);
x_88 = x_93;
goto lbl_89;
}
case 3:
{
obj* x_94; 
x_94 = lean::box(0);
x_88 = x_94;
goto lbl_89;
}
default:
{
obj* x_96; 
lean::dec(x_80);
x_96 = lean::box(0);
x_88 = x_96;
goto lbl_89;
}
}
lbl_89:
{
obj* x_97; obj* x_98; 
if (lean::obj_tag(x_79) == 0)
{
obj* x_100; 
x_100 = lean::box(3);
x_97 = x_79;
x_98 = x_100;
goto lbl_99;
}
else
{
obj* x_101; obj* x_103; 
x_101 = lean::cnstr_get(x_79, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_79, 1);
lean::inc(x_103);
lean::dec(x_79);
x_97 = x_103;
x_98 = x_101;
goto lbl_99;
}
lbl_99:
{
obj* x_106; 
switch (lean::obj_tag(x_98)) {
case 0:
{
obj* x_108; obj* x_111; 
x_108 = lean::cnstr_get(x_98, 0);
lean::inc(x_108);
lean::dec(x_98);
x_111 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_111, 0, x_108);
x_106 = x_111;
goto lbl_107;
}
case 3:
{
obj* x_112; 
x_112 = lean::box(0);
x_106 = x_112;
goto lbl_107;
}
default:
{
obj* x_114; 
lean::dec(x_98);
x_114 = lean::box(0);
x_106 = x_114;
goto lbl_107;
}
}
lbl_107:
{
obj* x_115; obj* x_116; 
if (lean::obj_tag(x_97) == 0)
{
obj* x_118; 
x_118 = lean::box(3);
x_115 = x_97;
x_116 = x_118;
goto lbl_117;
}
else
{
obj* x_119; obj* x_121; 
x_119 = lean::cnstr_get(x_97, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_97, 1);
lean::inc(x_121);
lean::dec(x_97);
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
obj* x_127; 
x_127 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_127);
x_124 = x_127;
goto lbl_125;
}
else
{
obj* x_129; obj* x_132; obj* x_135; 
x_129 = lean::cnstr_get(x_126, 0);
lean::inc(x_129);
lean::dec(x_126);
x_132 = lean::cnstr_get(x_129, 1);
lean::inc(x_132);
lean::dec(x_129);
x_135 = l___private_init_lean_parser_combinators_3__sep__by_view__aux___main___at_lean_parser_command_attribute_has__view_x_27___spec__2(x_132);
x_124 = x_135;
goto lbl_125;
}
lbl_125:
{
obj* x_136; obj* x_137; 
if (lean::obj_tag(x_115) == 0)
{
obj* x_139; 
x_139 = lean::box(3);
x_136 = x_115;
x_137 = x_139;
goto lbl_138;
}
else
{
obj* x_140; obj* x_142; 
x_140 = lean::cnstr_get(x_115, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_115, 1);
lean::inc(x_142);
lean::dec(x_115);
x_136 = x_142;
x_137 = x_140;
goto lbl_138;
}
lbl_138:
{
obj* x_145; 
switch (lean::obj_tag(x_137)) {
case 0:
{
obj* x_147; obj* x_150; 
x_147 = lean::cnstr_get(x_137, 0);
lean::inc(x_147);
lean::dec(x_137);
x_150 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_150, 0, x_147);
x_145 = x_150;
goto lbl_146;
}
case 3:
{
obj* x_151; 
x_151 = lean::box(0);
x_145 = x_151;
goto lbl_146;
}
default:
{
obj* x_153; 
lean::dec(x_137);
x_153 = lean::box(0);
x_145 = x_153;
goto lbl_146;
}
}
lbl_146:
{
obj* x_154; 
if (lean::obj_tag(x_136) == 0)
{
obj* x_156; 
x_156 = lean::box(3);
x_154 = x_156;
goto lbl_155;
}
else
{
obj* x_157; 
x_157 = lean::cnstr_get(x_136, 0);
lean::inc(x_157);
lean::dec(x_136);
x_154 = x_157;
goto lbl_155;
}
lbl_155:
{
obj* x_160; 
x_160 = l_lean_parser_syntax_as__node___main(x_154);
if (lean::obj_tag(x_160) == 0)
{
obj* x_161; obj* x_163; 
x_161 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_161);
x_163 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_163, 0, x_44);
lean::cnstr_set(x_163, 1, x_88);
lean::cnstr_set(x_163, 2, x_106);
lean::cnstr_set(x_163, 3, x_124);
lean::cnstr_set(x_163, 4, x_145);
lean::cnstr_set(x_163, 5, x_161);
return x_163;
}
else
{
obj* x_164; obj* x_167; obj* x_170; obj* x_171; 
x_164 = lean::cnstr_get(x_160, 0);
lean::inc(x_164);
lean::dec(x_160);
x_167 = lean::cnstr_get(x_164, 1);
lean::inc(x_167);
lean::dec(x_164);
x_170 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__1(x_167);
x_171 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_171, 0, x_44);
lean::cnstr_set(x_171, 1, x_88);
lean::cnstr_set(x_171, 2, x_106);
lean::cnstr_set(x_171, 3, x_124);
lean::cnstr_set(x_171, 4, x_145);
lean::cnstr_set(x_171, 5, x_170);
return x_171;
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
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
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
x_18 = l_option_get__or__else___main___rarg(x_16, x_17);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
lean::inc(x_14);
x_22 = l_option_map___rarg(x_14, x_5);
x_23 = l_option_get__or__else___main___rarg(x_22, x_17);
x_24 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__3(x_7);
x_25 = l_list_join___main___rarg(x_24);
x_26 = l_lean_parser_no__kind;
lean::inc(x_26);
x_28 = l_lean_parser_syntax_mk__node(x_26, x_25);
lean::inc(x_14);
x_30 = l_option_map___rarg(x_14, x_9);
x_31 = l_option_get__or__else___main___rarg(x_30, x_17);
x_32 = l_list_map___main___at_lean_parser_command_attribute_has__view_x_27___spec__4(x_11);
lean::inc(x_26);
x_34 = l_lean_parser_syntax_mk__node(x_26, x_32);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_19);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_31);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_23);
lean::cnstr_set(x_38, 1, x_37);
if (lean::obj_tag(x_1) == 0)
{
obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; 
x_39 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_20);
lean::inc(x_26);
x_43 = l_lean_parser_syntax_mk__node(x_26, x_41);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_38);
x_45 = l_lean_parser_command_attribute;
lean::inc(x_45);
x_47 = l_lean_parser_syntax_mk__node(x_45, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_63; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
lean::dec(x_1);
lean::inc(x_14);
x_52 = l_option_map___rarg(x_14, x_48);
x_53 = l_option_get__or__else___main___rarg(x_52, x_17);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_19);
lean::inc(x_26);
x_56 = l_lean_parser_syntax_mk__node(x_26, x_54);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_20);
lean::inc(x_26);
x_59 = l_lean_parser_syntax_mk__node(x_26, x_57);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_38);
x_61 = l_lean_parser_command_attribute;
lean::inc(x_61);
x_63 = l_lean_parser_syntax_mk__node(x_61, x_60);
return x_63;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_0 = lean::mk_string("local ");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = l_lean_parser_tokens___rarg(x_2);
x_4 = lean::mk_string("attribute ");
x_5 = l_lean_parser_symbol_tokens___rarg(x_4, x_1);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_3, x_7);
x_9 = l_lean_parser_tokens___rarg(x_8);
x_10 = l_lean_parser_tokens___rarg(x_9);
x_11 = lean::mk_string("[");
x_12 = l_lean_parser_symbol_tokens___rarg(x_11, x_1);
x_13 = lean::mk_string(", ");
x_14 = l_lean_parser_symbol_tokens___rarg(x_13, x_1);
x_15 = l_lean_parser_command_attr__instance_parser_lean_parser_has__tokens;
lean::inc(x_15);
x_17 = l_lean_parser_combinators_sep__by1_tokens___rarg(x_15, x_14);
x_18 = lean::mk_string("] ");
x_19 = l_lean_parser_symbol_tokens___rarg(x_18, x_1);
x_20 = l_lean_parser_tokens___rarg(x_6);
x_21 = l_lean_parser_list_cons_tokens___rarg(x_20, x_6);
x_22 = l_lean_parser_list_cons_tokens___rarg(x_19, x_21);
x_23 = l_lean_parser_list_cons_tokens___rarg(x_17, x_22);
x_24 = l_lean_parser_list_cons_tokens___rarg(x_12, x_23);
x_25 = l_lean_parser_list_cons_tokens___rarg(x_10, x_24);
x_26 = l_lean_parser_tokens___rarg(x_25);
return x_26;
}
}
obj* _init_l_lean_parser_command_attribute_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_54; 
x_0 = lean::mk_string("local ");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::mk_string("attribute ");
x_8 = l_string_trim(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_4);
lean::closure_set(x_11, 2, x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::mk_string("[");
x_17 = l_string_trim(x_16);
lean::inc(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_17);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_20, 0, x_17);
lean::closure_set(x_20, 1, x_4);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::mk_string(", ");
x_22 = l_string_trim(x_21);
lean::inc(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_24, 0, x_22);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_25, 0, x_22);
lean::closure_set(x_25, 1, x_4);
lean::closure_set(x_25, 2, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attr__instance_parser), 4, 0);
x_27 = 1;
x_28 = lean::box(x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__tokens___spec__1___boxed), 7, 3);
lean::closure_set(x_29, 0, x_26);
lean::closure_set(x_29, 1, x_25);
lean::closure_set(x_29, 2, x_28);
x_30 = lean::mk_string("] ");
x_31 = l_string_trim(x_30);
lean::inc(x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_33, 0, x_31);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_34, 0, x_31);
lean::closure_set(x_34, 1, x_4);
lean::closure_set(x_34, 2, x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__2), 5, 1);
lean::closure_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_12);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_29);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_20);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_15);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_lean_parser_command__parser__m_monad___closed__1;
x_43 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_44 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_45 = l_lean_parser_command__parser__m_alternative___closed__1;
x_46 = l_lean_parser_command_attribute;
x_47 = l_lean_parser_command_attribute_has__view;
lean::inc(x_47);
lean::inc(x_46);
lean::inc(x_45);
lean::inc(x_44);
lean::inc(x_43);
lean::inc(x_42);
x_54 = l_lean_parser_combinators_node_view___rarg(x_42, x_43, x_44, x_45, x_46, x_41, x_47);
return x_54;
}
}
obj* _init_l_lean_parser_command_attribute_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_0 = lean::mk_string("local ");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::mk_string("attribute ");
x_8 = l_string_trim(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_4);
lean::closure_set(x_11, 2, x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::mk_string("[");
x_17 = l_string_trim(x_16);
lean::inc(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_17);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_20, 0, x_17);
lean::closure_set(x_20, 1, x_4);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::mk_string(", ");
x_22 = l_string_trim(x_21);
lean::inc(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_24, 0, x_22);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_25, 0, x_22);
lean::closure_set(x_25, 1, x_4);
lean::closure_set(x_25, 2, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attr__instance_parser), 4, 0);
x_27 = 1;
x_28 = lean::box(x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__tokens___spec__1___boxed), 7, 3);
lean::closure_set(x_29, 0, x_26);
lean::closure_set(x_29, 1, x_25);
lean::closure_set(x_29, 2, x_28);
x_30 = lean::mk_string("] ");
x_31 = l_string_trim(x_30);
lean::inc(x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_33, 0, x_31);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_34, 0, x_31);
lean::closure_set(x_34, 1, x_4);
lean::closure_set(x_34, 2, x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__tokens___spec__2), 5, 1);
lean::closure_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_12);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_29);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_20);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_15);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
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
lean::dec(x_1);
if (x_6 == 0)
{
obj* x_8; 
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_0);
return x_8;
}
else
{
obj* x_9; 
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_0);
return x_9;
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
obj* x_5; 
x_5 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_15 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__2;
x_16 = lean_name_dec_eq(x_10, x_15);
lean::dec(x_10);
if (x_16 == 0)
{
obj* x_19; 
lean::dec(x_12);
x_19 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_19);
return x_19;
}
else
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_21; 
x_21 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
return x_21;
}
else
{
obj* x_23; obj* x_25; 
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_12, 1);
lean::inc(x_25);
lean::dec(x_12);
if (lean::obj_tag(x_25) == 0)
{
obj* x_28; 
x_28 = l_lean_parser_syntax_as__node___main(x_23);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; 
x_29 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_29);
return x_29;
}
else
{
obj* x_31; obj* x_34; obj* x_36; 
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::dec(x_31);
switch (lean::obj_tag(x_34)) {
case 0:
{
obj* x_40; 
lean::dec(x_36);
x_40 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_40);
return x_40;
}
case 1:
{
obj* x_44; 
lean::dec(x_36);
lean::dec(x_34);
x_44 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_44);
return x_44;
}
default:
{
obj* x_46; obj* x_48; obj* x_51; uint8 x_52; 
x_46 = lean::cnstr_get(x_34, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_34, 1);
lean::inc(x_48);
lean::dec(x_34);
x_51 = lean::box(0);
x_52 = lean_name_dec_eq(x_46, x_51);
lean::dec(x_46);
if (x_52 == 0)
{
obj* x_56; 
lean::dec(x_36);
lean::dec(x_48);
x_56 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_56);
return x_56;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_59; 
lean::dec(x_48);
x_59 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_59);
return x_59;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_36, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_36, 1);
lean::inc(x_63);
lean::dec(x_36);
if (lean::obj_tag(x_63) == 0)
{
x_1 = x_61;
x_2 = x_48;
goto lbl_3;
}
else
{
obj* x_69; 
lean::dec(x_61);
lean::dec(x_63);
lean::dec(x_48);
x_69 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_69);
return x_69;
}
}
}
}
}
}
}
else
{
obj* x_73; 
lean::dec(x_23);
lean::dec(x_25);
x_73 = l_lean_parser_command_bool__option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_73);
return x_73;
}
}
}
}
lbl_3:
{
obj* x_75; uint8 x_76; 
x_75 = lean::mk_nat_obj(0u);
x_76 = lean::nat_dec_eq(x_2, x_75);
lean::dec(x_2);
if (x_76 == 0)
{
obj* x_78; 
x_78 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_78, 0, x_1);
return x_78;
}
else
{
obj* x_79; 
x_79 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_79, 0, x_1);
return x_79;
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
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_1);
x_6 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_6);
x_8 = l_lean_parser_syntax_mk__node(x_6, x_5);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_1);
x_10 = l_lean_parser_command_bool__option__value;
lean::inc(x_10);
x_12 = l_lean_parser_syntax_mk__node(x_10, x_9);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_1);
x_17 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_17);
x_19 = l_lean_parser_syntax_mk__node(x_17, x_16);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_1);
x_21 = l_lean_parser_command_bool__option__value;
lean::inc(x_21);
x_23 = l_lean_parser_syntax_mk__node(x_21, x_20);
return x_23;
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
if (x_6 == 0)
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_dec_eq(x_1, x_7);
lean::dec(x_1);
if (x_8 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = l_lean_parser_number_has__view;
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::apply_1(x_11, x_0);
x_14 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_15 = l_lean_parser_string__lit_has__view;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::apply_1(x_16, x_0);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
}
else
{
obj* x_21; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_1);
x_21 = l_lean_parser_command_bool__option__value_has__view;
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_0);
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
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
obj* x_5; 
x_5 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_15 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__2;
x_16 = lean_name_dec_eq(x_10, x_15);
lean::dec(x_10);
if (x_16 == 0)
{
obj* x_19; 
lean::dec(x_12);
x_19 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_19);
return x_19;
}
else
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_21; 
x_21 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
return x_21;
}
else
{
obj* x_23; obj* x_25; 
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_12, 1);
lean::inc(x_25);
lean::dec(x_12);
if (lean::obj_tag(x_25) == 0)
{
obj* x_28; 
x_28 = l_lean_parser_syntax_as__node___main(x_23);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; 
x_29 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_29);
return x_29;
}
else
{
obj* x_31; obj* x_34; obj* x_36; 
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::dec(x_31);
switch (lean::obj_tag(x_34)) {
case 0:
{
obj* x_40; 
lean::dec(x_36);
x_40 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_40);
return x_40;
}
case 1:
{
obj* x_44; 
lean::dec(x_36);
lean::dec(x_34);
x_44 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_44);
return x_44;
}
default:
{
obj* x_46; obj* x_48; obj* x_51; uint8 x_52; 
x_46 = lean::cnstr_get(x_34, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_34, 1);
lean::inc(x_48);
lean::dec(x_34);
x_51 = lean::box(0);
x_52 = lean_name_dec_eq(x_46, x_51);
lean::dec(x_46);
if (x_52 == 0)
{
obj* x_56; 
lean::dec(x_36);
lean::dec(x_48);
x_56 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_56);
return x_56;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_59; 
lean::dec(x_48);
x_59 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_59);
return x_59;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_36, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_36, 1);
lean::inc(x_63);
lean::dec(x_36);
if (lean::obj_tag(x_63) == 0)
{
x_1 = x_61;
x_2 = x_48;
goto lbl_3;
}
else
{
obj* x_69; 
lean::dec(x_61);
lean::dec(x_63);
lean::dec(x_48);
x_69 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_69);
return x_69;
}
}
}
}
}
}
}
else
{
obj* x_73; 
lean::dec(x_23);
lean::dec(x_25);
x_73 = l_lean_parser_command_option__value_has__view_x_27___lambda__1___closed__1;
lean::inc(x_73);
return x_73;
}
}
}
}
lbl_3:
{
obj* x_75; uint8 x_76; 
x_75 = lean::mk_nat_obj(0u);
x_76 = lean::nat_dec_eq(x_2, x_75);
if (x_76 == 0)
{
obj* x_77; uint8 x_78; 
x_77 = lean::mk_nat_obj(1u);
x_78 = lean::nat_dec_eq(x_2, x_77);
lean::dec(x_2);
if (x_78 == 0)
{
obj* x_80; obj* x_81; obj* x_83; obj* x_84; 
x_80 = l_lean_parser_number_has__view;
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_83 = lean::apply_1(x_81, x_1);
x_84 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
return x_84;
}
else
{
obj* x_85; obj* x_86; obj* x_88; obj* x_89; 
x_85 = l_lean_parser_string__lit_has__view;
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_88 = lean::apply_1(x_86, x_1);
x_89 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
return x_89;
}
}
else
{
obj* x_91; obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_2);
x_91 = l_lean_parser_command_bool__option__value_has__view;
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_94 = lean::apply_1(x_92, x_1);
x_95 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
return x_95;
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
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_command_bool__option__value_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_2);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_1);
x_10 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_10);
x_12 = l_lean_parser_syntax_mk__node(x_10, x_9);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_lean_parser_command_option__value;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
case 1:
{
obj* x_17; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_31; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_20 = l_lean_parser_string__lit_has__view;
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_23 = lean::apply_1(x_21, x_17);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_1);
x_29 = l_lean_parser_command_option__value;
lean::inc(x_29);
x_31 = l_lean_parser_syntax_mk__node(x_29, x_28);
return x_31;
}
default:
{
obj* x_32; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_46; 
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
lean::dec(x_0);
x_35 = l_lean_parser_number_has__view;
x_36 = lean::cnstr_get(x_35, 1);
lean::inc(x_36);
x_38 = lean::apply_1(x_36, x_32);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_1);
x_40 = l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
lean::inc(x_40);
x_42 = l_lean_parser_syntax_mk__node(x_40, x_39);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_1);
x_44 = l_lean_parser_command_option__value;
lean::inc(x_44);
x_46 = l_lean_parser_syntax_mk__node(x_44, x_43);
return x_46;
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_14; obj* x_15; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_17; 
x_17 = lean::box(3);
x_14 = x_0;
x_15 = x_17;
goto lbl_16;
}
else
{
obj* x_18; obj* x_20; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
lean::dec(x_0);
x_14 = x_20;
x_15 = x_18;
goto lbl_16;
}
lbl_16:
{
obj* x_23; 
switch (lean::obj_tag(x_15)) {
case 1:
{
obj* x_25; 
x_25 = lean::cnstr_get(x_15, 0);
lean::inc(x_25);
lean::dec(x_15);
if (lean::obj_tag(x_14) == 0)
{
obj* x_28; obj* x_30; 
x_28 = l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::cnstr_set(x_30, 1, x_25);
lean::cnstr_set(x_30, 2, x_28);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_35; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_14, 0);
lean::inc(x_31);
lean::dec(x_14);
x_34 = l_lean_parser_command_option__value_has__view;
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::apply_1(x_35, x_31);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_5);
lean::cnstr_set(x_38, 1, x_25);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
}
case 3:
{
obj* x_39; 
x_39 = lean::box(0);
x_23 = x_39;
goto lbl_24;
}
default:
{
obj* x_41; 
lean::dec(x_15);
x_41 = lean::box(0);
x_23 = x_41;
goto lbl_24;
}
}
lbl_24:
{
lean::dec(x_23);
if (lean::obj_tag(x_14) == 0)
{
obj* x_43; obj* x_44; obj* x_47; 
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
x_48 = lean::cnstr_get(x_14, 0);
lean::inc(x_48);
lean::dec(x_14);
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
obj* x_5; 
x_5 = l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__2;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_19 = x_24;
goto lbl_20;
}
case 3:
{
obj* x_25; 
x_25 = lean::box(0);
x_19 = x_25;
goto lbl_20;
}
default:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_19 = x_27;
goto lbl_20;
}
}
lbl_20:
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
obj* x_42; obj* x_44; 
x_42 = l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1;
lean::inc(x_42);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_19);
lean::cnstr_set(x_44, 1, x_39);
lean::cnstr_set(x_44, 2, x_42);
return x_44;
}
else
{
obj* x_45; obj* x_48; obj* x_49; obj* x_51; obj* x_52; 
x_45 = lean::cnstr_get(x_28, 0);
lean::inc(x_45);
lean::dec(x_28);
x_48 = l_lean_parser_command_option__value_has__view;
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::apply_1(x_49, x_45);
x_52 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_52, 0, x_19);
lean::cnstr_set(x_52, 1, x_39);
lean::cnstr_set(x_52, 2, x_51);
return x_52;
}
}
case 3:
{
obj* x_53; 
x_53 = lean::box(0);
x_37 = x_53;
goto lbl_38;
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
obj* x_57; obj* x_58; obj* x_61; 
x_57 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
x_58 = l_lean_parser_command_set__option_has__view_x_27___lambda__1___closed__1;
lean::inc(x_58);
lean::inc(x_57);
x_61 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_61, 0, x_19);
lean::cnstr_set(x_61, 1, x_57);
lean::cnstr_set(x_61, 2, x_58);
return x_61;
}
else
{
obj* x_62; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_71; 
x_62 = lean::cnstr_get(x_28, 0);
lean::inc(x_62);
lean::dec(x_28);
x_65 = l_lean_parser_command_option__value_has__view;
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
x_68 = lean::apply_1(x_66, x_62);
x_69 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_69);
x_71 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_71, 0, x_19);
lean::cnstr_set(x_71, 1, x_69);
lean::cnstr_set(x_71, 2, x_68);
return x_71;
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
} else {
 lean::dec(x_11);
 x_16 = lean::box(0);
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
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 lean::cnstr_release(x_12, 2);
 x_23 = x_12;
} else {
 lean::dec(x_12);
 x_23 = lean::box(0);
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
uint8 x_42; 
x_42 = 1;
x_40 = x_42;
goto lbl_41;
}
else
{
obj* x_43; uint8 x_46; 
x_43 = lean::cnstr_get(x_24, 0);
lean::inc(x_43);
lean::dec(x_24);
x_46 = lean::string_dec_eq(x_43, x_0);
lean::dec(x_43);
if (x_46 == 0)
{
uint8 x_48; 
x_48 = 1;
x_40 = x_48;
goto lbl_41;
}
else
{
uint8 x_49; 
x_49 = 0;
x_40 = x_49;
goto lbl_41;
}
}
lbl_41:
{
if (x_40 == 0)
{
obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
x_53 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_53);
if (lean::is_scalar(x_23)) {
 x_55 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_55 = x_23;
}
lean::cnstr_set(x_55, 0, x_17);
lean::cnstr_set(x_55, 1, x_19);
lean::cnstr_set(x_55, 2, x_53);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_55);
x_57 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_57);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_56);
x_60 = l_lean_parser_parsec__t_try__mk__res___rarg(x_59);
if (lean::is_scalar(x_16)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_16;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_14);
return x_61;
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_71; 
x_62 = l_string_quote(x_0);
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_63, 0, x_62);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_3);
x_65 = lean::box(0);
x_66 = l_string_join___closed__1;
lean::inc(x_66);
x_68 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_66, x_63, x_64, x_65, x_6, x_19, x_14);
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_74; obj* x_76; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_85; obj* x_86; obj* x_87; 
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_69, 2);
lean::inc(x_76);
lean::dec(x_69);
x_79 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_79);
if (lean::is_scalar(x_23)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_23;
}
lean::cnstr_set(x_81, 0, x_17);
lean::cnstr_set(x_81, 1, x_74);
lean::cnstr_set(x_81, 2, x_79);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_81);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_82);
lean::inc(x_79);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_83);
x_86 = l_lean_parser_parsec__t_try__mk__res___rarg(x_85);
if (lean::is_scalar(x_16)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_16;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_71);
return x_87;
}
else
{
obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_17);
lean::dec(x_23);
x_90 = lean::cnstr_get(x_69, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 x_93 = x_69;
} else {
 lean::dec(x_69);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_95);
x_97 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_97);
x_99 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_96);
x_100 = l_lean_parser_parsec__t_try__mk__res___rarg(x_99);
if (lean::is_scalar(x_16)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_16;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_71);
return x_101;
}
}
}
}
}
else
{
obj* x_105; uint8 x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
x_105 = lean::cnstr_get(x_12, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_108 = x_12;
} else {
 lean::dec(x_12);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_105);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_107);
x_110 = x_109;
x_111 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_111);
x_113 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_111, x_110);
x_114 = l_lean_parser_parsec__t_try__mk__res___rarg(x_113);
if (lean::is_scalar(x_16)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_16;
}
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_14);
return x_115;
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
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
} else {
 lean::dec(x_10);
 x_15 = lean::box(0);
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_22 = x_11;
} else {
 lean::dec(x_11);
 x_22 = lean::box(0);
}
lean::inc(x_16);
x_24 = l_lean_parser_try__view___at_lean_parser_string__lit_parser___spec__1(x_16);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; 
lean::dec(x_16);
lean::dec(x_22);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_2);
x_28 = lean::box(0);
x_29 = l_string_join___closed__1;
x_30 = l_lean_parser_string__lit_parser___at_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_29);
x_33 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_29, x_30, x_27, x_28, x_5, x_18, x_13);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_39);
x_41 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_34);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_41);
lean::inc(x_39);
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_42);
lean::inc(x_30);
x_46 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_44, x_30);
x_47 = l_lean_parser_parsec__t_try__mk__res___rarg(x_46);
if (lean::is_scalar(x_15)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_15;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_36);
return x_48;
}
else
{
obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_24);
x_52 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_52);
if (lean::is_scalar(x_22)) {
 x_54 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_54 = x_22;
}
lean::cnstr_set(x_54, 0, x_16);
lean::cnstr_set(x_54, 1, x_18);
lean::cnstr_set(x_54, 2, x_52);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_54);
x_56 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_56);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_55);
x_59 = l_lean_parser_string__lit_parser___at_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_59);
x_61 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_58, x_59);
x_62 = l_lean_parser_parsec__t_try__mk__res___rarg(x_61);
if (lean::is_scalar(x_15)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_15;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_13);
return x_63;
}
}
else
{
obj* x_66; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_5);
lean::dec(x_2);
x_66 = lean::cnstr_get(x_11, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_69 = x_11;
} else {
 lean::dec(x_11);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_66);
lean::cnstr_set_scalar(x_70, sizeof(void*)*1, x_68);
x_71 = x_70;
x_72 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_72);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_71);
x_75 = l_lean_parser_string__lit_parser___at_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_74, x_75);
x_78 = l_lean_parser_parsec__t_try__mk__res___rarg(x_77);
if (lean::is_scalar(x_15)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_15;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_13);
return x_79;
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
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
} else {
 lean::dec(x_10);
 x_15 = lean::box(0);
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_22 = x_11;
} else {
 lean::dec(x_11);
 x_22 = lean::box(0);
}
lean::inc(x_16);
x_24 = l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(x_16);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; 
lean::dec(x_16);
lean::dec(x_22);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_2);
x_28 = lean::box(0);
x_29 = l_string_join___closed__1;
x_30 = l_lean_parser_number_parser___at_lean_parser_command_notation__spec_precedence__lit_parser_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_29);
x_33 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_29, x_30, x_27, x_28, x_5, x_18, x_13);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_39);
x_41 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_34);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_41);
lean::inc(x_39);
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_42);
lean::inc(x_30);
x_46 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_44, x_30);
x_47 = l_lean_parser_parsec__t_try__mk__res___rarg(x_46);
if (lean::is_scalar(x_15)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_15;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_36);
return x_48;
}
else
{
obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_24);
x_52 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_52);
if (lean::is_scalar(x_22)) {
 x_54 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_54 = x_22;
}
lean::cnstr_set(x_54, 0, x_16);
lean::cnstr_set(x_54, 1, x_18);
lean::cnstr_set(x_54, 2, x_52);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_54);
x_56 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_56);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_55);
x_59 = l_lean_parser_number_parser___at_lean_parser_command_notation__spec_precedence__lit_parser_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_59);
x_61 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_58, x_59);
x_62 = l_lean_parser_parsec__t_try__mk__res___rarg(x_61);
if (lean::is_scalar(x_15)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_15;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_13);
return x_63;
}
}
else
{
obj* x_66; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_5);
lean::dec(x_2);
x_66 = lean::cnstr_get(x_11, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_69 = x_11;
} else {
 lean::dec(x_11);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_66);
lean::cnstr_set_scalar(x_70, sizeof(void*)*1, x_68);
x_71 = x_70;
x_72 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_72);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_71);
x_75 = l_lean_parser_number_parser___at_lean_parser_command_notation__spec_precedence__lit_parser_lean_parser_has__tokens___spec__1___rarg___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_74, x_75);
x_78 = l_lean_parser_parsec__t_try__mk__res___rarg(x_77);
if (lean::is_scalar(x_15)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_15;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_13);
return x_79;
}
}
}
obj* _init_l_lean_parser_command_set__option_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_0 = lean::mk_string("set_option");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_3, x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_3, x_4);
lean::inc(x_5);
x_7 = l_lean_parser_tokens___rarg(x_5);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_7, x_3);
x_9 = l_lean_parser_tokens___rarg(x_8);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_9, x_5);
x_11 = l_lean_parser_tokens___rarg(x_10);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_11, x_3);
x_13 = l_lean_parser_tokens___rarg(x_12);
x_14 = l_lean_parser_list_cons_tokens___rarg(x_13, x_3);
x_15 = l_lean_parser_list_cons_tokens___rarg(x_3, x_14);
x_16 = l_lean_parser_list_cons_tokens___rarg(x_2, x_15);
x_17 = l_lean_parser_tokens___rarg(x_16);
return x_17;
}
}
obj* _init_l_lean_parser_command_set__option_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_43; 
x_0 = lean::mk_string("set_option");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_string("true");
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
lean::inc(x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__2), 6, 2);
lean::closure_set(x_12, 0, x_11);
lean::closure_set(x_12, 1, x_4);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_8);
x_14 = l_lean_parser_command_bool__option__value;
lean::inc(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__3), 4, 0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_8);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__2), 4, 0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_16);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__2), 6, 2);
lean::closure_set(x_22, 0, x_21);
lean::closure_set(x_22, 1, x_4);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_8);
x_24 = l_lean_parser_command_option__value;
lean::inc(x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_26, 0, x_24);
lean::closure_set(x_26, 1, x_23);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_8);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_lean_parser_command__parser__m_monad___closed__1;
x_32 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_33 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_34 = l_lean_parser_command__parser__m_alternative___closed__1;
x_35 = l_lean_parser_command_set__option;
x_36 = l_lean_parser_command_set__option_has__view;
lean::inc(x_36);
lean::inc(x_35);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::inc(x_31);
x_43 = l_lean_parser_combinators_node_view___rarg(x_31, x_32, x_33, x_34, x_35, x_30, x_36);
return x_43;
}
}
obj* _init_l_lean_parser_command_set__option_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_0 = lean::mk_string("set_option");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_string("true");
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
lean::inc(x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__2), 6, 2);
lean::closure_set(x_12, 0, x_11);
lean::closure_set(x_12, 1, x_4);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_8);
x_14 = l_lean_parser_command_bool__option__value;
lean::inc(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__3), 4, 0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_8);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser___at_lean_parser_command_set__option_parser_lean_parser_has__tokens___spec__2), 4, 0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_16);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens___spec__2), 6, 2);
lean::closure_set(x_22, 0, x_21);
lean::closure_set(x_22, 1, x_4);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_8);
x_24 = l_lean_parser_command_option__value;
lean::inc(x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_26, 0, x_24);
lean::closure_set(x_26, 1, x_23);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_8);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__tokens___spec__1), 4, 0);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
} else {
 lean::dec(x_1);
 x_8 = lean::box(0);
}
lean::inc(x_0);
x_10 = lean::apply_1(x_4, x_0);
x_11 = l_list_map___main___at_lean_parser_command__parser_run___spec__1(x_0, x_6);
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
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_12 = x_7;
} else {
 lean::dec(x_7);
 x_12 = lean::box(0);
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
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_17);
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
obj* x_5; 
x_5 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_orelse___at_lean_parser_command__parser_run___spec__4___rarg), 5, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_6);
x_0 = x_11;
x_1 = x_8;
goto _start;
}
}
}
obj* l_lean_parser_combinators_any__of___at_lean_parser_command__parser_run___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_9; 
x_4 = lean::box(0);
x_5 = l_lean_parser_combinators_any__of___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_6);
lean::inc(x_5);
x_9 = l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__3___rarg(x_5, x_6, x_4, x_4, x_1, x_2, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_15; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_list_foldl___main___at_lean_parser_command__parser_run___spec__5(x_10, x_12, x_1, x_2, x_3);
return x_15;
}
}
}
obj* _init_l_lean_parser_parser__core__t___at_lean_parser_command__parser_run___spec__7() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
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
obj* x_4; obj* x_5; obj* x_6; obj* x_9; 
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_6);
lean::inc(x_5);
x_9 = l_lean_parser_monad__parsec_error___at_lean_parser_command__parser_run___spec__8___rarg(x_5, x_6, x_4, x_4, x_1, x_2);
return x_9;
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
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_4 = lean::string_iterator_remaining(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_add(x_4, x_5);
lean::dec(x_4);
x_8 = l_lean_parser_rec__t_run__parsec___at_lean_parser_command__parser_run___spec__6___closed__1;
lean::inc(x_8);
x_10 = l_lean_parser_rec__t_run___at_lean_parser_command__parser_run___spec__9(x_0, x_8, x_1, x_6);
x_11 = lean::apply_2(x_10, x_2, x_3);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
} else {
 lean::dec(x_11);
 x_16 = lean::box(0);
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_14);
return x_20;
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
