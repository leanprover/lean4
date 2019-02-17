// Lean compiler output
// Module: init.lean.elaborator
// Imports: init.lean.parser.module init.lean.expander init.lean.expr init.lean.options
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
obj* l_lean_parser_token__map_insert___rarg(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
obj* l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5;
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6;
obj* l_lean_elaborator_locally___rarg___lambda__2(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(obj*, obj*, obj*);
extern obj* l_lean_parser_command_variables;
extern "C" obj* lean_expr_mk_pi(obj*, uint8, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__reader__adapter(obj*);
obj* l_lean_elaborator_module_header_elaborate___closed__1;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_level__get__app__args___main___closed__1;
obj* l_lean_elaborator_level__get__app__args___main(obj*, obj*, obj*);
obj* l_lean_elaborator_elab__def__like(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_sort(obj*);
obj* l_lean_elaborator_run___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1(obj*);
obj* l_lean_elaborator_attrs__to__pexpr(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__except___rarg(obj*);
obj* l_lean_elaborator_elaborator__t_monad__reader(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__reader___rarg(obj*);
extern obj* l_lean_parser_command_attribute_has__view;
obj* l_lean_elaborator_namespace_elaborate(obj*, obj*, obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(obj*);
obj* l_lean_elaborator_match__spec___closed__1;
obj* l_lean_elaborator_resolve__context___main___closed__1;
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___rarg(obj*, obj*);
extern obj* l_lean_parser_level_leading_has__view;
extern obj* l_lean_parser_command_reserve__notation_has__view;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate___closed__1;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1(obj*, obj*);
obj* l_list_foldl___main___at_lean_expr_mk__app___spec__1(obj*, obj*);
obj* l_lean_elaborator_run___lambda__5(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_run___closed__2;
obj* l_lean_elaborator_end__scope___lambda__3___closed__1;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_command_declaration;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
obj* l_lean_elaborator_to__level(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__reader__adapter___rarg(obj*);
obj* l_lean_elaborator_get__namespace(obj*);
obj* l_lean_elaborator_level__add(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__7;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14(obj*, obj*, obj*);
extern obj* l_lean_parser_command_export_has__view;
obj* l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__33;
obj* l_lean_elaborator_to__pexpr___main___closed__1;
obj* l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1;
obj* l_lean_elaborator_include_elaborate(obj*, obj*, obj*);
uint8 l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___lambda__1___closed__1;
obj* l_list_filter__map___main___rarg(obj*, obj*);
extern obj* l_lean_parser_term_match_has__view;
obj* l_lean_elaborator_current__command___rarg___closed__1;
obj* l_lean_elaborator_level__get__app__args(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3;
extern obj* l_lean_parser_command_open;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5;
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1___lambda__1(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2;
obj* l_lean_elaborator_run___lambda__2___closed__1;
obj* l_lean_elaborator_elaborator__config__coe__frontend__config(obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___closed__1;
obj* l_lean_elaborator_elaborator__coe__coelaborator(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__26;
obj* l_lean_kvmap_set__string(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1;
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__15(obj*, obj*);
obj* l_lean_elaborator_notation_elaborate__aux___closed__1;
obj* l_lean_elaborator_mk__eqns___closed__2;
obj* l_lean_elaborator_locally___rarg___lambda__3(obj*, obj*, obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_run___lambda__4(obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__31;
obj* l_lean_elaborator_register__notation__macro(obj*, obj*, obj*);
obj* l_lean_elaborator_section_elaborate___lambda__1(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(obj*, obj*, obj*);
obj* l_list_enum__from___main___rarg(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__state(obj*);
obj* l_lean_elaborator_variables_elaborate___closed__2;
uint8 l_lean_elaborator_match__precedence___main(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__39;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__16(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
obj* l_lean_parser_number_view_to__nat___main(obj*);
obj* l_lean_elaborator_run___closed__6;
extern obj* l_lean_parser_term_sort_has__view_x_27___lambda__1___closed__4;
extern obj* l_lean_parser_command_open_has__view;
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(obj*, obj*, obj*, obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_lean_elaborator_run___lambda__8(obj*);
extern "C" obj* lean_expr_local(obj*, obj*, obj*, uint8);
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
obj* l_lean_parser_term_simple__binder_view_to__binder__info___main(obj*);
extern obj* l_lean_parser_command_set__option;
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2(obj*, obj*);
obj* l_lean_elaborator_max__recursion;
obj* l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1___boxed(obj*, obj*);
obj* l_lean_elaborator_section_elaborate___closed__1;
obj* l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg(obj*, obj*);
obj* l_lean_elaborator_elab__def__like___closed__1;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(obj*);
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_expr_mk__annotation___closed__1;
obj* l_list_zip___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(obj*);
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__6;
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_check_elaborate(obj*, obj*, obj*);
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_parser_rec__t_run___at_lean_elaborator_run___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1(obj*, obj*, obj*);
uint8 l_coe__decidable__eq(uint8);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(obj*, obj*, obj*);
extern obj* l_lean_parser_command_notation;
obj* l_lean_elaborator_elaborator__t;
obj* l_lean_elaborator_current__command(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24(obj*, obj*, obj*);
obj* l_lean_kvmap_set__name(obj*, obj*, obj*);
uint8 l_lean_elaborator_is__open__namespace(obj*, obj*);
obj* l_lean_elaborator_elaborators;
obj* l_lean_elaborator_commands_elaborate(uint8, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_string__lit_has__view;
extern obj* l_lean_parser_term_pi_has__view;
obj* l_lean_elaborator_ordered__rbmap_find___rarg(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(obj*, obj*);
obj* l_lean_elaborator_resolve__context___main___lambda__1(obj*, obj*);
extern obj* l_lean_parser_command_universe_has__view;
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
obj* l_lean_elaborator_locally___rarg(obj*, obj*, obj*);
obj* l_state__t_monad__state___rarg(obj*);
obj* l_lean_elaborator_elaborator__m;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
extern "C" obj* lean_expr_mk_lambda(obj*, uint8, obj*, obj*);
obj* l_reader__t_monad__reader__adapter(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_kvmap_set__nat(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
obj* l_lean_elaborator_declaration_elaborate(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main___closed__4;
obj* l_lean_elaborator_check_elaborate___closed__1;
extern obj* l_lean_parser_command_include;
obj* l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(obj*, obj*, obj*);
obj* l_lean_environment_contains___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(obj*, obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
extern "C" obj* lean_expr_mk_const(obj*, obj*);
extern obj* l_lean_parser_command_reserve__notation;
obj* l_lean_elaborator_commands_elaborate___main___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad__except___rarg(obj*);
extern obj* l_lean_parser_term_have_has__view;
obj* l_lean_elaborator_init__quot_elaborate(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
extern obj* l_lean_parser_command_variables_has__view;
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__32;
obj* l_lean_elaborator_end__scope___lambda__1(obj*, obj*);
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_lean_parser_trie_insert___rarg(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22(obj*, obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t___at_lean_elaborator_command_elaborate___spec__2;
obj* l_lean_elaborator_preresolve___main(obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind___rarg___closed__1;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__5;
obj* l_lean_elaborator_yield__to__outside___rarg(obj*);
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__3;
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(obj*, obj*);
obj* l_lean_elaborator_expr_mk__annotation(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___lambda__1(obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25(obj*, obj*);
obj* l_lean_name_replace__prefix___main(obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate__aux___lambda__1(obj*, obj*);
obj* l_lean_elaborator_open_elaborate(obj*, obj*, obj*);
extern obj* l_lean_parser_command_section_has__view;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(obj*);
obj* l_list_join___main___rarg(obj*);
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(obj*, obj*);
obj* l_lean_elaborator_mangle__ident(obj*);
obj* l_lean_elaborator_universe_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2(obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view;
obj* l_lean_elaborator_to__pexpr___main___closed__4;
obj* l_lean_elaborator_commands_elaborate___main___lambda__5(obj*, obj*, obj*);
obj* l_lean_parser_syntax_get__pos(obj*);
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__5(obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind(obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7;
extern "C" obj* level_mk_imax(obj*, obj*);
obj* l_lean_environment_mk__empty___boxed(obj*);
obj* l_lean_elaborator_attribute_elaborate___closed__2;
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5;
obj* l_list_zip__with___main___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1;
obj* l_lean_elaborator_run___closed__3;
obj* l_lean_elaborator_reserve__notation_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_simple__binders__to__pexpr(obj*, obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(obj*, obj*);
obj* l_lean_elaborator_is__open__namespace___boxed(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__47;
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(obj*);
obj* l_lean_elaborator_commands_elaborate___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___closed__1;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__19(obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__parser(obj*, obj*, obj*);
obj* l_lean_elaborator_match__open__spec(obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_run___spec__4(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__11;
obj* l_lean_elaborator_ordered__rbmap_empty(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__16;
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___rarg(obj*, obj*, obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__17;
extern obj* l_lean_parser_module_header;
obj* l_list_map___main___at_lean_elaborator_names__to__pexpr___spec__1(obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__23(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__36;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(obj*);
obj* l_lean_elaborator_update__parser__config(obj*, obj*);
extern obj* l_lean_parser_no__kind;
obj* l_lean_elaborator_run___lambda__4___closed__1;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__46;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__9(obj*, obj*);
obj* l_monad__coroutine__trans___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__tokens(obj*, obj*);
obj* l_except__t_lift___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__10;
obj* l_rbmap_insert___main___at_lean_elaborator_include_elaborate___spec__1(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(obj*, obj*);
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m(obj*);
obj* l_lean_elaborator_run(obj*);
obj* l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1___boxed(obj*);
obj* l_lean_elaborator_match__precedence___boxed(obj*, obj*);
extern obj* l_lean_message__log_empty;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_export_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___lambda__2(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__38;
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(obj*);
uint8 l_lean_elaborator_is__open__namespace___main(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(obj*, obj*, obj*);
extern obj* l_char_has__repr___closed__1;
extern "C" obj* lean_environment_mk_empty(obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__except(obj*);
obj* l_coroutine_bind___main___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_coelaborator;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_mangle__ident___spec__1(obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__9(obj*, obj*, obj*);
extern obj* l_lean_expander_binding__annotation__update;
extern obj* l_lean_parser_command_attribute;
extern obj* l_lean_parser_term_let_has__view;
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3;
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m___rarg(obj*, obj*, obj*, obj*);
extern "C" obj* level_mk_succ(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__45;
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__14;
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(obj*);
obj* l_lean_elaborator_get__namespace___rarg(obj*);
obj* l_lean_elaborator_universe_elaborate___closed__2;
obj* l_lean_elaborator_is__open__namespace___main___boxed(obj*, obj*);
extern obj* l_lean_parser_term_projection_has__view;
obj* l_lean_elaborator_variables_elaborate___closed__1;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__13(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__6___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_coelaborator__m;
obj* l_lean_elaborator_yield__to__outside___rarg___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__12;
obj* l_lean_elaborator_with__current__command(obj*);
obj* l_lean_parser_syntax_to__format___main(obj*);
obj* l_lean_name_append___main(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
extern obj* l_string_join___closed__1;
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2;
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_end__scope___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__35;
obj* l_lean_elaborator_to__pexpr___main___closed__25;
obj* l_lean_elaborator_names__to__pexpr(obj*);
obj* l_list_foldl___main___at_lean_elaborator_include_elaborate___spec__2(obj*, obj*);
extern obj* l_lean_parser_command_check_has__view;
obj* l_lean_elaborator_run___closed__4;
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_set__option_elaborate(obj*, obj*, obj*);
obj* l_reader__t_read___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(obj*, obj*, obj*);
obj* l_lean_elaborator_run___lambda__1(obj*, obj*, obj*);
obj* l_lean_elaborator_no__kind_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_resolve__context___main(obj*, obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_run___spec__6(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_max__prec;
obj* l_lean_elaborator_notation_elaborate__aux(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__7(obj*, obj*);
obj* l_lean_elaborator_end__scope___lambda__2___closed__2;
extern obj* l_lean_options_mk;
obj* l_lean_parser_module_yield__command___lambda__3(obj*, obj*);
obj* l_lean_elaborator_universe_elaborate___closed__1;
obj* l_monad__state__trans___rarg(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__20;
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1;
obj* l_lean_expander_get__opt__type___main(obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4;
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2(obj*, obj*);
extern obj* l_lean_parser_term_struct__inst_has__view;
obj* l_lean_elaborator_run___lambda__7(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_lambda_has__view;
obj* l_lean_elaborator_mk__eqns___closed__1;
obj* l_lean_elaborator_commands_elaborate___main___lambda__3(uint8, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(obj*);
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(obj*);
obj* l_lean_elaborator_commands_elaborate___main(uint8, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8(obj*);
obj* l_lean_elaborator_run___lambda__3(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__1(obj*);
obj* l_lean_elaborator_resolve__context(obj*, obj*, obj*);
obj* l_except__t_monad___rarg(obj*);
extern "C" obj* lean_expr_mk_let(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_app_has__view;
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
obj* l_lean_elaborator_to__level___main(obj*, obj*, obj*);
extern obj* l_lean_parser_ident__univs_has__view;
obj* l_lean_elaborator_to__pexpr___main___closed__9;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(obj*);
obj* l_state__t_monad__except___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_end__scope(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
obj* l_reader__t_monad__except___rarg(obj*);
extern obj* l_lean_parser_term_sort__app_has__view;
obj* l_lean_elaborator_to__pexpr___main___lambda__1(obj*);
extern obj* l_lean_parser_term_explicit_has__view;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3(obj*, obj*);
obj* l_lean_elaborator_current__command___rarg(obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
obj* l_lean_elaborator_prec__to__nat(obj*);
obj* l_lean_parser_term_get__leading(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_end__scope___lambda__2___closed__1;
extern obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__24;
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__6(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_term_parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate(obj*, obj*, obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__13;
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(obj*, obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__3;
obj* l_lean_elaborator_to__level___main___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__27;
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___lambda__4(obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1;
obj* l_lean_format_pretty(obj*, obj*);
extern obj* l_lean_parser_command_namespace_has__view;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__15;
obj* l_lean_elaborator_notation_elaborate___closed__2;
obj* l_lean_elaborator_to__pexpr___main___closed__18;
obj* l_lean_elaborator_elaborator__t_monad(obj*);
extern obj* l_lean_parser_term_inaccessible_has__view;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1;
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__2;
obj* l_lean_elaborator_dummy;
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2(obj*, obj*);
obj* l_lean_elaborator_section_elaborate___lambda__1___closed__1;
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(obj*, obj*);
obj* l_lean_elaborator_run___closed__5;
extern obj* l_coroutine_monad___closed__1;
obj* l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(obj*);
obj* l_lean_elaborator_no__kind_elaborate___lambda__2(obj*, obj*, obj*);
obj* l_lean_elaborator_module_header_elaborate(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_parser_syntax_kind___main(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__2;
obj* l_lean_elaborator_section_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_preresolve(obj*, obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
extern obj* l_lean_parser_module_header_has__view;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26(obj*, obj*, obj*);
uint8 l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__1;
extern obj* l_lean_parser_command_section;
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(obj*, obj*, obj*);
obj* l_reader__t_lift(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__21;
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_struct__inst__item_has__view;
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__2(obj*);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_match__precedence___main___boxed(obj*, obj*);
extern obj* l_lean_parser_term_borrowed_has__view;
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(obj*);
obj* l_lean_parser_term_binders_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_find(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_universe;
obj* l_lean_elaborator_to__pexpr___main___closed__19;
obj* l_list_map___main___at_lean_elaborator_ident__univ__params__to__pexpr___spec__1(obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1;
extern obj* l_lean_parser_term_show_has__view;
obj* l_lean_elaborator_run___lambda__6(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4(obj*, obj*, obj*);
obj* l_lean_elaborator_run___closed__1;
obj* l_except__t_lift___rarg___lambda__1(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(obj*);
obj* l_lean_level_of__nat___main(obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1;
extern obj* l_lean_parser_syntax_reprint__lst___main___closed__1;
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__5(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_end__scope___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__17(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__22;
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(obj*);
obj* l_lean_parser_term_binder__ident_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14(obj*, obj*, obj*);
obj* l_lean_elaborator_coelaborator__m_monad__coroutine;
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__8;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__43;
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_elaborator_attribute_elaborate___closed__1;
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(obj*);
uint8 l_lean_elaborator_match__precedence(obj*, obj*);
obj* l_lean_elaborator_elaborator;
obj* l_lean_elaborator_to__pexpr___main___closed__23;
obj* l_string_trim(obj*);
obj* l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__34;
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__5(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8(obj*, obj*, obj*);
extern obj* l_lean_parser_term_sort_has__view;
obj* l_lean_elaborator_current__command___rarg___lambda__1(obj*, obj*);
obj* l_lean_elaborator_locally(obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
obj* l_lean_elaborator_to__level___main___closed__2;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__5(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(obj*, obj*, obj*);
extern obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
obj* l_lean_elaborator_commands_elaborate___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_match__spec(obj*, obj*);
obj* l_lean_expander_mk__notation__transformer(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__30;
obj* l_lean_expr_local___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__eqns(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___lambda__1(obj*);
obj* l_lean_elaborator_level__add___main(obj*, obj*);
obj* l_lean_elaborator_elaborate__command___boxed(obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_expr_mk__capp(obj*, obj*);
extern "C" obj* level_mk_mvar(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__2(uint8, obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__2(obj*);
obj* l_lean_elaborator_run___lambda__1___closed__1;
extern obj* l_lean_parser_command_declaration_has__view;
obj* l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
extern obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
obj* l_lean_elaborator_run___closed__7;
obj* l_lean_kvmap_insert__core___main(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__28;
obj* l_lean_elaborator_to__level___main___closed__3;
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__1(obj*, obj*, obj*);
extern obj* l_lean_parser_command_end_has__view;
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__1(obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__4(obj*, obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13;
extern obj* l_lean_parser_term_anonymous__constructor_has__view;
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2;
obj* l_lean_elaborator_to__pexpr___main___closed__37;
obj* l_lean_elaborator_attribute_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___lambda__2(obj*);
extern obj* l_lean_parser_command_init__quot;
obj* l_lean_elaborator_variables_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__41;
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(obj*);
obj* l_lean_elaborator_ident__univ__params__to__pexpr(obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(obj*, obj*);
obj* l_rbtree_to__list___rarg(obj*);
obj* l_coroutine_pure___rarg(obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad___rarg(obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(obj*, obj*, obj*);
obj* l_lean_elaborator_yield__to__outside(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__3(obj*, obj*);
obj* l_lean_elaborator_section_elaborate___lambda__2(obj*, obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__coe__coelaborator___lambda__1(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__21(obj*, obj*);
obj* l_lean_elaborator_postprocess__notation__spec(obj*);
obj* l_lean_elaborator_elab__def__like___closed__2;
extern obj* l_lean_parser_command_include_has__view;
extern obj* l_lean_parser_command_namespace;
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2(obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(obj*);
obj* l_lean_elaborator_old__elab__command(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1(obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
extern "C" obj* level_mk_param(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_state__t_lift___rarg(obj*, obj*, obj*, obj*);
extern "C" obj* lean_elaborator_elaborate_command(obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20(obj*, obj*, obj*);
extern obj* l_lean_expander_get__opt__type___main___closed__1;
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__10(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_level_trailing_has__view;
obj* l_lean_elaborator_no__kind_elaborate___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___closed__1;
obj* l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__29;
extern obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_option_map___rarg(obj*, obj*);
extern obj* l_lean_expander_no__expansion___closed__1;
extern "C" obj* lean_expr_mk_bvar(obj*);
obj* l_coroutine_yield___rarg(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__40;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(obj*);
extern "C" obj* lean_expr_mk_mvar(obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1(obj*);
obj* l_lean_elaborator_command_elaborate(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(obj*, obj*, obj*);
obj* l_lean_elaborator_prec__to__nat___main(obj*);
obj* l_lean_elaborator_with__current__command___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_view_value(obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4(obj*, obj*, uint8, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__42;
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1;
extern "C" uint8 lean_environment_contains(obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1(obj*, obj*, obj*);
extern obj* l_lean_parser_command_notation_has__view;
extern obj* l_lean_parser_command_check;
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__1(obj*, obj*);
obj* l_lean_elaborator_max__commands;
extern obj* l_lean_parser_command_export;
obj* l_lean_elaborator_elaborator__t_monad__state___rarg(obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__44;
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12(obj*, obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
obj* l_lean_elaborator_init__quot_elaborate___closed__1;
obj* l_lean_elaborator_postprocess__notation__spec___closed__1;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2;
extern obj* l_lean_parser_command_set__option_has__view;
obj* l_lean_environment_mk__empty___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean_environment_mk_empty(x_0);
return x_1;
}
}
obj* l_lean_environment_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean_environment_contains(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_lean_expr_local___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
x_5 = lean_expr_local(x_0, x_1, x_2, x_4);
return x_5;
}
}
obj* l_lean_elaborator_elaborate__command___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_elaborator_elaborate_command(x_0, x_1, x_2);
return x_3;
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_empty___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set(x_3, 2, x_1);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
lean::inc(x_8);
return x_8;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_14 = x_1;
}
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_30; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_0);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_3);
lean::cnstr_set(x_30, 3, x_12);
return x_30;
}
else
{
obj* x_31; obj* x_32; 
x_31 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_12, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_6);
lean::cnstr_set(x_32, 1, x_8);
lean::cnstr_set(x_32, 2, x_10);
lean::cnstr_set(x_32, 3, x_31);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
x_33 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_6, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_34 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_34 = x_14;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_8);
lean::cnstr_set(x_34, 2, x_10);
lean::cnstr_set(x_34, 3, x_12);
return x_34;
}
}
default:
{
obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_47; uint8 x_48; 
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_1, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 2);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_1, 3);
lean::inc(x_41);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_43 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_43 = x_1;
}
lean::inc(x_37);
lean::inc(x_2);
lean::inc(x_0);
x_47 = lean::apply_2(x_0, x_2, x_37);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_53; uint8 x_54; 
lean::inc(x_2);
lean::inc(x_37);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_37, x_2);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_59; 
lean::dec(x_0);
lean::dec(x_39);
lean::dec(x_37);
if (lean::is_scalar(x_43)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_43;
}
lean::cnstr_set(x_59, 0, x_35);
lean::cnstr_set(x_59, 1, x_2);
lean::cnstr_set(x_59, 2, x_3);
lean::cnstr_set(x_59, 3, x_41);
return x_59;
}
else
{
uint8 x_61; 
lean::inc(x_41);
x_61 = l_rbnode_get__color___main___rarg(x_41);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_43);
x_63 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_41, x_2, x_3);
x_64 = l_rbnode_balance2__node___main___rarg(x_63, x_37, x_39, x_35);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_41, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_43;
}
lean::cnstr_set(x_66, 0, x_35);
lean::cnstr_set(x_66, 1, x_37);
lean::cnstr_set(x_66, 2, x_39);
lean::cnstr_set(x_66, 3, x_65);
return x_66;
}
}
}
else
{
uint8 x_68; 
lean::inc(x_35);
x_68 = l_rbnode_get__color___main___rarg(x_35);
if (x_68 == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_43);
x_70 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_35, x_2, x_3);
x_71 = l_rbnode_balance1__node___main___rarg(x_70, x_37, x_39, x_41);
return x_71;
}
else
{
obj* x_72; obj* x_73; 
x_72 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_73 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_73 = x_43;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_37);
lean::cnstr_set(x_73, 2, x_39);
lean::cnstr_set(x_73, 3, x_41);
return x_73;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_22; 
lean::inc(x_3);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_3);
x_17 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(x_0, x_10, x_2, x_16);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_12, x_18);
lean::dec(x_18);
lean::dec(x_12);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_9);
lean::cnstr_set(x_22, 1, x_17);
lean::cnstr_set(x_22, 2, x_19);
return x_22;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_insert___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
return x_7;
}
case 1:
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_20; uint8 x_21; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 3);
lean::inc(x_14);
lean::dec(x_2);
lean::inc(x_10);
lean::inc(x_3);
lean::inc(x_0);
x_20 = lean::apply_2(x_0, x_3, x_10);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_26; uint8 x_27; 
lean::dec(x_8);
lean::inc(x_3);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_10, x_3);
x_27 = lean::unbox(x_26);
lean::dec(x_26);
if (x_27 == 0)
{
obj* x_32; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_14);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_12);
return x_32;
}
else
{
lean::dec(x_12);
x_1 = x_0;
x_2 = x_14;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_14);
x_1 = x_0;
x_2 = x_8;
goto _start;
}
}
default:
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_2, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_2, 1);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_2, 2);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_2, 3);
lean::inc(x_45);
lean::dec(x_2);
lean::inc(x_41);
lean::inc(x_3);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_3, x_41);
x_52 = lean::unbox(x_51);
lean::dec(x_51);
if (x_52 == 0)
{
obj* x_57; uint8 x_58; 
lean::dec(x_39);
lean::inc(x_3);
lean::inc(x_0);
x_57 = lean::apply_2(x_0, x_41, x_3);
x_58 = lean::unbox(x_57);
lean::dec(x_57);
if (x_58 == 0)
{
obj* x_63; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_45);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_43);
return x_63;
}
else
{
lean::dec(x_43);
x_1 = x_0;
x_2 = x_45;
goto _start;
}
}
else
{
lean::dec(x_43);
lean::dec(x_41);
lean::dec(x_45);
x_1 = x_0;
x_2 = x_39;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg), 4, 0);
return x_4;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___rarg), 3, 0);
return x_6;
}
}
obj* l_lean_elaborator_ordered__rbmap_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_6 = l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(x_0, lean::box(0), x_3, x_2);
return x_6;
}
}
obj* l_lean_elaborator_ordered__rbmap_find(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_find___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_14 = x_1;
}
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_30; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_0);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_3);
lean::cnstr_set(x_30, 3, x_12);
return x_30;
}
else
{
obj* x_31; obj* x_32; 
x_31 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_12, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_6);
lean::cnstr_set(x_32, 1, x_8);
lean::cnstr_set(x_32, 2, x_10);
lean::cnstr_set(x_32, 3, x_31);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
x_33 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_6, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_34 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_34 = x_14;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_8);
lean::cnstr_set(x_34, 2, x_10);
lean::cnstr_set(x_34, 3, x_12);
return x_34;
}
}
default:
{
obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_47; uint8 x_48; 
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_1, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 2);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_1, 3);
lean::inc(x_41);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_43 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_43 = x_1;
}
lean::inc(x_37);
lean::inc(x_2);
lean::inc(x_0);
x_47 = lean::apply_2(x_0, x_2, x_37);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_53; uint8 x_54; 
lean::inc(x_2);
lean::inc(x_37);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_37, x_2);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_59; 
lean::dec(x_0);
lean::dec(x_39);
lean::dec(x_37);
if (lean::is_scalar(x_43)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_43;
}
lean::cnstr_set(x_59, 0, x_35);
lean::cnstr_set(x_59, 1, x_2);
lean::cnstr_set(x_59, 2, x_3);
lean::cnstr_set(x_59, 3, x_41);
return x_59;
}
else
{
uint8 x_61; 
lean::inc(x_41);
x_61 = l_rbnode_get__color___main___rarg(x_41);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_43);
x_63 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_41, x_2, x_3);
x_64 = l_rbnode_balance2__node___main___rarg(x_63, x_37, x_39, x_35);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_41, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_43;
}
lean::cnstr_set(x_66, 0, x_35);
lean::cnstr_set(x_66, 1, x_37);
lean::cnstr_set(x_66, 2, x_39);
lean::cnstr_set(x_66, 3, x_65);
return x_66;
}
}
}
else
{
uint8 x_68; 
lean::inc(x_35);
x_68 = l_rbnode_get__color___main___rarg(x_35);
if (x_68 == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_43);
x_70 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_35, x_2, x_3);
x_71 = l_rbnode_balance1__node___main___rarg(x_70, x_37, x_39, x_41);
return x_71;
}
else
{
obj* x_72; obj* x_73; 
x_72 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_73 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_73 = x_43;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_37);
lean::cnstr_set(x_73, 2, x_39);
lean::cnstr_set(x_73, 3, x_41);
return x_73;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg), 4, 0);
return x_6;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_22; 
lean::inc(x_3);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_3);
x_17 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(x_0, x_10, x_2, x_16);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_12, x_18);
lean::dec(x_18);
lean::dec(x_12);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_9);
lean::cnstr_set(x_22, 1, x_17);
lean::cnstr_set(x_22, 2, x_19);
return x_22;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
lean::inc(x_8);
return x_8;
}
}
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__6___rarg), 3, 0);
return x_6;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
lean::inc(x_2);
x_4 = l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__6___rarg(x_0, x_2, x_1);
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_of__list___rarg), 2, 0);
return x_6;
}
}
obj* l_lean_elaborator_elaborator__config__coe__frontend__config(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_elaborator__t_monad___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_except__t_monad___rarg(x_0);
x_2 = l_state__t_monad___rarg(x_1);
x_3 = l_reader__t_monad___rarg(x_2);
return x_3;
}
}
obj* l_lean_elaborator_elaborator__t_monad(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__t_monad___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_elaborator_elaborator__t_monad__reader___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_except__t_monad___rarg(x_0);
x_2 = l_state__t_monad___rarg(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_read___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_lean_elaborator_elaborator__t_monad__reader(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__t_monad__reader___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_elaborator_elaborator__t_monad__state___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_except__t_monad___rarg(x_0);
lean::inc(x_1);
x_3 = l_state__t_monad___rarg(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_4, 0, lean::box(0));
lean::closure_set(x_4, 1, lean::box(0));
lean::closure_set(x_4, 2, x_3);
x_5 = l_state__t_monad__state___rarg(x_1);
x_6 = l_monad__state__trans___rarg(x_4, x_5);
return x_6;
}
}
obj* l_lean_elaborator_elaborator__t_monad__state(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__t_monad__state___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_elaborator_elaborator__t_monad__except___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
lean::inc(x_0);
x_2 = l_except__t_monad___rarg(x_0);
x_3 = l_except__t_monad__except___rarg(x_0);
x_4 = l_state__t_monad__except___rarg(x_2, lean::box(0), x_3);
x_5 = l_reader__t_monad__except___rarg(x_4);
return x_5;
}
}
obj* l_lean_elaborator_elaborator__t_monad__except(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__t_monad__except___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_lean_elaborator_elaborator__t() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_elaborator_elaborator__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_elaborator_elaborator() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_elaborator_coelaborator__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_elaborator_coelaborator() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_elaborator_elaborator__t___at_lean_elaborator_command_elaborate___spec__2() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
}
if (lean::is_scalar(x_5)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_5;
}
lean::cnstr_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::apply_1(x_0, x_8);
return x_11;
}
}
}
obj* l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 0);
return x_4;
}
}
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::apply_3(x_3, x_0, x_1, x_5);
return x_8;
}
}
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_lean_elaborator_command_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_3, x_0, x_1, x_2);
return x_4;
}
}
obj* _init_l_lean_elaborator_coelaborator__m_monad__coroutine() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = l_coroutine_monad___closed__1;
lean::inc(x_0);
x_2 = l_lean_elaborator_elaborator__t_monad___rarg(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, lean::box(0));
lean::closure_set(x_3, 2, x_2);
lean::inc(x_0);
x_5 = l_except__t_monad___rarg(x_0);
lean::inc(x_5);
x_7 = l_state__t_monad___rarg(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_8, 0, lean::box(0));
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg), 4, 1);
lean::closure_set(x_9, 0, x_5);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg), 3, 1);
lean::closure_set(x_11, 0, x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_yield___rarg), 2, 0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_14, 0, x_9);
lean::closure_set(x_14, 1, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_15, 0, x_8);
lean::closure_set(x_15, 1, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_16, 0, x_3);
lean::closure_set(x_16, 1, x_15);
return x_16;
}
}
obj* l_lean_elaborator_elaborator__t_monad__reader__adapter___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_except__t_monad___rarg(x_0);
x_2 = l_state__t_monad___rarg(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__reader__adapter), 5, 4);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, lean::box(0));
lean::closure_set(x_3, 2, lean::box(0));
lean::closure_set(x_3, 3, x_2);
return x_3;
}
}
obj* l_lean_elaborator_elaborator__t_monad__reader__adapter(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__t_monad__reader__adapter___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_elaborator_current__command___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_elaborator_current__command___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pure___rarg), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__1), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_4, 0, x_3);
lean::closure_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_lean_elaborator_current__command___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg___lambda__1), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_lean_elaborator_current__command___rarg___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_5, 0, x_3);
lean::closure_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_lean_elaborator_current__command(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 1, 0);
return x_4;
}
}
obj* l_lean_elaborator_with__current__command___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; 
lean::dec(x_5);
x_7 = lean::apply_4(x_1, x_2, x_3, x_4, x_0);
return x_7;
}
}
obj* l_lean_elaborator_with__current__command(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_with__current__command___rarg), 6, 0);
return x_2;
}
}
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__m__coe__coelaborator__m___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_elaborator_elaborator__coe__coelaborator___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::apply_3(x_0, x_3, x_1, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
}
}
obj* l_lean_elaborator_elaborator__coe__coelaborator(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_5 = l_lean_elaborator_current__command___rarg(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__coe__coelaborator___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_5);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_list_foldl___main___at_lean_elaborator_mangle__ident___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean_name_mk_numeral(x_0, x_2);
x_0 = x_7;
x_1 = x_4;
goto _start;
}
}
}
obj* l_lean_elaborator_mangle__ident(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 2);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 4);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_list_foldl___main___at_lean_elaborator_mangle__ident___spec__1(x_1, x_3);
return x_6;
}
}
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
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
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* _init_l_lean_elaborator_level__get__app__args___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("level_get_app_args: unexpected input: ");
return x_0;
}
}
obj* l_lean_elaborator_level__get__app__args___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_0);
x_4 = l_lean_parser_syntax_kind___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::inc(x_0);
x_6 = l_lean_parser_syntax_to__format___main(x_0);
x_7 = lean::mk_nat_obj(80u);
x_8 = l_lean_format_pretty(x_6, x_7);
x_9 = l_lean_elaborator_level__get__app__args___main___closed__1;
lean::inc(x_9);
x_11 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_13 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_11, x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_17; uint8 x_18; 
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
lean::dec(x_4);
x_17 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_18 = lean_name_dec_eq(x_14, x_17);
if (x_18 == 0)
{
obj* x_19; uint8 x_20; 
x_19 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_20 = lean_name_dec_eq(x_14, x_19);
lean::dec(x_14);
if (x_20 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; 
lean::inc(x_0);
x_23 = l_lean_parser_syntax_to__format___main(x_0);
x_24 = lean::mk_nat_obj(80u);
x_25 = l_lean_format_pretty(x_23, x_24);
x_26 = l_lean_elaborator_level__get__app__args___main___closed__1;
lean::inc(x_26);
x_28 = lean::string_append(x_26, x_25);
lean::dec(x_25);
x_30 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_28, x_1, x_2);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_35; 
x_31 = l_lean_parser_level_trailing_has__view;
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
lean::inc(x_0);
x_35 = lean::apply_1(x_32, x_0);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; obj* x_40; obj* x_42; 
lean::dec(x_0);
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
lean::dec(x_35);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = l_lean_elaborator_level__get__app__args___main(x_40, x_1, x_2);
if (lean::obj_tag(x_42) == 0)
{
obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_37);
x_44 = lean::cnstr_get(x_42, 0);
lean::inc(x_44);
if (lean::is_shared(x_42)) {
 lean::dec(x_42);
 x_46 = lean::box(0);
} else {
 lean::cnstr_release(x_42, 0);
 x_46 = x_42;
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
obj* x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_48 = lean::cnstr_get(x_42, 0);
lean::inc(x_48);
if (lean::is_shared(x_42)) {
 lean::dec(x_42);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_42, 0);
 x_50 = x_42;
}
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_55 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_55 = x_48;
}
x_56 = lean::cnstr_get(x_51, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_51, 1);
lean::inc(x_58);
if (lean::is_shared(x_51)) {
 lean::dec(x_51);
 x_60 = lean::box(0);
} else {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_60 = x_51;
}
x_61 = lean::cnstr_get(x_37, 1);
lean::inc(x_61);
lean::dec(x_37);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_61);
lean::cnstr_set(x_64, 1, x_58);
if (lean::is_scalar(x_55)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_55;
}
lean::cnstr_set(x_65, 0, x_56);
lean::cnstr_set(x_65, 1, x_64);
if (lean::is_scalar(x_60)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_60;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_50)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_50;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_1);
lean::dec(x_35);
x_70 = lean::box(0);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_0);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_2);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_1);
lean::dec(x_14);
x_76 = lean::box(0);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_0);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_2);
x_79 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
return x_79;
}
}
}
}
obj* l_lean_elaborator_level__get__app__args(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_level__get__app__args___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_elaborator_level__add___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
x_9 = l_lean_elaborator_level__add___main(x_0, x_6);
x_10 = level_mk_succ(x_9);
return x_10;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_lean_elaborator_level__add(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_level__add___main(x_0, x_1);
return x_2;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
lean::inc(x_1);
x_13 = l_lean_elaborator_to__level___main(x_7, x_1, x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
}
x_29 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_36; 
lean::dec(x_11);
lean::dec(x_24);
lean::dec(x_28);
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
lean::dec(x_29);
if (lean::is_scalar(x_23)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_23;
 lean::cnstr_set_tag(x_23, 0);
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
if (lean::is_scalar(x_11)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_11;
}
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_28)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_28;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_23)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_23;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(x_0, x_4);
x_8 = level_mk_max(x_2, x_7);
return x_8;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
lean::inc(x_1);
x_13 = l_lean_elaborator_to__level___main(x_7, x_1, x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
}
x_29 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_36; 
lean::dec(x_11);
lean::dec(x_24);
lean::dec(x_28);
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
lean::dec(x_29);
if (lean::is_scalar(x_23)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_23;
 lean::cnstr_set_tag(x_23, 0);
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
if (lean::is_scalar(x_11)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_11;
}
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_28)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_28;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_23)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_23;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(x_0, x_4);
x_8 = level_mk_imax(x_2, x_7);
return x_8;
}
}
}
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_2, x_1);
return x_5;
}
}
obj* _init_l_lean_elaborator_to__level___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("to_level: unexpected input: ");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__level___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed universe level");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__level___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = level_mk_mvar(x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_to__level___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown universe variable '");
return x_0;
}
}
obj* l_lean_elaborator_to__level___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_lean_elaborator_level__get__app__args___main(x_0, x_1, x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_10 = x_5;
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_26; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
}
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_19 = x_12;
}
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_15, 1);
lean::inc(x_22);
lean::dec(x_15);
lean::inc(x_20);
x_26 = l_lean_parser_syntax_kind___main(x_20);
if (lean::obj_tag(x_26) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_39; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
lean::dec(x_20);
lean::inc(x_0);
x_32 = l_lean_parser_syntax_to__format___main(x_0);
x_33 = lean::mk_nat_obj(80u);
x_34 = l_lean_format_pretty(x_32, x_33);
x_35 = l_lean_elaborator_to__level___main___closed__1;
lean::inc(x_35);
x_37 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_39 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_37, x_1, x_17);
return x_39;
}
else
{
obj* x_40; obj* x_43; uint8 x_44; 
x_40 = lean::cnstr_get(x_26, 0);
lean::inc(x_40);
lean::dec(x_26);
x_43 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_44 = lean_name_dec_eq(x_40, x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_46 = lean_name_dec_eq(x_40, x_45);
lean::dec(x_40);
if (x_46 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_60; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
lean::dec(x_20);
lean::inc(x_0);
x_53 = l_lean_parser_syntax_to__format___main(x_0);
x_54 = lean::mk_nat_obj(80u);
x_55 = l_lean_format_pretty(x_53, x_54);
x_56 = l_lean_elaborator_to__level___main___closed__1;
lean::inc(x_56);
x_58 = lean::string_append(x_56, x_55);
lean::dec(x_55);
x_60 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_58, x_1, x_17);
return x_60;
}
else
{
obj* x_61; obj* x_62; obj* x_64; 
x_61 = l_lean_parser_level_trailing_has__view;
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::apply_1(x_62, x_20);
if (lean::obj_tag(x_64) == 0)
{
obj* x_69; obj* x_71; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_64);
lean::dec(x_19);
x_69 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_69);
x_71 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_69, x_1, x_17);
return x_71;
}
else
{
obj* x_72; 
x_72 = lean::cnstr_get(x_64, 0);
lean::inc(x_72);
lean::dec(x_64);
if (lean::obj_tag(x_22) == 0)
{
obj* x_76; obj* x_78; 
lean::dec(x_0);
x_76 = lean::cnstr_get(x_72, 0);
lean::inc(x_76);
x_78 = l_lean_elaborator_to__level___main(x_76, x_1, x_17);
if (lean::obj_tag(x_78) == 0)
{
obj* x_81; obj* x_84; 
lean::dec(x_72);
lean::dec(x_19);
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
lean::dec(x_78);
if (lean::is_scalar(x_14)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_14;
 lean::cnstr_set_tag(x_14, 0);
}
lean::cnstr_set(x_84, 0, x_81);
return x_84;
}
else
{
obj* x_85; obj* x_88; obj* x_90; obj* x_93; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_85 = lean::cnstr_get(x_78, 0);
lean::inc(x_85);
lean::dec(x_78);
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_85, 1);
lean::inc(x_90);
lean::dec(x_85);
x_93 = lean::cnstr_get(x_72, 2);
lean::inc(x_93);
lean::dec(x_72);
x_96 = l_lean_parser_number_view_to__nat___main(x_93);
x_97 = l_lean_elaborator_level__add___main(x_88, x_96);
if (lean::is_scalar(x_19)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_19;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_90);
if (lean::is_scalar(x_14)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_14;
}
lean::cnstr_set(x_99, 0, x_98);
return x_99;
}
}
else
{
obj* x_104; obj* x_106; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_72);
lean::dec(x_19);
x_104 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_104);
x_106 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_104, x_1, x_17);
return x_106;
}
}
}
}
else
{
obj* x_108; obj* x_109; obj* x_111; 
lean::dec(x_40);
x_108 = l_lean_parser_level_leading_has__view;
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::apply_1(x_109, x_20);
switch (lean::obj_tag(x_111)) {
case 0:
{
lean::dec(x_111);
if (lean::obj_tag(x_22) == 0)
{
obj* x_115; obj* x_117; 
lean::dec(x_14);
lean::dec(x_19);
x_115 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_115);
x_117 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_115, x_1, x_17);
return x_117;
}
else
{
obj* x_119; obj* x_121; obj* x_125; 
lean::dec(x_0);
x_119 = lean::cnstr_get(x_22, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_22, 1);
lean::inc(x_121);
lean::dec(x_22);
lean::inc(x_1);
x_125 = l_lean_elaborator_to__level___main(x_119, x_1, x_17);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_132; 
lean::dec(x_1);
lean::dec(x_19);
lean::dec(x_121);
x_129 = lean::cnstr_get(x_125, 0);
lean::inc(x_129);
lean::dec(x_125);
if (lean::is_scalar(x_14)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_14;
 lean::cnstr_set_tag(x_14, 0);
}
lean::cnstr_set(x_132, 0, x_129);
return x_132;
}
else
{
obj* x_133; obj* x_136; obj* x_138; obj* x_141; 
x_133 = lean::cnstr_get(x_125, 0);
lean::inc(x_133);
lean::dec(x_125);
x_136 = lean::cnstr_get(x_133, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_133, 1);
lean::inc(x_138);
lean::dec(x_133);
x_141 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_121, x_1, x_138);
if (lean::obj_tag(x_141) == 0)
{
obj* x_144; obj* x_147; 
lean::dec(x_19);
lean::dec(x_136);
x_144 = lean::cnstr_get(x_141, 0);
lean::inc(x_144);
lean::dec(x_141);
if (lean::is_scalar(x_14)) {
 x_147 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_147 = x_14;
 lean::cnstr_set_tag(x_14, 0);
}
lean::cnstr_set(x_147, 0, x_144);
return x_147;
}
else
{
obj* x_148; obj* x_151; obj* x_153; obj* x_156; obj* x_157; obj* x_158; 
x_148 = lean::cnstr_get(x_141, 0);
lean::inc(x_148);
lean::dec(x_141);
x_151 = lean::cnstr_get(x_148, 0);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_148, 1);
lean::inc(x_153);
lean::dec(x_148);
x_156 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(x_136, x_151);
if (lean::is_scalar(x_19)) {
 x_157 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_157 = x_19;
}
lean::cnstr_set(x_157, 0, x_156);
lean::cnstr_set(x_157, 1, x_153);
if (lean::is_scalar(x_14)) {
 x_158 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_158 = x_14;
}
lean::cnstr_set(x_158, 0, x_157);
return x_158;
}
}
}
}
case 1:
{
lean::dec(x_111);
if (lean::obj_tag(x_22) == 0)
{
obj* x_162; obj* x_164; 
lean::dec(x_14);
lean::dec(x_19);
x_162 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_162);
x_164 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_162, x_1, x_17);
return x_164;
}
else
{
obj* x_166; obj* x_168; obj* x_172; 
lean::dec(x_0);
x_166 = lean::cnstr_get(x_22, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get(x_22, 1);
lean::inc(x_168);
lean::dec(x_22);
lean::inc(x_1);
x_172 = l_lean_elaborator_to__level___main(x_166, x_1, x_17);
if (lean::obj_tag(x_172) == 0)
{
obj* x_176; obj* x_179; 
lean::dec(x_168);
lean::dec(x_1);
lean::dec(x_19);
x_176 = lean::cnstr_get(x_172, 0);
lean::inc(x_176);
lean::dec(x_172);
if (lean::is_scalar(x_14)) {
 x_179 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_179 = x_14;
 lean::cnstr_set_tag(x_14, 0);
}
lean::cnstr_set(x_179, 0, x_176);
return x_179;
}
else
{
obj* x_180; obj* x_183; obj* x_185; obj* x_188; 
x_180 = lean::cnstr_get(x_172, 0);
lean::inc(x_180);
lean::dec(x_172);
x_183 = lean::cnstr_get(x_180, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_180, 1);
lean::inc(x_185);
lean::dec(x_180);
x_188 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_168, x_1, x_185);
if (lean::obj_tag(x_188) == 0)
{
obj* x_191; obj* x_194; 
lean::dec(x_183);
lean::dec(x_19);
x_191 = lean::cnstr_get(x_188, 0);
lean::inc(x_191);
lean::dec(x_188);
if (lean::is_scalar(x_14)) {
 x_194 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_194 = x_14;
 lean::cnstr_set_tag(x_14, 0);
}
lean::cnstr_set(x_194, 0, x_191);
return x_194;
}
else
{
obj* x_195; obj* x_198; obj* x_200; obj* x_203; obj* x_204; obj* x_205; 
x_195 = lean::cnstr_get(x_188, 0);
lean::inc(x_195);
lean::dec(x_188);
x_198 = lean::cnstr_get(x_195, 0);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_195, 1);
lean::inc(x_200);
lean::dec(x_195);
x_203 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(x_183, x_198);
if (lean::is_scalar(x_19)) {
 x_204 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_204 = x_19;
}
lean::cnstr_set(x_204, 0, x_203);
lean::cnstr_set(x_204, 1, x_200);
if (lean::is_scalar(x_14)) {
 x_205 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_205 = x_14;
}
lean::cnstr_set(x_205, 0, x_204);
return x_205;
}
}
}
}
case 2:
{
lean::dec(x_111);
if (lean::obj_tag(x_22) == 0)
{
obj* x_209; obj* x_211; obj* x_212; 
lean::dec(x_1);
lean::dec(x_0);
x_209 = l_lean_elaborator_to__level___main___closed__3;
lean::inc(x_209);
if (lean::is_scalar(x_19)) {
 x_211 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_211 = x_19;
}
lean::cnstr_set(x_211, 0, x_209);
lean::cnstr_set(x_211, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_212 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_212 = x_14;
}
lean::cnstr_set(x_212, 0, x_211);
return x_212;
}
else
{
obj* x_216; obj* x_218; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
x_216 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_216);
x_218 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_216, x_1, x_17);
return x_218;
}
}
case 3:
{
obj* x_223; obj* x_225; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
lean::dec(x_111);
x_223 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_223);
x_225 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_223, x_1, x_17);
return x_225;
}
case 4:
{
obj* x_226; 
x_226 = lean::cnstr_get(x_111, 0);
lean::inc(x_226);
lean::dec(x_111);
if (lean::obj_tag(x_22) == 0)
{
obj* x_231; obj* x_232; obj* x_233; obj* x_234; 
lean::dec(x_1);
lean::dec(x_0);
x_231 = l_lean_parser_number_view_to__nat___main(x_226);
x_232 = l_lean_level_of__nat___main(x_231);
if (lean::is_scalar(x_19)) {
 x_233 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_233 = x_19;
}
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_234 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_234 = x_14;
}
lean::cnstr_set(x_234, 0, x_233);
return x_234;
}
else
{
obj* x_239; obj* x_241; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_226);
lean::dec(x_19);
x_239 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_239);
x_241 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_239, x_1, x_17);
return x_241;
}
}
default:
{
obj* x_242; 
x_242 = lean::cnstr_get(x_111, 0);
lean::inc(x_242);
lean::dec(x_111);
if (lean::obj_tag(x_22) == 0)
{
obj* x_245; obj* x_246; obj* x_248; obj* x_252; 
x_245 = l_lean_elaborator_mangle__ident(x_242);
x_246 = lean::cnstr_get(x_17, 4);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_246, 1);
lean::inc(x_248);
lean::dec(x_246);
lean::inc(x_245);
x_252 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_248, x_245);
if (lean::obj_tag(x_252) == 0)
{
obj* x_255; obj* x_257; obj* x_258; obj* x_260; obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_14);
lean::dec(x_19);
x_255 = l_lean_name_to__string___closed__1;
lean::inc(x_255);
x_257 = l_lean_name_to__string__with__sep___main(x_255, x_245);
x_258 = l_lean_elaborator_to__level___main___closed__4;
lean::inc(x_258);
x_260 = lean::string_append(x_258, x_257);
lean::dec(x_257);
x_262 = l_char_has__repr___closed__1;
x_263 = lean::string_append(x_260, x_262);
x_264 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_263, x_1, x_17);
return x_264;
}
else
{
obj* x_268; obj* x_269; obj* x_270; 
lean::dec(x_252);
lean::dec(x_1);
lean::dec(x_0);
x_268 = level_mk_param(x_245);
if (lean::is_scalar(x_19)) {
 x_269 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_269 = x_19;
}
lean::cnstr_set(x_269, 0, x_268);
lean::cnstr_set(x_269, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_270 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_270 = x_14;
}
lean::cnstr_set(x_270, 0, x_269);
return x_270;
}
}
else
{
obj* x_275; obj* x_277; 
lean::dec(x_242);
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
x_275 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_275);
x_277 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_275, x_1, x_17);
return x_277;
}
}
}
}
}
}
}
}
obj* l_lean_elaborator_to__level(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_to__level___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _init_l_lean_elaborator_expr_mk__annotation___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("annotation");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_expr_mk__annotation(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::box(0);
x_3 = l_lean_elaborator_expr_mk__annotation___closed__1;
lean::inc(x_3);
x_5 = l_lean_kvmap_set__name(x_2, x_3, x_0);
x_6 = lean_expr_mk_mdata(x_5, x_1);
return x_6;
}
}
obj* _init_l_lean_elaborator_dummy() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Prop");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean_expr_mk_const(x_3, x_0);
return x_4;
}
}
obj* _init_l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_20; uint8 x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
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
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
lean::dec(x_11);
lean::inc(x_0);
x_20 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(x_0, x_6);
x_21 = 4;
lean::inc(x_9);
x_23 = lean_expr_local(x_9, x_9, x_0, x_21);
x_24 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
lean::inc(x_24);
x_26 = l_lean_elaborator_expr_mk__annotation(x_24, x_23);
x_27 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_26, x_14);
x_28 = lean_expr_mk_app(x_27, x_16);
if (lean::is_scalar(x_8)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_8;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_20);
return x_29;
}
}
}
obj* _init_l_lean_elaborator_mk__eqns___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_mk__eqns___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("pre_equations");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_mk__eqns(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_2 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(x_0, x_1);
x_3 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_3);
x_5 = l_lean_expr_mk__capp(x_3, x_2);
x_6 = l_lean_elaborator_mk__eqns___closed__2;
lean::inc(x_6);
x_8 = l_lean_elaborator_expr_mk__annotation(x_6, x_5);
return x_8;
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_0, x_4);
x_8 = lean_expr_mk_app(x_2, x_7);
return x_8;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_16; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
lean::inc(x_1);
x_16 = l_lean_elaborator_to__pexpr___main(x_12, x_1, x_2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_22 = x_16;
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; 
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_26 = x_16;
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 x_31 = x_24;
}
x_32 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(x_9, x_1, x_29);
if (lean::obj_tag(x_32) == 0)
{
obj* x_36; obj* x_39; 
lean::dec(x_11);
lean::dec(x_27);
lean::dec(x_31);
x_36 = lean::cnstr_get(x_32, 0);
lean::inc(x_36);
lean::dec(x_32);
if (lean::is_scalar(x_26)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_26;
 lean::cnstr_set_tag(x_26, 0);
}
lean::cnstr_set(x_39, 0, x_36);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_32, 0);
lean::inc(x_40);
lean::dec(x_32);
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
if (lean::is_scalar(x_11)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_11;
}
lean::cnstr_set(x_48, 0, x_27);
lean::cnstr_set(x_48, 1, x_43);
if (lean::is_scalar(x_31)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_31;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
if (lean::is_scalar(x_26)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_26;
}
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(obj* x_0) {
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
x_10 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(x_4);
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
obj* _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_match_fn");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::inc(x_1);
x_15 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(x_12, x_1, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_22 = x_15;
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_36; 
x_24 = lean::cnstr_get(x_15, 0);
lean::inc(x_24);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_26 = x_15;
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 x_31 = x_24;
}
x_32 = lean::cnstr_get(x_7, 2);
lean::inc(x_32);
lean::dec(x_7);
lean::inc(x_1);
x_36 = l_lean_elaborator_to__pexpr___main(x_32, x_1, x_29);
if (lean::obj_tag(x_36) == 0)
{
obj* x_42; obj* x_45; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_27);
lean::dec(x_31);
x_42 = lean::cnstr_get(x_36, 0);
lean::inc(x_42);
lean::dec(x_36);
if (lean::is_scalar(x_26)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_26;
 lean::cnstr_set_tag(x_26, 0);
}
lean::cnstr_set(x_45, 0, x_42);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_51; obj* x_53; obj* x_54; 
x_46 = lean::cnstr_get(x_36, 0);
lean::inc(x_46);
lean::dec(x_36);
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
x_54 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_9, x_1, x_51);
if (lean::obj_tag(x_54) == 0)
{
obj* x_60; obj* x_63; 
lean::dec(x_11);
lean::dec(x_27);
lean::dec(x_31);
lean::dec(x_49);
lean::dec(x_53);
x_60 = lean::cnstr_get(x_54, 0);
lean::inc(x_60);
lean::dec(x_54);
if (lean::is_scalar(x_26)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_26;
 lean::cnstr_set_tag(x_26, 0);
}
lean::cnstr_set(x_63, 0, x_60);
return x_63;
}
else
{
obj* x_64; obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_64 = lean::cnstr_get(x_54, 0);
lean::inc(x_64);
lean::dec(x_54);
x_67 = lean::cnstr_get(x_64, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_64, 1);
lean::inc(x_69);
if (lean::is_shared(x_64)) {
 lean::dec(x_64);
 x_71 = lean::box(0);
} else {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_71 = x_64;
}
if (lean::is_scalar(x_31)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_31;
}
lean::cnstr_set(x_72, 0, x_27);
lean::cnstr_set(x_72, 1, x_49);
x_73 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1;
lean::inc(x_73);
if (lean::is_scalar(x_53)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_53;
}
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set(x_75, 1, x_72);
if (lean::is_scalar(x_11)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_11;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_67);
if (lean::is_scalar(x_71)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_71;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_69);
if (lean::is_scalar(x_26)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_26;
}
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_16; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
lean::inc(x_1);
x_16 = l_lean_elaborator_to__pexpr___main(x_12, x_1, x_2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_22 = x_16;
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; 
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_26 = x_16;
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 x_31 = x_24;
}
x_32 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_9, x_1, x_29);
if (lean::obj_tag(x_32) == 0)
{
obj* x_36; obj* x_39; 
lean::dec(x_11);
lean::dec(x_27);
lean::dec(x_31);
x_36 = lean::cnstr_get(x_32, 0);
lean::inc(x_36);
lean::dec(x_32);
if (lean::is_scalar(x_26)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_26;
 lean::cnstr_set_tag(x_26, 0);
}
lean::cnstr_set(x_39, 0, x_36);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_32, 0);
lean::inc(x_40);
lean::dec(x_32);
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
if (lean::is_scalar(x_11)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_11;
}
lean::cnstr_set(x_48, 0, x_27);
lean::cnstr_set(x_48, 1, x_43);
if (lean::is_scalar(x_31)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_31;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
if (lean::is_scalar(x_26)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_26;
}
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_9; uint8 x_10; 
lean::dec(x_6);
x_9 = 1;
x_10 = l_coe__decidable__eq(x_9);
if (x_10 == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_4);
lean::dec(x_2);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_0);
return x_14;
}
else
{
obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_0);
x_16 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_4);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_21 = x_16;
}
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_2);
lean::cnstr_set(x_22, 1, x_17);
if (lean::is_scalar(x_21)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_21;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8 x_25; uint8 x_26; 
lean::dec(x_6);
x_25 = 0;
x_26 = l_coe__decidable__eq(x_25);
if (x_26 == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_4);
lean::dec(x_2);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_0);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_0);
x_32 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_4);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 x_37 = x_32;
}
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_2);
lean::cnstr_set(x_38, 1, x_33);
if (lean::is_scalar(x_37)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_37;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_35);
return x_39;
}
}
}
}
}
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_9; uint8 x_10; 
lean::dec(x_6);
x_9 = 0;
x_10 = l_coe__decidable__eq(x_9);
if (x_10 == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_4);
lean::dec(x_2);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_0);
return x_14;
}
else
{
obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_0);
x_16 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_4);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_21 = x_16;
}
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_2);
lean::cnstr_set(x_22, 1, x_17);
if (lean::is_scalar(x_21)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_21;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_6, 0);
lean::inc(x_24);
lean::dec(x_6);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_30; uint8 x_31; 
x_30 = 0;
x_31 = l_coe__decidable__eq(x_30);
if (x_31 == 0)
{
obj* x_34; obj* x_35; 
lean::dec(x_4);
lean::dec(x_2);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_0);
return x_35;
}
else
{
obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_37 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_4);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
if (lean::is_shared(x_37)) {
 lean::dec(x_37);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 x_42 = x_37;
}
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_2);
lean::cnstr_set(x_43, 1, x_38);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_40);
return x_44;
}
}
else
{
uint8 x_46; uint8 x_47; 
lean::dec(x_27);
x_46 = 1;
x_47 = l_coe__decidable__eq(x_46);
if (x_47 == 0)
{
obj* x_50; obj* x_51; 
lean::dec(x_4);
lean::dec(x_2);
x_50 = lean::box(0);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_0);
return x_51;
}
else
{
obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_0);
x_53 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_4);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_58 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 lean::cnstr_release(x_53, 1);
 x_58 = x_53;
}
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_2);
lean::cnstr_set(x_59, 1, x_54);
if (lean::is_scalar(x_58)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_58;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_56);
return x_60;
}
}
}
}
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("field");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("to_pexpr: unreachable");
return x_0;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_20; obj* x_23; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::inc(x_2);
x_23 = l_lean_elaborator_to__pexpr___main(x_20, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_17);
x_29 = lean::cnstr_get(x_23, 0);
lean::inc(x_29);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
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
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_35 = x_23;
}
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
if (lean::is_shared(x_33)) {
 lean::dec(x_33);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_40 = x_33;
}
x_41 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_11, x_2, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_46; obj* x_49; 
lean::dec(x_13);
lean::dec(x_36);
lean::dec(x_17);
lean::dec(x_40);
x_46 = lean::cnstr_get(x_41, 0);
lean::inc(x_46);
lean::dec(x_41);
if (lean::is_scalar(x_35)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_49, 0, x_46);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
lean::dec(x_41);
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
lean::dec(x_50);
x_58 = lean::box(0);
x_59 = lean::cnstr_get(x_17, 0);
lean::inc(x_59);
lean::dec(x_17);
x_62 = l_lean_elaborator_mangle__ident(x_59);
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
lean::inc(x_63);
x_65 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_66 = lean_expr_mk_mdata(x_65, x_36);
if (lean::is_scalar(x_13)) {
 x_67 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_67 = x_13;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_53);
if (lean::is_scalar(x_40)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_40;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_55);
if (lean::is_scalar(x_35)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_35;
}
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
obj* x_71; obj* x_75; 
lean::dec(x_14);
x_71 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_71);
lean::inc(x_0);
x_75 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_71, x_2, x_3);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_80 = lean::cnstr_get(x_75, 0);
lean::inc(x_80);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_82 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_82 = x_75;
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
return x_83;
}
else
{
obj* x_84; obj* x_86; obj* x_87; obj* x_89; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_75, 0);
lean::inc(x_84);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_86 = x_75;
}
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
if (lean::is_shared(x_84)) {
 lean::dec(x_84);
 x_91 = lean::box(0);
} else {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_91 = x_84;
}
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_11, x_2, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_96; obj* x_99; 
lean::dec(x_13);
lean::dec(x_91);
lean::dec(x_87);
x_96 = lean::cnstr_get(x_92, 0);
lean::inc(x_96);
lean::dec(x_92);
if (lean::is_scalar(x_86)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_86;
 lean::cnstr_set_tag(x_86, 0);
}
lean::cnstr_set(x_99, 0, x_96);
return x_99;
}
else
{
obj* x_100; obj* x_103; obj* x_105; obj* x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_92, 0);
lean::inc(x_100);
lean::dec(x_92);
x_103 = lean::cnstr_get(x_100, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_100, 1);
lean::inc(x_105);
lean::dec(x_100);
if (lean::is_scalar(x_13)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_13;
}
lean::cnstr_set(x_108, 0, x_87);
lean::cnstr_set(x_108, 1, x_103);
if (lean::is_scalar(x_91)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_91;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_105);
if (lean::is_scalar(x_86)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_86;
}
lean::cnstr_set(x_110, 0, x_109);
return x_110;
}
}
}
}
}
}
obj* _init_l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean_expr_mk_sort(x_0);
return x_1;
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_22; 
lean::dec(x_14);
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_18);
lean::inc(x_0);
x_22 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_29 = x_22;
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
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_33 = x_22;
}
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_38 = x_31;
}
x_39 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_11, x_2, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_46; 
lean::dec(x_13);
lean::dec(x_34);
lean::dec(x_38);
x_43 = lean::cnstr_get(x_39, 0);
lean::inc(x_43);
lean::dec(x_39);
if (lean::is_scalar(x_33)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_33;
 lean::cnstr_set_tag(x_33, 0);
}
lean::cnstr_set(x_46, 0, x_43);
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_57; 
x_47 = lean::cnstr_get(x_39, 0);
lean::inc(x_47);
lean::dec(x_39);
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
lean::dec(x_47);
if (lean::is_scalar(x_13)) {
 x_55 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_55 = x_13;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_50);
if (lean::is_scalar(x_38)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_38;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_52);
if (lean::is_scalar(x_33)) {
 x_57 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_57 = x_33;
}
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_14, 0);
lean::inc(x_58);
lean::dec(x_14);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
if (lean::obj_tag(x_61) == 0)
{
obj* x_64; obj* x_68; 
x_64 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_64);
lean::inc(x_0);
x_68 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_64, x_2, x_3);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_73 = lean::cnstr_get(x_68, 0);
lean::inc(x_73);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_75 = x_68;
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
return x_76;
}
else
{
obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; 
x_77 = lean::cnstr_get(x_68, 0);
lean::inc(x_77);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_79 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_79 = x_68;
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
}
x_85 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_11, x_2, x_82);
if (lean::obj_tag(x_85) == 0)
{
obj* x_89; obj* x_92; 
lean::dec(x_13);
lean::dec(x_80);
lean::dec(x_84);
x_89 = lean::cnstr_get(x_85, 0);
lean::inc(x_89);
lean::dec(x_85);
if (lean::is_scalar(x_79)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_79;
 lean::cnstr_set_tag(x_79, 0);
}
lean::cnstr_set(x_92, 0, x_89);
return x_92;
}
else
{
obj* x_93; obj* x_96; obj* x_98; obj* x_101; obj* x_102; obj* x_103; 
x_93 = lean::cnstr_get(x_85, 0);
lean::inc(x_93);
lean::dec(x_85);
x_96 = lean::cnstr_get(x_93, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_93, 1);
lean::inc(x_98);
lean::dec(x_93);
if (lean::is_scalar(x_13)) {
 x_101 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_101 = x_13;
}
lean::cnstr_set(x_101, 0, x_80);
lean::cnstr_set(x_101, 1, x_96);
if (lean::is_scalar(x_84)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_84;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_98);
if (lean::is_scalar(x_79)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_79;
}
lean::cnstr_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
obj* x_104; obj* x_108; 
x_104 = lean::cnstr_get(x_61, 0);
lean::inc(x_104);
lean::dec(x_61);
lean::inc(x_2);
x_108 = l_lean_elaborator_to__pexpr___main(x_104, x_2, x_3);
if (lean::obj_tag(x_108) == 0)
{
obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_113 = lean::cnstr_get(x_108, 0);
lean::inc(x_113);
if (lean::is_shared(x_108)) {
 lean::dec(x_108);
 x_115 = lean::box(0);
} else {
 lean::cnstr_release(x_108, 0);
 x_115 = x_108;
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
obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
x_117 = lean::cnstr_get(x_108, 0);
lean::inc(x_117);
if (lean::is_shared(x_108)) {
 lean::dec(x_108);
 x_119 = lean::box(0);
} else {
 lean::cnstr_release(x_108, 0);
 x_119 = x_108;
}
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
if (lean::is_shared(x_117)) {
 lean::dec(x_117);
 x_124 = lean::box(0);
} else {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_124 = x_117;
}
x_125 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_11, x_2, x_122);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_132; 
lean::dec(x_13);
lean::dec(x_120);
lean::dec(x_124);
x_129 = lean::cnstr_get(x_125, 0);
lean::inc(x_129);
lean::dec(x_125);
if (lean::is_scalar(x_119)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_119;
 lean::cnstr_set_tag(x_119, 0);
}
lean::cnstr_set(x_132, 0, x_129);
return x_132;
}
else
{
obj* x_133; obj* x_136; obj* x_138; obj* x_141; obj* x_142; obj* x_143; 
x_133 = lean::cnstr_get(x_125, 0);
lean::inc(x_133);
lean::dec(x_125);
x_136 = lean::cnstr_get(x_133, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_133, 1);
lean::inc(x_138);
lean::dec(x_133);
if (lean::is_scalar(x_13)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_13;
}
lean::cnstr_set(x_141, 0, x_120);
lean::cnstr_set(x_141, 1, x_136);
if (lean::is_scalar(x_124)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_124;
}
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_138);
if (lean::is_scalar(x_119)) {
 x_143 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_143 = x_119;
}
lean::cnstr_set(x_143, 0, x_142);
return x_143;
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_20; obj* x_23; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::inc(x_2);
x_23 = l_lean_elaborator_to__pexpr___main(x_20, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_17);
x_29 = lean::cnstr_get(x_23, 0);
lean::inc(x_29);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
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
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_35 = x_23;
}
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
if (lean::is_shared(x_33)) {
 lean::dec(x_33);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_40 = x_33;
}
x_41 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_11, x_2, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_46; obj* x_49; 
lean::dec(x_13);
lean::dec(x_36);
lean::dec(x_17);
lean::dec(x_40);
x_46 = lean::cnstr_get(x_41, 0);
lean::inc(x_46);
lean::dec(x_41);
if (lean::is_scalar(x_35)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_49, 0, x_46);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
lean::dec(x_41);
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
lean::dec(x_50);
x_58 = lean::box(0);
x_59 = lean::cnstr_get(x_17, 0);
lean::inc(x_59);
lean::dec(x_17);
x_62 = l_lean_elaborator_mangle__ident(x_59);
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
lean::inc(x_63);
x_65 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_66 = lean_expr_mk_mdata(x_65, x_36);
if (lean::is_scalar(x_13)) {
 x_67 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_67 = x_13;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_53);
if (lean::is_scalar(x_40)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_40;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_55);
if (lean::is_scalar(x_35)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_35;
}
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
obj* x_71; obj* x_75; 
lean::dec(x_14);
x_71 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_71);
lean::inc(x_0);
x_75 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_71, x_2, x_3);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_80 = lean::cnstr_get(x_75, 0);
lean::inc(x_80);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_82 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_82 = x_75;
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
return x_83;
}
else
{
obj* x_84; obj* x_86; obj* x_87; obj* x_89; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_75, 0);
lean::inc(x_84);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_86 = x_75;
}
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
if (lean::is_shared(x_84)) {
 lean::dec(x_84);
 x_91 = lean::box(0);
} else {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_91 = x_84;
}
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_11, x_2, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_96; obj* x_99; 
lean::dec(x_13);
lean::dec(x_91);
lean::dec(x_87);
x_96 = lean::cnstr_get(x_92, 0);
lean::inc(x_96);
lean::dec(x_92);
if (lean::is_scalar(x_86)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_86;
 lean::cnstr_set_tag(x_86, 0);
}
lean::cnstr_set(x_99, 0, x_96);
return x_99;
}
else
{
obj* x_100; obj* x_103; obj* x_105; obj* x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_92, 0);
lean::inc(x_100);
lean::dec(x_92);
x_103 = lean::cnstr_get(x_100, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_100, 1);
lean::inc(x_105);
lean::dec(x_100);
if (lean::is_scalar(x_13)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_13;
}
lean::cnstr_set(x_108, 0, x_87);
lean::cnstr_set(x_108, 1, x_103);
if (lean::is_scalar(x_91)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_91;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_105);
if (lean::is_scalar(x_86)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_86;
}
lean::cnstr_set(x_110, 0, x_109);
return x_110;
}
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_22; 
lean::dec(x_14);
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_18);
lean::inc(x_0);
x_22 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_29 = x_22;
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
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_33 = x_22;
}
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_38 = x_31;
}
x_39 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_11, x_2, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_46; 
lean::dec(x_13);
lean::dec(x_34);
lean::dec(x_38);
x_43 = lean::cnstr_get(x_39, 0);
lean::inc(x_43);
lean::dec(x_39);
if (lean::is_scalar(x_33)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_33;
 lean::cnstr_set_tag(x_33, 0);
}
lean::cnstr_set(x_46, 0, x_43);
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_57; 
x_47 = lean::cnstr_get(x_39, 0);
lean::inc(x_47);
lean::dec(x_39);
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
lean::dec(x_47);
if (lean::is_scalar(x_13)) {
 x_55 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_55 = x_13;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_50);
if (lean::is_scalar(x_38)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_38;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_52);
if (lean::is_scalar(x_33)) {
 x_57 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_57 = x_33;
}
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_14, 0);
lean::inc(x_58);
lean::dec(x_14);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
if (lean::obj_tag(x_61) == 0)
{
obj* x_64; obj* x_68; 
x_64 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_64);
lean::inc(x_0);
x_68 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_64, x_2, x_3);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_73 = lean::cnstr_get(x_68, 0);
lean::inc(x_73);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_75 = x_68;
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
return x_76;
}
else
{
obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; 
x_77 = lean::cnstr_get(x_68, 0);
lean::inc(x_77);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_79 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_79 = x_68;
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
}
x_85 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_11, x_2, x_82);
if (lean::obj_tag(x_85) == 0)
{
obj* x_89; obj* x_92; 
lean::dec(x_13);
lean::dec(x_80);
lean::dec(x_84);
x_89 = lean::cnstr_get(x_85, 0);
lean::inc(x_89);
lean::dec(x_85);
if (lean::is_scalar(x_79)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_79;
 lean::cnstr_set_tag(x_79, 0);
}
lean::cnstr_set(x_92, 0, x_89);
return x_92;
}
else
{
obj* x_93; obj* x_96; obj* x_98; obj* x_101; obj* x_102; obj* x_103; 
x_93 = lean::cnstr_get(x_85, 0);
lean::inc(x_93);
lean::dec(x_85);
x_96 = lean::cnstr_get(x_93, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_93, 1);
lean::inc(x_98);
lean::dec(x_93);
if (lean::is_scalar(x_13)) {
 x_101 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_101 = x_13;
}
lean::cnstr_set(x_101, 0, x_80);
lean::cnstr_set(x_101, 1, x_96);
if (lean::is_scalar(x_84)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_84;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_98);
if (lean::is_scalar(x_79)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_79;
}
lean::cnstr_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
obj* x_104; obj* x_108; 
x_104 = lean::cnstr_get(x_61, 0);
lean::inc(x_104);
lean::dec(x_61);
lean::inc(x_2);
x_108 = l_lean_elaborator_to__pexpr___main(x_104, x_2, x_3);
if (lean::obj_tag(x_108) == 0)
{
obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_113 = lean::cnstr_get(x_108, 0);
lean::inc(x_113);
if (lean::is_shared(x_108)) {
 lean::dec(x_108);
 x_115 = lean::box(0);
} else {
 lean::cnstr_release(x_108, 0);
 x_115 = x_108;
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
obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
x_117 = lean::cnstr_get(x_108, 0);
lean::inc(x_117);
if (lean::is_shared(x_108)) {
 lean::dec(x_108);
 x_119 = lean::box(0);
} else {
 lean::cnstr_release(x_108, 0);
 x_119 = x_108;
}
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
if (lean::is_shared(x_117)) {
 lean::dec(x_117);
 x_124 = lean::box(0);
} else {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_124 = x_117;
}
x_125 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_11, x_2, x_122);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_132; 
lean::dec(x_13);
lean::dec(x_120);
lean::dec(x_124);
x_129 = lean::cnstr_get(x_125, 0);
lean::inc(x_129);
lean::dec(x_125);
if (lean::is_scalar(x_119)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_119;
 lean::cnstr_set_tag(x_119, 0);
}
lean::cnstr_set(x_132, 0, x_129);
return x_132;
}
else
{
obj* x_133; obj* x_136; obj* x_138; obj* x_141; obj* x_142; obj* x_143; 
x_133 = lean::cnstr_get(x_125, 0);
lean::inc(x_133);
lean::dec(x_125);
x_136 = lean::cnstr_get(x_133, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_133, 1);
lean::inc(x_138);
lean::dec(x_133);
if (lean::is_scalar(x_13)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_13;
}
lean::cnstr_set(x_141, 0, x_120);
lean::cnstr_set(x_141, 1, x_136);
if (lean::is_scalar(x_124)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_124;
}
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_138);
if (lean::is_scalar(x_119)) {
 x_143 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_143 = x_119;
}
lean::cnstr_set(x_143, 0, x_142);
return x_143;
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_20; obj* x_23; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::inc(x_2);
x_23 = l_lean_elaborator_to__pexpr___main(x_20, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_17);
x_29 = lean::cnstr_get(x_23, 0);
lean::inc(x_29);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
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
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_35 = x_23;
}
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
if (lean::is_shared(x_33)) {
 lean::dec(x_33);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_40 = x_33;
}
x_41 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_11, x_2, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_46; obj* x_49; 
lean::dec(x_13);
lean::dec(x_36);
lean::dec(x_17);
lean::dec(x_40);
x_46 = lean::cnstr_get(x_41, 0);
lean::inc(x_46);
lean::dec(x_41);
if (lean::is_scalar(x_35)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_49, 0, x_46);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
lean::dec(x_41);
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
lean::dec(x_50);
x_58 = lean::box(0);
x_59 = lean::cnstr_get(x_17, 0);
lean::inc(x_59);
lean::dec(x_17);
x_62 = l_lean_elaborator_mangle__ident(x_59);
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
lean::inc(x_63);
x_65 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_66 = lean_expr_mk_mdata(x_65, x_36);
if (lean::is_scalar(x_13)) {
 x_67 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_67 = x_13;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_53);
if (lean::is_scalar(x_40)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_40;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_55);
if (lean::is_scalar(x_35)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_35;
}
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
obj* x_71; obj* x_75; 
lean::dec(x_14);
x_71 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_71);
lean::inc(x_0);
x_75 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_71, x_2, x_3);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_80 = lean::cnstr_get(x_75, 0);
lean::inc(x_80);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_82 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_82 = x_75;
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
return x_83;
}
else
{
obj* x_84; obj* x_86; obj* x_87; obj* x_89; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_75, 0);
lean::inc(x_84);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_86 = x_75;
}
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
if (lean::is_shared(x_84)) {
 lean::dec(x_84);
 x_91 = lean::box(0);
} else {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_91 = x_84;
}
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_11, x_2, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_96; obj* x_99; 
lean::dec(x_13);
lean::dec(x_91);
lean::dec(x_87);
x_96 = lean::cnstr_get(x_92, 0);
lean::inc(x_96);
lean::dec(x_92);
if (lean::is_scalar(x_86)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_86;
 lean::cnstr_set_tag(x_86, 0);
}
lean::cnstr_set(x_99, 0, x_96);
return x_99;
}
else
{
obj* x_100; obj* x_103; obj* x_105; obj* x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_92, 0);
lean::inc(x_100);
lean::dec(x_92);
x_103 = lean::cnstr_get(x_100, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_100, 1);
lean::inc(x_105);
lean::dec(x_100);
if (lean::is_scalar(x_13)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_13;
}
lean::cnstr_set(x_108, 0, x_87);
lean::cnstr_set(x_108, 1, x_103);
if (lean::is_scalar(x_91)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_91;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_105);
if (lean::is_scalar(x_86)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_86;
}
lean::cnstr_set(x_110, 0, x_109);
return x_110;
}
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_22; 
lean::dec(x_14);
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_18);
lean::inc(x_0);
x_22 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_29 = x_22;
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
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_33 = x_22;
}
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_38 = x_31;
}
x_39 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_11, x_2, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_46; 
lean::dec(x_13);
lean::dec(x_34);
lean::dec(x_38);
x_43 = lean::cnstr_get(x_39, 0);
lean::inc(x_43);
lean::dec(x_39);
if (lean::is_scalar(x_33)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_33;
 lean::cnstr_set_tag(x_33, 0);
}
lean::cnstr_set(x_46, 0, x_43);
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_57; 
x_47 = lean::cnstr_get(x_39, 0);
lean::inc(x_47);
lean::dec(x_39);
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
lean::dec(x_47);
if (lean::is_scalar(x_13)) {
 x_55 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_55 = x_13;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_50);
if (lean::is_scalar(x_38)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_38;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_52);
if (lean::is_scalar(x_33)) {
 x_57 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_57 = x_33;
}
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_14, 0);
lean::inc(x_58);
lean::dec(x_14);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
if (lean::obj_tag(x_61) == 0)
{
obj* x_64; obj* x_68; 
x_64 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_64);
lean::inc(x_0);
x_68 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_64, x_2, x_3);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_73 = lean::cnstr_get(x_68, 0);
lean::inc(x_73);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_75 = x_68;
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
return x_76;
}
else
{
obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; 
x_77 = lean::cnstr_get(x_68, 0);
lean::inc(x_77);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_79 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_79 = x_68;
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
}
x_85 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_11, x_2, x_82);
if (lean::obj_tag(x_85) == 0)
{
obj* x_89; obj* x_92; 
lean::dec(x_13);
lean::dec(x_80);
lean::dec(x_84);
x_89 = lean::cnstr_get(x_85, 0);
lean::inc(x_89);
lean::dec(x_85);
if (lean::is_scalar(x_79)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_79;
 lean::cnstr_set_tag(x_79, 0);
}
lean::cnstr_set(x_92, 0, x_89);
return x_92;
}
else
{
obj* x_93; obj* x_96; obj* x_98; obj* x_101; obj* x_102; obj* x_103; 
x_93 = lean::cnstr_get(x_85, 0);
lean::inc(x_93);
lean::dec(x_85);
x_96 = lean::cnstr_get(x_93, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_93, 1);
lean::inc(x_98);
lean::dec(x_93);
if (lean::is_scalar(x_13)) {
 x_101 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_101 = x_13;
}
lean::cnstr_set(x_101, 0, x_80);
lean::cnstr_set(x_101, 1, x_96);
if (lean::is_scalar(x_84)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_84;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_98);
if (lean::is_scalar(x_79)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_79;
}
lean::cnstr_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
obj* x_104; obj* x_108; 
x_104 = lean::cnstr_get(x_61, 0);
lean::inc(x_104);
lean::dec(x_61);
lean::inc(x_2);
x_108 = l_lean_elaborator_to__pexpr___main(x_104, x_2, x_3);
if (lean::obj_tag(x_108) == 0)
{
obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_113 = lean::cnstr_get(x_108, 0);
lean::inc(x_113);
if (lean::is_shared(x_108)) {
 lean::dec(x_108);
 x_115 = lean::box(0);
} else {
 lean::cnstr_release(x_108, 0);
 x_115 = x_108;
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
obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
x_117 = lean::cnstr_get(x_108, 0);
lean::inc(x_117);
if (lean::is_shared(x_108)) {
 lean::dec(x_108);
 x_119 = lean::box(0);
} else {
 lean::cnstr_release(x_108, 0);
 x_119 = x_108;
}
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
if (lean::is_shared(x_117)) {
 lean::dec(x_117);
 x_124 = lean::box(0);
} else {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_124 = x_117;
}
x_125 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_11, x_2, x_122);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_132; 
lean::dec(x_13);
lean::dec(x_120);
lean::dec(x_124);
x_129 = lean::cnstr_get(x_125, 0);
lean::inc(x_129);
lean::dec(x_125);
if (lean::is_scalar(x_119)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_119;
 lean::cnstr_set_tag(x_119, 0);
}
lean::cnstr_set(x_132, 0, x_129);
return x_132;
}
else
{
obj* x_133; obj* x_136; obj* x_138; obj* x_141; obj* x_142; obj* x_143; 
x_133 = lean::cnstr_get(x_125, 0);
lean::inc(x_133);
lean::dec(x_125);
x_136 = lean::cnstr_get(x_133, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_133, 1);
lean::inc(x_138);
lean::dec(x_133);
if (lean::is_scalar(x_13)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_13;
}
lean::cnstr_set(x_141, 0, x_120);
lean::cnstr_set(x_141, 1, x_136);
if (lean::is_scalar(x_124)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_124;
}
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_138);
if (lean::is_scalar(x_119)) {
 x_143 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_143 = x_119;
}
lean::cnstr_set(x_143, 0, x_142);
return x_143;
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_20; obj* x_23; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::inc(x_2);
x_23 = l_lean_elaborator_to__pexpr___main(x_20, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_17);
x_29 = lean::cnstr_get(x_23, 0);
lean::inc(x_29);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
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
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_35 = x_23;
}
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
if (lean::is_shared(x_33)) {
 lean::dec(x_33);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_40 = x_33;
}
x_41 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_11, x_2, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_46; obj* x_49; 
lean::dec(x_13);
lean::dec(x_36);
lean::dec(x_17);
lean::dec(x_40);
x_46 = lean::cnstr_get(x_41, 0);
lean::inc(x_46);
lean::dec(x_41);
if (lean::is_scalar(x_35)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_49, 0, x_46);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
lean::dec(x_41);
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
lean::dec(x_50);
x_58 = lean::box(0);
x_59 = lean::cnstr_get(x_17, 0);
lean::inc(x_59);
lean::dec(x_17);
x_62 = l_lean_elaborator_mangle__ident(x_59);
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
lean::inc(x_63);
x_65 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_66 = lean_expr_mk_mdata(x_65, x_36);
if (lean::is_scalar(x_13)) {
 x_67 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_67 = x_13;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_53);
if (lean::is_scalar(x_40)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_40;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_55);
if (lean::is_scalar(x_35)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_35;
}
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
obj* x_71; obj* x_75; 
lean::dec(x_14);
x_71 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_71);
lean::inc(x_0);
x_75 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_71, x_2, x_3);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_80 = lean::cnstr_get(x_75, 0);
lean::inc(x_80);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_82 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_82 = x_75;
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
return x_83;
}
else
{
obj* x_84; obj* x_86; obj* x_87; obj* x_89; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_75, 0);
lean::inc(x_84);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_86 = x_75;
}
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
if (lean::is_shared(x_84)) {
 lean::dec(x_84);
 x_91 = lean::box(0);
} else {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_91 = x_84;
}
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_11, x_2, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_96; obj* x_99; 
lean::dec(x_13);
lean::dec(x_91);
lean::dec(x_87);
x_96 = lean::cnstr_get(x_92, 0);
lean::inc(x_96);
lean::dec(x_92);
if (lean::is_scalar(x_86)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_86;
 lean::cnstr_set_tag(x_86, 0);
}
lean::cnstr_set(x_99, 0, x_96);
return x_99;
}
else
{
obj* x_100; obj* x_103; obj* x_105; obj* x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_92, 0);
lean::inc(x_100);
lean::dec(x_92);
x_103 = lean::cnstr_get(x_100, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_100, 1);
lean::inc(x_105);
lean::dec(x_100);
if (lean::is_scalar(x_13)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_13;
}
lean::cnstr_set(x_108, 0, x_87);
lean::cnstr_set(x_108, 1, x_103);
if (lean::is_scalar(x_91)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_91;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_105);
if (lean::is_scalar(x_86)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_86;
}
lean::cnstr_set(x_110, 0, x_109);
return x_110;
}
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_22; 
lean::dec(x_14);
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_18);
lean::inc(x_0);
x_22 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_29 = x_22;
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
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_33 = x_22;
}
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_38 = x_31;
}
x_39 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_11, x_2, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_46; 
lean::dec(x_13);
lean::dec(x_34);
lean::dec(x_38);
x_43 = lean::cnstr_get(x_39, 0);
lean::inc(x_43);
lean::dec(x_39);
if (lean::is_scalar(x_33)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_33;
 lean::cnstr_set_tag(x_33, 0);
}
lean::cnstr_set(x_46, 0, x_43);
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_57; 
x_47 = lean::cnstr_get(x_39, 0);
lean::inc(x_47);
lean::dec(x_39);
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
lean::dec(x_47);
if (lean::is_scalar(x_13)) {
 x_55 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_55 = x_13;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_50);
if (lean::is_scalar(x_38)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_38;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_52);
if (lean::is_scalar(x_33)) {
 x_57 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_57 = x_33;
}
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_14, 0);
lean::inc(x_58);
lean::dec(x_14);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
if (lean::obj_tag(x_61) == 0)
{
obj* x_64; obj* x_68; 
x_64 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_64);
lean::inc(x_0);
x_68 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_64, x_2, x_3);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_73 = lean::cnstr_get(x_68, 0);
lean::inc(x_73);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_75 = x_68;
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
return x_76;
}
else
{
obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; 
x_77 = lean::cnstr_get(x_68, 0);
lean::inc(x_77);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_79 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_79 = x_68;
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
}
x_85 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_11, x_2, x_82);
if (lean::obj_tag(x_85) == 0)
{
obj* x_89; obj* x_92; 
lean::dec(x_13);
lean::dec(x_80);
lean::dec(x_84);
x_89 = lean::cnstr_get(x_85, 0);
lean::inc(x_89);
lean::dec(x_85);
if (lean::is_scalar(x_79)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_79;
 lean::cnstr_set_tag(x_79, 0);
}
lean::cnstr_set(x_92, 0, x_89);
return x_92;
}
else
{
obj* x_93; obj* x_96; obj* x_98; obj* x_101; obj* x_102; obj* x_103; 
x_93 = lean::cnstr_get(x_85, 0);
lean::inc(x_93);
lean::dec(x_85);
x_96 = lean::cnstr_get(x_93, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_93, 1);
lean::inc(x_98);
lean::dec(x_93);
if (lean::is_scalar(x_13)) {
 x_101 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_101 = x_13;
}
lean::cnstr_set(x_101, 0, x_80);
lean::cnstr_set(x_101, 1, x_96);
if (lean::is_scalar(x_84)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_84;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_98);
if (lean::is_scalar(x_79)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_79;
}
lean::cnstr_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
obj* x_104; obj* x_108; 
x_104 = lean::cnstr_get(x_61, 0);
lean::inc(x_104);
lean::dec(x_61);
lean::inc(x_2);
x_108 = l_lean_elaborator_to__pexpr___main(x_104, x_2, x_3);
if (lean::obj_tag(x_108) == 0)
{
obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_113 = lean::cnstr_get(x_108, 0);
lean::inc(x_113);
if (lean::is_shared(x_108)) {
 lean::dec(x_108);
 x_115 = lean::box(0);
} else {
 lean::cnstr_release(x_108, 0);
 x_115 = x_108;
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
obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
x_117 = lean::cnstr_get(x_108, 0);
lean::inc(x_117);
if (lean::is_shared(x_108)) {
 lean::dec(x_108);
 x_119 = lean::box(0);
} else {
 lean::cnstr_release(x_108, 0);
 x_119 = x_108;
}
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
if (lean::is_shared(x_117)) {
 lean::dec(x_117);
 x_124 = lean::box(0);
} else {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_124 = x_117;
}
x_125 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_11, x_2, x_122);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_132; 
lean::dec(x_13);
lean::dec(x_120);
lean::dec(x_124);
x_129 = lean::cnstr_get(x_125, 0);
lean::inc(x_129);
lean::dec(x_125);
if (lean::is_scalar(x_119)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_119;
 lean::cnstr_set_tag(x_119, 0);
}
lean::cnstr_set(x_132, 0, x_129);
return x_132;
}
else
{
obj* x_133; obj* x_136; obj* x_138; obj* x_141; obj* x_142; obj* x_143; 
x_133 = lean::cnstr_get(x_125, 0);
lean::inc(x_133);
lean::dec(x_125);
x_136 = lean::cnstr_get(x_133, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_133, 1);
lean::inc(x_138);
lean::dec(x_133);
if (lean::is_scalar(x_13)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_13;
}
lean::cnstr_set(x_141, 0, x_120);
lean::cnstr_set(x_141, 1, x_136);
if (lean::is_scalar(x_124)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_124;
}
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_138);
if (lean::is_scalar(x_119)) {
 x_143 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_143 = x_119;
}
lean::cnstr_set(x_143, 0, x_142);
return x_143;
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
lean::inc(x_1);
x_13 = l_lean_elaborator_to__pexpr___main(x_7, x_1, x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
}
x_29 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_36; 
lean::dec(x_11);
lean::dec(x_24);
lean::dec(x_28);
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
lean::dec(x_29);
if (lean::is_scalar(x_23)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_23;
 lean::cnstr_set_tag(x_23, 0);
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
if (lean::is_scalar(x_11)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_11;
}
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_28)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_28;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_23)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_23;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(obj* x_0) {
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
x_10 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_4);
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
obj* l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
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
x_12 = lean::box(0);
x_13 = lean_name_mk_numeral(x_12, x_7);
x_14 = l_lean_kvmap_set__name(x_0, x_13, x_9);
x_0 = x_14;
x_1 = x_4;
goto _start;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
lean::inc(x_1);
x_13 = l_lean_elaborator_to__level___main(x_7, x_1, x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
}
x_29 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_36; 
lean::dec(x_11);
lean::dec(x_24);
lean::dec(x_28);
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
lean::dec(x_29);
if (lean::is_scalar(x_23)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_23;
 lean::cnstr_set_tag(x_23, 0);
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
if (lean::is_scalar(x_11)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_11;
}
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_28)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_28;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_23)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_23;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
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
x_12 = lean::box(0);
x_13 = lean_name_mk_numeral(x_12, x_7);
x_14 = l_lean_kvmap_set__name(x_0, x_13, x_9);
x_0 = x_14;
x_1 = x_4;
goto _start;
}
}
}
obj* l_lean_elaborator_to__pexpr___main___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_to__pexpr___main___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("to_pexpr: unexpected: ");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("app");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("column");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("row");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed choice");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("choice");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("ident_univs");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("lambda");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__9() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("pi");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__10() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("sort_app");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__11() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("anonymous_constructor");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__12() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("hole");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__13() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("have");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__14() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("show");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__15() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("let");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__16() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("projection");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__17() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("explicit");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__18() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("inaccessible");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__19() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("borrowed");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__20() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("choice");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__21() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("struct_inst");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__22() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("match");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__23() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("to_pexpr: unexpected node: ");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__24() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("match");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__25() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("structure instance");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__26() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("catchall");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__27() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_to__pexpr___main___lambda__1), 1, 0);
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__28() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_mangle__ident), 1, 0);
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__29() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("struct");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__30() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected item in structure instance notation");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__31() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("NOT_A_STRING");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__32() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("borrowed");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__33() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("innaccessible");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__34() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@@");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__35() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("field_notation");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__36() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed let");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__37() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__38() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean_expr_mk_bvar(x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__39() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("show");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__40() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("have");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__41() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_to__pexpr___main___lambda__2), 1, 0);
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__42() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_lean_elaborator_dummy;
lean::inc(x_1);
x_3 = lean_expr_mk_mvar(x_0, x_1);
return x_3;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__43() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("anonymous_constructor");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__44() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = level_mk_succ(x_0);
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__45() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed pi");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__46() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed lambda");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__47() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("annotation");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("preresolved");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
}
}
obj* l_lean_elaborator_to__pexpr___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 2:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_16; obj* x_18; uint8 x_19; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_9);
lean::dec(x_5);
x_18 = l_lean_elaborator_to__pexpr___main___closed__7;
x_19 = lean_name_dec_eq(x_7, x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_elaborator_to__pexpr___main___closed__2;
x_21 = lean_name_dec_eq(x_7, x_20);
if (x_21 == 0)
{
obj* x_22; uint8 x_23; 
x_22 = l_lean_elaborator_to__pexpr___main___closed__8;
x_23 = lean_name_dec_eq(x_7, x_22);
if (x_23 == 0)
{
obj* x_24; uint8 x_25; 
x_24 = l_lean_elaborator_to__pexpr___main___closed__9;
x_25 = lean_name_dec_eq(x_7, x_24);
if (x_25 == 0)
{
obj* x_26; uint8 x_27; 
x_26 = l_lean_parser_term_sort_has__view_x_27___lambda__1___closed__4;
x_27 = lean_name_dec_eq(x_7, x_26);
if (x_27 == 0)
{
obj* x_28; uint8 x_29; 
x_28 = l_lean_elaborator_to__pexpr___main___closed__10;
x_29 = lean_name_dec_eq(x_7, x_28);
if (x_29 == 0)
{
obj* x_30; uint8 x_31; 
x_30 = l_lean_elaborator_to__pexpr___main___closed__11;
x_31 = lean_name_dec_eq(x_7, x_30);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = l_lean_elaborator_to__pexpr___main___closed__12;
x_33 = lean_name_dec_eq(x_7, x_32);
if (x_33 == 0)
{
obj* x_34; uint8 x_35; 
x_34 = l_lean_elaborator_to__pexpr___main___closed__13;
x_35 = lean_name_dec_eq(x_7, x_34);
if (x_35 == 0)
{
obj* x_36; uint8 x_37; 
x_36 = l_lean_elaborator_to__pexpr___main___closed__14;
x_37 = lean_name_dec_eq(x_7, x_36);
if (x_37 == 0)
{
obj* x_38; uint8 x_39; 
x_38 = l_lean_elaborator_to__pexpr___main___closed__15;
x_39 = lean_name_dec_eq(x_7, x_38);
if (x_39 == 0)
{
obj* x_40; uint8 x_41; 
x_40 = l_lean_elaborator_to__pexpr___main___closed__16;
x_41 = lean_name_dec_eq(x_7, x_40);
if (x_41 == 0)
{
obj* x_42; uint8 x_43; 
x_42 = l_lean_elaborator_to__pexpr___main___closed__17;
x_43 = lean_name_dec_eq(x_7, x_42);
if (x_43 == 0)
{
obj* x_44; uint8 x_45; 
x_44 = l_lean_elaborator_to__pexpr___main___closed__18;
x_45 = lean_name_dec_eq(x_7, x_44);
if (x_45 == 0)
{
obj* x_46; uint8 x_47; 
x_46 = l_lean_elaborator_to__pexpr___main___closed__19;
x_47 = lean_name_dec_eq(x_7, x_46);
if (x_47 == 0)
{
obj* x_48; uint8 x_49; 
x_48 = l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
x_49 = lean_name_dec_eq(x_7, x_48);
if (x_49 == 0)
{
obj* x_50; uint8 x_51; 
x_50 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
x_51 = lean_name_dec_eq(x_7, x_50);
if (x_51 == 0)
{
obj* x_52; uint8 x_53; 
x_52 = l_lean_elaborator_to__pexpr___main___closed__20;
x_53 = lean_name_dec_eq(x_7, x_52);
if (x_53 == 0)
{
obj* x_55; uint8 x_56; 
lean::dec(x_9);
x_55 = l_lean_elaborator_to__pexpr___main___closed__21;
x_56 = lean_name_dec_eq(x_7, x_55);
if (x_56 == 0)
{
obj* x_57; uint8 x_58; 
x_57 = l_lean_elaborator_to__pexpr___main___closed__22;
x_58 = lean_name_dec_eq(x_7, x_57);
if (x_58 == 0)
{
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_68; 
x_59 = l_lean_name_to__string___closed__1;
lean::inc(x_59);
x_61 = l_lean_name_to__string__with__sep___main(x_59, x_7);
x_62 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_62);
x_64 = lean::string_append(x_62, x_61);
lean::dec(x_61);
lean::inc(x_1);
lean::inc(x_0);
x_68 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_64, x_1, x_2);
if (lean::obj_tag(x_68) == 0)
{
obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_1);
lean::dec(x_0);
x_71 = lean::cnstr_get(x_68, 0);
lean::inc(x_71);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_73 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_73 = x_68;
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
return x_74;
}
else
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_82; 
x_75 = lean::cnstr_get(x_68, 0);
lean::inc(x_75);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_77 = x_68;
}
x_78 = lean::cnstr_get(x_75, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_75, 1);
lean::inc(x_80);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_82 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 lean::cnstr_release(x_75, 1);
 x_82 = x_75;
}
if (x_21 == 0)
{
obj* x_83; 
x_83 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_83) == 0)
{
obj* x_85; obj* x_86; 
lean::dec(x_1);
if (lean::is_scalar(x_82)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_82;
}
lean::cnstr_set(x_85, 0, x_78);
lean::cnstr_set(x_85, 1, x_80);
if (lean::is_scalar(x_77)) {
 x_86 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_86 = x_77;
}
lean::cnstr_set(x_86, 0, x_85);
return x_86;
}
else
{
obj* x_87; obj* x_90; obj* x_93; obj* x_96; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_103; obj* x_106; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_87 = lean::cnstr_get(x_83, 0);
lean::inc(x_87);
lean::dec(x_83);
x_90 = lean::cnstr_get(x_1, 0);
lean::inc(x_90);
lean::dec(x_1);
x_93 = lean::cnstr_get(x_90, 2);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_lean_file__map_to__position(x_93, x_87);
x_97 = lean::box(0);
x_98 = lean::cnstr_get(x_96, 1);
lean::inc(x_98);
x_100 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_100);
x_102 = l_lean_kvmap_set__nat(x_97, x_100, x_98);
x_103 = lean::cnstr_get(x_96, 0);
lean::inc(x_103);
lean::dec(x_96);
x_106 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_106);
x_108 = l_lean_kvmap_set__nat(x_102, x_106, x_103);
x_109 = lean_expr_mk_mdata(x_108, x_78);
if (lean::is_scalar(x_82)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_82;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_80);
if (lean::is_scalar(x_77)) {
 x_111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_111 = x_77;
}
lean::cnstr_set(x_111, 0, x_110);
return x_111;
}
}
else
{
obj* x_114; obj* x_115; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_82)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_82;
}
lean::cnstr_set(x_114, 0, x_78);
lean::cnstr_set(x_114, 1, x_80);
if (lean::is_scalar(x_77)) {
 x_115 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_115 = x_77;
}
lean::cnstr_set(x_115, 0, x_114);
return x_115;
}
}
}
else
{
obj* x_116; obj* x_117; obj* x_120; obj* x_121; obj* x_123; obj* x_125; 
x_116 = l_lean_parser_term_match_has__view;
x_117 = lean::cnstr_get(x_116, 0);
lean::inc(x_117);
lean::inc(x_0);
x_120 = lean::apply_1(x_117, x_0);
x_121 = lean::cnstr_get(x_120, 5);
lean::inc(x_121);
x_123 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(x_121);
lean::inc(x_1);
x_125 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_123, x_1, x_2);
if (lean::obj_tag(x_125) == 0)
{
obj* x_127; obj* x_129; obj* x_130; 
lean::dec(x_120);
x_127 = lean::cnstr_get(x_125, 0);
lean::inc(x_127);
if (lean::is_shared(x_125)) {
 lean::dec(x_125);
 x_129 = lean::box(0);
} else {
 lean::cnstr_release(x_125, 0);
 x_129 = x_125;
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_127);
x_12 = x_130;
goto lbl_13;
}
else
{
obj* x_131; obj* x_133; obj* x_134; obj* x_136; obj* x_138; obj* x_139; obj* x_141; obj* x_143; 
x_131 = lean::cnstr_get(x_125, 0);
lean::inc(x_131);
if (lean::is_shared(x_125)) {
 lean::dec(x_125);
 x_133 = lean::box(0);
} else {
 lean::cnstr_release(x_125, 0);
 x_133 = x_125;
}
x_134 = lean::cnstr_get(x_131, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_131, 1);
lean::inc(x_136);
if (lean::is_shared(x_131)) {
 lean::dec(x_131);
 x_138 = lean::box(0);
} else {
 lean::cnstr_release(x_131, 0);
 lean::cnstr_release(x_131, 1);
 x_138 = x_131;
}
x_139 = lean::cnstr_get(x_120, 2);
lean::inc(x_139);
x_141 = l_lean_expander_get__opt__type___main(x_139);
lean::inc(x_1);
x_143 = l_lean_elaborator_to__pexpr___main(x_141, x_1, x_136);
if (lean::obj_tag(x_143) == 0)
{
obj* x_147; obj* x_150; 
lean::dec(x_138);
lean::dec(x_134);
lean::dec(x_120);
x_147 = lean::cnstr_get(x_143, 0);
lean::inc(x_147);
lean::dec(x_143);
if (lean::is_scalar(x_133)) {
 x_150 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_150 = x_133;
 lean::cnstr_set_tag(x_133, 0);
}
lean::cnstr_set(x_150, 0, x_147);
x_12 = x_150;
goto lbl_13;
}
else
{
obj* x_151; obj* x_154; obj* x_156; obj* x_159; 
x_151 = lean::cnstr_get(x_143, 0);
lean::inc(x_151);
lean::dec(x_143);
x_154 = lean::cnstr_get(x_151, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_151, 1);
lean::inc(x_156);
lean::dec(x_151);
x_159 = l_lean_elaborator_mk__eqns(x_154, x_134);
switch (lean::obj_tag(x_159)) {
case 10:
{
obj* x_160; obj* x_162; obj* x_165; obj* x_169; 
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_159, 1);
lean::inc(x_162);
lean::dec(x_159);
x_165 = lean::cnstr_get(x_120, 1);
lean::inc(x_165);
lean::dec(x_120);
lean::inc(x_1);
x_169 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_165, x_1, x_156);
if (lean::obj_tag(x_169) == 0)
{
obj* x_173; obj* x_176; 
lean::dec(x_138);
lean::dec(x_160);
lean::dec(x_162);
x_173 = lean::cnstr_get(x_169, 0);
lean::inc(x_173);
lean::dec(x_169);
if (lean::is_scalar(x_133)) {
 x_176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_176 = x_133;
 lean::cnstr_set_tag(x_133, 0);
}
lean::cnstr_set(x_176, 0, x_173);
x_12 = x_176;
goto lbl_13;
}
else
{
obj* x_177; obj* x_180; obj* x_182; obj* x_185; uint8 x_186; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
x_177 = lean::cnstr_get(x_169, 0);
lean::inc(x_177);
lean::dec(x_169);
x_180 = lean::cnstr_get(x_177, 0);
lean::inc(x_180);
x_182 = lean::cnstr_get(x_177, 1);
lean::inc(x_182);
lean::dec(x_177);
x_185 = l_lean_elaborator_to__pexpr___main___closed__24;
x_186 = 1;
lean::inc(x_185);
x_188 = l_lean_kvmap_set__bool(x_160, x_185, x_186);
x_189 = lean_expr_mk_mdata(x_188, x_162);
x_190 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_189, x_180);
if (lean::is_scalar(x_138)) {
 x_191 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_191 = x_138;
}
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_182);
if (lean::is_scalar(x_133)) {
 x_192 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_192 = x_133;
}
lean::cnstr_set(x_192, 0, x_191);
x_12 = x_192;
goto lbl_13;
}
}
default:
{
obj* x_197; obj* x_201; 
lean::dec(x_138);
lean::dec(x_159);
lean::dec(x_120);
lean::dec(x_133);
x_197 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_1);
lean::inc(x_197);
lean::inc(x_0);
x_201 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_197, x_1, x_156);
x_12 = x_201;
goto lbl_13;
}
}
}
}
}
}
else
{
obj* x_202; obj* x_203; obj* x_206; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_215; obj* x_216; obj* x_218; obj* x_220; 
x_202 = l_lean_parser_term_struct__inst_has__view;
x_203 = lean::cnstr_get(x_202, 0);
lean::inc(x_203);
lean::inc(x_0);
x_206 = lean::apply_1(x_203, x_0);
x_207 = lean::cnstr_get(x_206, 3);
lean::inc(x_207);
x_209 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_207);
x_210 = lean::cnstr_get(x_209, 0);
lean::inc(x_210);
x_212 = lean::cnstr_get(x_209, 1);
lean::inc(x_212);
if (lean::is_shared(x_209)) {
 lean::dec(x_209);
 x_214 = lean::box(0);
} else {
 lean::cnstr_release(x_209, 0);
 lean::cnstr_release(x_209, 1);
 x_214 = x_209;
}
x_215 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_212);
x_216 = lean::cnstr_get(x_215, 0);
lean::inc(x_216);
x_218 = lean::cnstr_get(x_215, 1);
lean::inc(x_218);
if (lean::is_shared(x_215)) {
 lean::dec(x_215);
 x_220 = lean::box(0);
} else {
 lean::cnstr_release(x_215, 0);
 lean::cnstr_release(x_215, 1);
 x_220 = x_215;
}
if (lean::obj_tag(x_218) == 0)
{
obj* x_223; 
lean::inc(x_1);
lean::inc(x_0);
x_223 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_210, x_1, x_2);
if (lean::obj_tag(x_223) == 0)
{
obj* x_231; obj* x_233; obj* x_234; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_231 = lean::cnstr_get(x_223, 0);
lean::inc(x_231);
if (lean::is_shared(x_223)) {
 lean::dec(x_223);
 x_233 = lean::box(0);
} else {
 lean::cnstr_release(x_223, 0);
 x_233 = x_223;
}
if (lean::is_scalar(x_233)) {
 x_234 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_234 = x_233;
}
lean::cnstr_set(x_234, 0, x_231);
return x_234;
}
else
{
obj* x_235; obj* x_237; obj* x_238; obj* x_240; obj* x_243; obj* x_247; 
x_235 = lean::cnstr_get(x_223, 0);
lean::inc(x_235);
if (lean::is_shared(x_223)) {
 lean::dec(x_223);
 x_237 = lean::box(0);
} else {
 lean::cnstr_release(x_223, 0);
 x_237 = x_223;
}
x_238 = lean::cnstr_get(x_235, 0);
lean::inc(x_238);
x_240 = lean::cnstr_get(x_235, 1);
lean::inc(x_240);
lean::dec(x_235);
lean::inc(x_1);
lean::inc(x_0);
x_247 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_216, x_1, x_240);
if (lean::obj_tag(x_247) == 0)
{
obj* x_255; obj* x_258; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_214);
lean::dec(x_238);
x_255 = lean::cnstr_get(x_247, 0);
lean::inc(x_255);
lean::dec(x_247);
if (lean::is_scalar(x_237)) {
 x_258 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_258 = x_237;
 lean::cnstr_set_tag(x_237, 0);
}
lean::cnstr_set(x_258, 0, x_255);
return x_258;
}
else
{
obj* x_259; obj* x_262; obj* x_264; obj* x_267; 
x_259 = lean::cnstr_get(x_247, 0);
lean::inc(x_259);
lean::dec(x_247);
x_262 = lean::cnstr_get(x_259, 0);
lean::inc(x_262);
x_264 = lean::cnstr_get(x_259, 1);
lean::inc(x_264);
lean::dec(x_259);
x_267 = lean::cnstr_get(x_206, 2);
lean::inc(x_267);
if (lean::obj_tag(x_267) == 0)
{
obj* x_270; 
lean::dec(x_237);
if (lean::is_scalar(x_220)) {
 x_270 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_270 = x_220;
}
lean::cnstr_set(x_270, 0, x_262);
lean::cnstr_set(x_270, 1, x_264);
x_243 = x_270;
goto lbl_244;
}
else
{
obj* x_271; obj* x_274; obj* x_278; 
x_271 = lean::cnstr_get(x_267, 0);
lean::inc(x_271);
lean::dec(x_267);
x_274 = lean::cnstr_get(x_271, 0);
lean::inc(x_274);
lean::dec(x_271);
lean::inc(x_1);
x_278 = l_lean_elaborator_to__pexpr___main(x_274, x_1, x_264);
if (lean::obj_tag(x_278) == 0)
{
obj* x_287; obj* x_290; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_262);
lean::dec(x_220);
lean::dec(x_214);
lean::dec(x_238);
x_287 = lean::cnstr_get(x_278, 0);
lean::inc(x_287);
lean::dec(x_278);
if (lean::is_scalar(x_237)) {
 x_290 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_290 = x_237;
 lean::cnstr_set_tag(x_237, 0);
}
lean::cnstr_set(x_290, 0, x_287);
return x_290;
}
else
{
obj* x_292; obj* x_295; obj* x_297; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
lean::dec(x_237);
x_292 = lean::cnstr_get(x_278, 0);
lean::inc(x_292);
lean::dec(x_278);
x_295 = lean::cnstr_get(x_292, 0);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_292, 1);
lean::inc(x_297);
lean::dec(x_292);
x_300 = lean::box(0);
x_301 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_301, 0, x_295);
lean::cnstr_set(x_301, 1, x_300);
x_302 = l_list_append___rarg(x_262, x_301);
if (lean::is_scalar(x_220)) {
 x_303 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_303 = x_220;
}
lean::cnstr_set(x_303, 0, x_302);
lean::cnstr_set(x_303, 1, x_297);
x_243 = x_303;
goto lbl_244;
}
}
}
lbl_244:
{
obj* x_304; obj* x_306; obj* x_309; obj* x_310; obj* x_312; obj* x_313; obj* x_316; obj* x_317; uint8 x_318; obj* x_320; obj* x_321; obj* x_324; obj* x_326; obj* x_327; obj* x_329; obj* x_330; obj* x_331; obj* x_333; obj* x_334; obj* x_335; obj* x_336; obj* x_337; 
x_304 = lean::cnstr_get(x_243, 0);
lean::inc(x_304);
x_306 = lean::cnstr_get(x_243, 1);
lean::inc(x_306);
lean::dec(x_243);
x_309 = lean::box(0);
x_310 = lean::mk_nat_obj(0u);
lean::inc(x_238);
x_312 = l_list_length__aux___main___rarg(x_238, x_310);
x_313 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_313);
lean::inc(x_309);
x_316 = l_lean_kvmap_set__nat(x_309, x_313, x_312);
x_317 = l_lean_elaborator_to__pexpr___main___closed__26;
x_318 = 0;
lean::inc(x_317);
x_320 = l_lean_kvmap_set__bool(x_316, x_317, x_318);
x_321 = lean::cnstr_get(x_206, 1);
lean::inc(x_321);
lean::dec(x_206);
x_324 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_324);
x_326 = l_option_map___rarg(x_324, x_321);
x_327 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_327);
x_329 = l_option_map___rarg(x_327, x_326);
x_330 = l_option_get__or__else___main___rarg(x_329, x_309);
x_331 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_331);
x_333 = l_lean_kvmap_set__name(x_320, x_331, x_330);
x_334 = l_list_append___rarg(x_238, x_304);
x_335 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(x_334);
x_336 = lean_expr_mk_mdata(x_333, x_335);
if (lean::is_scalar(x_214)) {
 x_337 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_337 = x_214;
}
lean::cnstr_set(x_337, 0, x_336);
lean::cnstr_set(x_337, 1, x_306);
x_14 = x_337;
goto lbl_15;
}
}
}
else
{
obj* x_338; obj* x_340; obj* x_342; obj* x_343; 
x_338 = lean::cnstr_get(x_218, 0);
lean::inc(x_338);
x_340 = lean::cnstr_get(x_218, 1);
lean::inc(x_340);
if (lean::is_shared(x_218)) {
 lean::dec(x_218);
 x_342 = lean::box(0);
} else {
 lean::cnstr_release(x_218, 0);
 lean::cnstr_release(x_218, 1);
 x_342 = x_218;
}
x_343 = lean::cnstr_get(x_338, 0);
lean::inc(x_343);
lean::dec(x_338);
if (lean::obj_tag(x_343) == 0)
{
obj* x_347; obj* x_348; obj* x_350; obj* x_351; obj* x_354; 
lean::dec(x_340);
x_347 = l_lean_parser_term_struct__inst__item_has__view;
x_348 = lean::cnstr_get(x_347, 1);
lean::inc(x_348);
x_350 = lean::apply_1(x_348, x_343);
x_351 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
lean::inc(x_351);
x_354 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_350, x_351, x_1, x_2);
if (lean::obj_tag(x_354) == 0)
{
obj* x_364; obj* x_366; obj* x_367; 
lean::dec(x_342);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_210);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_364 = lean::cnstr_get(x_354, 0);
lean::inc(x_364);
if (lean::is_shared(x_354)) {
 lean::dec(x_354);
 x_366 = lean::box(0);
} else {
 lean::cnstr_release(x_354, 0);
 x_366 = x_354;
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
obj* x_368; obj* x_370; obj* x_371; obj* x_373; obj* x_378; 
x_368 = lean::cnstr_get(x_354, 0);
lean::inc(x_368);
if (lean::is_shared(x_354)) {
 lean::dec(x_354);
 x_370 = lean::box(0);
} else {
 lean::cnstr_release(x_354, 0);
 x_370 = x_354;
}
x_371 = lean::cnstr_get(x_368, 0);
lean::inc(x_371);
x_373 = lean::cnstr_get(x_368, 1);
lean::inc(x_373);
lean::dec(x_368);
lean::inc(x_1);
lean::inc(x_0);
x_378 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_210, x_1, x_373);
if (lean::obj_tag(x_378) == 0)
{
obj* x_388; obj* x_391; 
lean::dec(x_342);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_371);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_388 = lean::cnstr_get(x_378, 0);
lean::inc(x_388);
lean::dec(x_378);
if (lean::is_scalar(x_370)) {
 x_391 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_391 = x_370;
 lean::cnstr_set_tag(x_370, 0);
}
lean::cnstr_set(x_391, 0, x_388);
return x_391;
}
else
{
obj* x_392; obj* x_395; obj* x_397; obj* x_400; obj* x_404; 
x_392 = lean::cnstr_get(x_378, 0);
lean::inc(x_392);
lean::dec(x_378);
x_395 = lean::cnstr_get(x_392, 0);
lean::inc(x_395);
x_397 = lean::cnstr_get(x_392, 1);
lean::inc(x_397);
lean::dec(x_392);
lean::inc(x_1);
lean::inc(x_0);
x_404 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_216, x_1, x_397);
if (lean::obj_tag(x_404) == 0)
{
obj* x_414; obj* x_417; 
lean::dec(x_342);
lean::dec(x_395);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_371);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_214);
x_414 = lean::cnstr_get(x_404, 0);
lean::inc(x_414);
lean::dec(x_404);
if (lean::is_scalar(x_370)) {
 x_417 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_417 = x_370;
 lean::cnstr_set_tag(x_370, 0);
}
lean::cnstr_set(x_417, 0, x_414);
return x_417;
}
else
{
obj* x_418; obj* x_421; obj* x_423; obj* x_426; 
x_418 = lean::cnstr_get(x_404, 0);
lean::inc(x_418);
lean::dec(x_404);
x_421 = lean::cnstr_get(x_418, 0);
lean::inc(x_421);
x_423 = lean::cnstr_get(x_418, 1);
lean::inc(x_423);
lean::dec(x_418);
x_426 = lean::cnstr_get(x_206, 2);
lean::inc(x_426);
if (lean::obj_tag(x_426) == 0)
{
obj* x_430; 
lean::dec(x_342);
lean::dec(x_370);
if (lean::is_scalar(x_220)) {
 x_430 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_430 = x_220;
}
lean::cnstr_set(x_430, 0, x_421);
lean::cnstr_set(x_430, 1, x_423);
x_400 = x_430;
goto lbl_401;
}
else
{
obj* x_431; obj* x_434; obj* x_438; 
x_431 = lean::cnstr_get(x_426, 0);
lean::inc(x_431);
lean::dec(x_426);
x_434 = lean::cnstr_get(x_431, 0);
lean::inc(x_434);
lean::dec(x_431);
lean::inc(x_1);
x_438 = l_lean_elaborator_to__pexpr___main(x_434, x_1, x_423);
if (lean::obj_tag(x_438) == 0)
{
obj* x_449; obj* x_452; 
lean::dec(x_342);
lean::dec(x_395);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_371);
lean::dec(x_206);
lean::dec(x_421);
lean::dec(x_220);
lean::dec(x_214);
x_449 = lean::cnstr_get(x_438, 0);
lean::inc(x_449);
lean::dec(x_438);
if (lean::is_scalar(x_370)) {
 x_452 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_452 = x_370;
 lean::cnstr_set_tag(x_370, 0);
}
lean::cnstr_set(x_452, 0, x_449);
return x_452;
}
else
{
obj* x_454; obj* x_457; obj* x_459; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
lean::dec(x_370);
x_454 = lean::cnstr_get(x_438, 0);
lean::inc(x_454);
lean::dec(x_438);
x_457 = lean::cnstr_get(x_454, 0);
lean::inc(x_457);
x_459 = lean::cnstr_get(x_454, 1);
lean::inc(x_459);
lean::dec(x_454);
x_462 = lean::box(0);
if (lean::is_scalar(x_342)) {
 x_463 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_463 = x_342;
}
lean::cnstr_set(x_463, 0, x_457);
lean::cnstr_set(x_463, 1, x_462);
x_464 = l_list_append___rarg(x_421, x_463);
if (lean::is_scalar(x_220)) {
 x_465 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_465 = x_220;
}
lean::cnstr_set(x_465, 0, x_464);
lean::cnstr_set(x_465, 1, x_459);
x_400 = x_465;
goto lbl_401;
}
}
}
lbl_401:
{
obj* x_466; obj* x_468; obj* x_471; obj* x_472; obj* x_474; obj* x_475; obj* x_478; obj* x_479; uint8 x_480; obj* x_483; obj* x_484; obj* x_487; obj* x_489; obj* x_490; obj* x_492; obj* x_493; obj* x_494; obj* x_496; obj* x_497; obj* x_498; obj* x_499; obj* x_500; 
x_466 = lean::cnstr_get(x_400, 0);
lean::inc(x_466);
x_468 = lean::cnstr_get(x_400, 1);
lean::inc(x_468);
lean::dec(x_400);
x_471 = lean::box(0);
x_472 = lean::mk_nat_obj(0u);
lean::inc(x_395);
x_474 = l_list_length__aux___main___rarg(x_395, x_472);
x_475 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_475);
lean::inc(x_471);
x_478 = l_lean_kvmap_set__nat(x_471, x_475, x_474);
x_479 = l_lean_elaborator_to__pexpr___main___closed__26;
x_480 = lean::unbox(x_371);
lean::dec(x_371);
lean::inc(x_479);
x_483 = l_lean_kvmap_set__bool(x_478, x_479, x_480);
x_484 = lean::cnstr_get(x_206, 1);
lean::inc(x_484);
lean::dec(x_206);
x_487 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_487);
x_489 = l_option_map___rarg(x_487, x_484);
x_490 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_490);
x_492 = l_option_map___rarg(x_490, x_489);
x_493 = l_option_get__or__else___main___rarg(x_492, x_471);
x_494 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_494);
x_496 = l_lean_kvmap_set__name(x_483, x_494, x_493);
x_497 = l_list_append___rarg(x_395, x_466);
x_498 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_497);
x_499 = lean_expr_mk_mdata(x_496, x_498);
if (lean::is_scalar(x_214)) {
 x_500 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_500 = x_214;
}
lean::cnstr_set(x_500, 0, x_499);
lean::cnstr_set(x_500, 1, x_468);
x_14 = x_500;
goto lbl_15;
}
}
}
}
else
{
if (lean::obj_tag(x_340) == 0)
{
obj* x_504; 
lean::dec(x_343);
lean::inc(x_1);
lean::inc(x_0);
x_504 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_210, x_1, x_2);
if (lean::obj_tag(x_504) == 0)
{
obj* x_513; obj* x_515; obj* x_516; 
lean::dec(x_342);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_513 = lean::cnstr_get(x_504, 0);
lean::inc(x_513);
if (lean::is_shared(x_504)) {
 lean::dec(x_504);
 x_515 = lean::box(0);
} else {
 lean::cnstr_release(x_504, 0);
 x_515 = x_504;
}
if (lean::is_scalar(x_515)) {
 x_516 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_516 = x_515;
}
lean::cnstr_set(x_516, 0, x_513);
return x_516;
}
else
{
obj* x_517; obj* x_519; obj* x_520; obj* x_522; obj* x_525; obj* x_529; 
x_517 = lean::cnstr_get(x_504, 0);
lean::inc(x_517);
if (lean::is_shared(x_504)) {
 lean::dec(x_504);
 x_519 = lean::box(0);
} else {
 lean::cnstr_release(x_504, 0);
 x_519 = x_504;
}
x_520 = lean::cnstr_get(x_517, 0);
lean::inc(x_520);
x_522 = lean::cnstr_get(x_517, 1);
lean::inc(x_522);
lean::dec(x_517);
lean::inc(x_1);
lean::inc(x_0);
x_529 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_216, x_1, x_522);
if (lean::obj_tag(x_529) == 0)
{
obj* x_538; obj* x_541; 
lean::dec(x_342);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_520);
lean::dec(x_220);
lean::dec(x_214);
x_538 = lean::cnstr_get(x_529, 0);
lean::inc(x_538);
lean::dec(x_529);
if (lean::is_scalar(x_519)) {
 x_541 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_541 = x_519;
 lean::cnstr_set_tag(x_519, 0);
}
lean::cnstr_set(x_541, 0, x_538);
return x_541;
}
else
{
obj* x_542; obj* x_545; obj* x_547; obj* x_550; 
x_542 = lean::cnstr_get(x_529, 0);
lean::inc(x_542);
lean::dec(x_529);
x_545 = lean::cnstr_get(x_542, 0);
lean::inc(x_545);
x_547 = lean::cnstr_get(x_542, 1);
lean::inc(x_547);
lean::dec(x_542);
x_550 = lean::cnstr_get(x_206, 2);
lean::inc(x_550);
if (lean::obj_tag(x_550) == 0)
{
obj* x_554; 
lean::dec(x_342);
lean::dec(x_519);
if (lean::is_scalar(x_220)) {
 x_554 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_554 = x_220;
}
lean::cnstr_set(x_554, 0, x_545);
lean::cnstr_set(x_554, 1, x_547);
x_525 = x_554;
goto lbl_526;
}
else
{
obj* x_555; obj* x_558; obj* x_562; 
x_555 = lean::cnstr_get(x_550, 0);
lean::inc(x_555);
lean::dec(x_550);
x_558 = lean::cnstr_get(x_555, 0);
lean::inc(x_558);
lean::dec(x_555);
lean::inc(x_1);
x_562 = l_lean_elaborator_to__pexpr___main(x_558, x_1, x_547);
if (lean::obj_tag(x_562) == 0)
{
obj* x_572; obj* x_575; 
lean::dec(x_545);
lean::dec(x_342);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_520);
lean::dec(x_220);
lean::dec(x_214);
x_572 = lean::cnstr_get(x_562, 0);
lean::inc(x_572);
lean::dec(x_562);
if (lean::is_scalar(x_519)) {
 x_575 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_575 = x_519;
 lean::cnstr_set_tag(x_519, 0);
}
lean::cnstr_set(x_575, 0, x_572);
return x_575;
}
else
{
obj* x_577; obj* x_580; obj* x_582; obj* x_585; obj* x_586; obj* x_587; obj* x_588; 
lean::dec(x_519);
x_577 = lean::cnstr_get(x_562, 0);
lean::inc(x_577);
lean::dec(x_562);
x_580 = lean::cnstr_get(x_577, 0);
lean::inc(x_580);
x_582 = lean::cnstr_get(x_577, 1);
lean::inc(x_582);
lean::dec(x_577);
x_585 = lean::box(0);
if (lean::is_scalar(x_342)) {
 x_586 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_586 = x_342;
}
lean::cnstr_set(x_586, 0, x_580);
lean::cnstr_set(x_586, 1, x_585);
x_587 = l_list_append___rarg(x_545, x_586);
if (lean::is_scalar(x_220)) {
 x_588 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_588 = x_220;
}
lean::cnstr_set(x_588, 0, x_587);
lean::cnstr_set(x_588, 1, x_582);
x_525 = x_588;
goto lbl_526;
}
}
}
lbl_526:
{
obj* x_589; obj* x_591; obj* x_594; obj* x_595; obj* x_597; obj* x_598; obj* x_601; obj* x_602; uint8 x_603; obj* x_605; obj* x_606; obj* x_609; obj* x_611; obj* x_612; obj* x_614; obj* x_615; obj* x_616; obj* x_618; obj* x_619; obj* x_620; obj* x_621; obj* x_622; 
x_589 = lean::cnstr_get(x_525, 0);
lean::inc(x_589);
x_591 = lean::cnstr_get(x_525, 1);
lean::inc(x_591);
lean::dec(x_525);
x_594 = lean::box(0);
x_595 = lean::mk_nat_obj(0u);
lean::inc(x_520);
x_597 = l_list_length__aux___main___rarg(x_520, x_595);
x_598 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_598);
lean::inc(x_594);
x_601 = l_lean_kvmap_set__nat(x_594, x_598, x_597);
x_602 = l_lean_elaborator_to__pexpr___main___closed__26;
x_603 = 1;
lean::inc(x_602);
x_605 = l_lean_kvmap_set__bool(x_601, x_602, x_603);
x_606 = lean::cnstr_get(x_206, 1);
lean::inc(x_606);
lean::dec(x_206);
x_609 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_609);
x_611 = l_option_map___rarg(x_609, x_606);
x_612 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_612);
x_614 = l_option_map___rarg(x_612, x_611);
x_615 = l_option_get__or__else___main___rarg(x_614, x_594);
x_616 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_616);
x_618 = l_lean_kvmap_set__name(x_605, x_616, x_615);
x_619 = l_list_append___rarg(x_520, x_589);
x_620 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_619);
x_621 = lean_expr_mk_mdata(x_618, x_620);
if (lean::is_scalar(x_214)) {
 x_622 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_622 = x_214;
}
lean::cnstr_set(x_622, 0, x_621);
lean::cnstr_set(x_622, 1, x_591);
x_14 = x_622;
goto lbl_15;
}
}
}
else
{
obj* x_624; obj* x_625; obj* x_627; obj* x_628; obj* x_631; 
lean::dec(x_340);
x_624 = l_lean_parser_term_struct__inst__item_has__view;
x_625 = lean::cnstr_get(x_624, 1);
lean::inc(x_625);
x_627 = lean::apply_1(x_625, x_343);
x_628 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
lean::inc(x_628);
x_631 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_627, x_628, x_1, x_2);
if (lean::obj_tag(x_631) == 0)
{
obj* x_641; obj* x_643; obj* x_644; 
lean::dec(x_342);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_210);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_641 = lean::cnstr_get(x_631, 0);
lean::inc(x_641);
if (lean::is_shared(x_631)) {
 lean::dec(x_631);
 x_643 = lean::box(0);
} else {
 lean::cnstr_release(x_631, 0);
 x_643 = x_631;
}
if (lean::is_scalar(x_643)) {
 x_644 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_644 = x_643;
}
lean::cnstr_set(x_644, 0, x_641);
return x_644;
}
else
{
obj* x_645; obj* x_647; obj* x_648; obj* x_650; obj* x_655; 
x_645 = lean::cnstr_get(x_631, 0);
lean::inc(x_645);
if (lean::is_shared(x_631)) {
 lean::dec(x_631);
 x_647 = lean::box(0);
} else {
 lean::cnstr_release(x_631, 0);
 x_647 = x_631;
}
x_648 = lean::cnstr_get(x_645, 0);
lean::inc(x_648);
x_650 = lean::cnstr_get(x_645, 1);
lean::inc(x_650);
lean::dec(x_645);
lean::inc(x_1);
lean::inc(x_0);
x_655 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_210, x_1, x_650);
if (lean::obj_tag(x_655) == 0)
{
obj* x_665; obj* x_668; 
lean::dec(x_342);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_648);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_665 = lean::cnstr_get(x_655, 0);
lean::inc(x_665);
lean::dec(x_655);
if (lean::is_scalar(x_647)) {
 x_668 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_668 = x_647;
 lean::cnstr_set_tag(x_647, 0);
}
lean::cnstr_set(x_668, 0, x_665);
return x_668;
}
else
{
obj* x_669; obj* x_672; obj* x_674; obj* x_677; obj* x_681; 
x_669 = lean::cnstr_get(x_655, 0);
lean::inc(x_669);
lean::dec(x_655);
x_672 = lean::cnstr_get(x_669, 0);
lean::inc(x_672);
x_674 = lean::cnstr_get(x_669, 1);
lean::inc(x_674);
lean::dec(x_669);
lean::inc(x_1);
lean::inc(x_0);
x_681 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_216, x_1, x_674);
if (lean::obj_tag(x_681) == 0)
{
obj* x_691; obj* x_694; 
lean::dec(x_342);
lean::dec(x_672);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_648);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_214);
x_691 = lean::cnstr_get(x_681, 0);
lean::inc(x_691);
lean::dec(x_681);
if (lean::is_scalar(x_647)) {
 x_694 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_694 = x_647;
 lean::cnstr_set_tag(x_647, 0);
}
lean::cnstr_set(x_694, 0, x_691);
return x_694;
}
else
{
obj* x_695; obj* x_698; obj* x_700; obj* x_703; 
x_695 = lean::cnstr_get(x_681, 0);
lean::inc(x_695);
lean::dec(x_681);
x_698 = lean::cnstr_get(x_695, 0);
lean::inc(x_698);
x_700 = lean::cnstr_get(x_695, 1);
lean::inc(x_700);
lean::dec(x_695);
x_703 = lean::cnstr_get(x_206, 2);
lean::inc(x_703);
if (lean::obj_tag(x_703) == 0)
{
obj* x_707; 
lean::dec(x_342);
lean::dec(x_647);
if (lean::is_scalar(x_220)) {
 x_707 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_707 = x_220;
}
lean::cnstr_set(x_707, 0, x_698);
lean::cnstr_set(x_707, 1, x_700);
x_677 = x_707;
goto lbl_678;
}
else
{
obj* x_708; obj* x_711; obj* x_715; 
x_708 = lean::cnstr_get(x_703, 0);
lean::inc(x_708);
lean::dec(x_703);
x_711 = lean::cnstr_get(x_708, 0);
lean::inc(x_711);
lean::dec(x_708);
lean::inc(x_1);
x_715 = l_lean_elaborator_to__pexpr___main(x_711, x_1, x_700);
if (lean::obj_tag(x_715) == 0)
{
obj* x_726; obj* x_729; 
lean::dec(x_342);
lean::dec(x_672);
lean::dec(x_698);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_648);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_214);
x_726 = lean::cnstr_get(x_715, 0);
lean::inc(x_726);
lean::dec(x_715);
if (lean::is_scalar(x_647)) {
 x_729 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_729 = x_647;
 lean::cnstr_set_tag(x_647, 0);
}
lean::cnstr_set(x_729, 0, x_726);
return x_729;
}
else
{
obj* x_731; obj* x_734; obj* x_736; obj* x_739; obj* x_740; obj* x_741; obj* x_742; 
lean::dec(x_647);
x_731 = lean::cnstr_get(x_715, 0);
lean::inc(x_731);
lean::dec(x_715);
x_734 = lean::cnstr_get(x_731, 0);
lean::inc(x_734);
x_736 = lean::cnstr_get(x_731, 1);
lean::inc(x_736);
lean::dec(x_731);
x_739 = lean::box(0);
if (lean::is_scalar(x_342)) {
 x_740 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_740 = x_342;
}
lean::cnstr_set(x_740, 0, x_734);
lean::cnstr_set(x_740, 1, x_739);
x_741 = l_list_append___rarg(x_698, x_740);
if (lean::is_scalar(x_220)) {
 x_742 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_742 = x_220;
}
lean::cnstr_set(x_742, 0, x_741);
lean::cnstr_set(x_742, 1, x_736);
x_677 = x_742;
goto lbl_678;
}
}
}
lbl_678:
{
obj* x_743; obj* x_745; obj* x_748; obj* x_749; obj* x_751; obj* x_752; obj* x_755; obj* x_756; uint8 x_757; obj* x_760; obj* x_761; obj* x_764; obj* x_766; obj* x_767; obj* x_769; obj* x_770; obj* x_771; obj* x_773; obj* x_774; obj* x_775; obj* x_776; obj* x_777; 
x_743 = lean::cnstr_get(x_677, 0);
lean::inc(x_743);
x_745 = lean::cnstr_get(x_677, 1);
lean::inc(x_745);
lean::dec(x_677);
x_748 = lean::box(0);
x_749 = lean::mk_nat_obj(0u);
lean::inc(x_672);
x_751 = l_list_length__aux___main___rarg(x_672, x_749);
x_752 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_752);
lean::inc(x_748);
x_755 = l_lean_kvmap_set__nat(x_748, x_752, x_751);
x_756 = l_lean_elaborator_to__pexpr___main___closed__26;
x_757 = lean::unbox(x_648);
lean::dec(x_648);
lean::inc(x_756);
x_760 = l_lean_kvmap_set__bool(x_755, x_756, x_757);
x_761 = lean::cnstr_get(x_206, 1);
lean::inc(x_761);
lean::dec(x_206);
x_764 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_764);
x_766 = l_option_map___rarg(x_764, x_761);
x_767 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_767);
x_769 = l_option_map___rarg(x_767, x_766);
x_770 = l_option_get__or__else___main___rarg(x_769, x_748);
x_771 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_771);
x_773 = l_lean_kvmap_set__name(x_760, x_771, x_770);
x_774 = l_list_append___rarg(x_672, x_743);
x_775 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_774);
x_776 = lean_expr_mk_mdata(x_773, x_775);
if (lean::is_scalar(x_214)) {
 x_777 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_777 = x_214;
}
lean::cnstr_set(x_777, 0, x_776);
lean::cnstr_set(x_777, 1, x_745);
x_14 = x_777;
goto lbl_15;
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
obj* x_780; 
lean::inc(x_1);
lean::inc(x_9);
x_780 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_9, x_1, x_2);
if (lean::obj_tag(x_780) == 0)
{
obj* x_785; obj* x_787; obj* x_788; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_785 = lean::cnstr_get(x_780, 0);
lean::inc(x_785);
if (lean::is_shared(x_780)) {
 lean::dec(x_780);
 x_787 = lean::box(0);
} else {
 lean::cnstr_release(x_780, 0);
 x_787 = x_780;
}
if (lean::is_scalar(x_787)) {
 x_788 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_788 = x_787;
}
lean::cnstr_set(x_788, 0, x_785);
return x_788;
}
else
{
obj* x_789; obj* x_792; obj* x_794; obj* x_796; obj* x_797; obj* x_798; 
x_789 = lean::cnstr_get(x_780, 0);
lean::inc(x_789);
lean::dec(x_780);
x_792 = lean::cnstr_get(x_789, 0);
lean::inc(x_792);
x_794 = lean::cnstr_get(x_789, 1);
lean::inc(x_794);
if (lean::is_shared(x_789)) {
 lean::dec(x_789);
 x_796 = lean::box(0);
} else {
 lean::cnstr_release(x_789, 0);
 lean::cnstr_release(x_789, 1);
 x_796 = x_789;
}
x_797 = l_list_reverse___rarg(x_792);
if (lean::is_scalar(x_796)) {
 x_798 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_798 = x_796;
}
lean::cnstr_set(x_798, 0, x_797);
lean::cnstr_set(x_798, 1, x_794);
x_16 = x_798;
goto lbl_17;
}
}
}
else
{
obj* x_801; obj* x_802; obj* x_805; obj* x_806; obj* x_807; obj* x_809; obj* x_810; obj* x_811; 
lean::dec(x_9);
lean::dec(x_7);
x_801 = l_lean_parser_string__lit_has__view;
x_802 = lean::cnstr_get(x_801, 0);
lean::inc(x_802);
lean::inc(x_0);
x_805 = lean::apply_1(x_802, x_0);
x_806 = l_lean_parser_string__lit_view_value(x_805);
x_807 = l_lean_elaborator_to__pexpr___main___closed__31;
lean::inc(x_807);
x_809 = l_option_get__or__else___main___rarg(x_806, x_807);
x_810 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_810, 0, x_809);
x_811 = lean_expr_mk_lit(x_810);
if (x_21 == 0)
{
obj* x_812; 
x_812 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_812) == 0)
{
obj* x_814; obj* x_815; 
lean::dec(x_1);
x_814 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_814, 0, x_811);
lean::cnstr_set(x_814, 1, x_2);
x_815 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_815, 0, x_814);
return x_815;
}
else
{
obj* x_816; obj* x_819; obj* x_822; obj* x_825; obj* x_826; obj* x_827; obj* x_829; obj* x_831; obj* x_832; obj* x_835; obj* x_837; obj* x_838; obj* x_839; obj* x_840; 
x_816 = lean::cnstr_get(x_812, 0);
lean::inc(x_816);
lean::dec(x_812);
x_819 = lean::cnstr_get(x_1, 0);
lean::inc(x_819);
lean::dec(x_1);
x_822 = lean::cnstr_get(x_819, 2);
lean::inc(x_822);
lean::dec(x_819);
x_825 = l_lean_file__map_to__position(x_822, x_816);
x_826 = lean::box(0);
x_827 = lean::cnstr_get(x_825, 1);
lean::inc(x_827);
x_829 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_829);
x_831 = l_lean_kvmap_set__nat(x_826, x_829, x_827);
x_832 = lean::cnstr_get(x_825, 0);
lean::inc(x_832);
lean::dec(x_825);
x_835 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_835);
x_837 = l_lean_kvmap_set__nat(x_831, x_835, x_832);
x_838 = lean_expr_mk_mdata(x_837, x_811);
x_839 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_839, 0, x_838);
lean::cnstr_set(x_839, 1, x_2);
x_840 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_840, 0, x_839);
return x_840;
}
}
else
{
obj* x_843; obj* x_844; 
lean::dec(x_1);
lean::dec(x_0);
x_843 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_843, 0, x_811);
lean::cnstr_set(x_843, 1, x_2);
x_844 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_844, 0, x_843);
return x_844;
}
}
}
else
{
obj* x_847; obj* x_848; obj* x_851; obj* x_852; obj* x_853; obj* x_854; 
lean::dec(x_9);
lean::dec(x_7);
x_847 = l_lean_parser_number_has__view;
x_848 = lean::cnstr_get(x_847, 0);
lean::inc(x_848);
lean::inc(x_0);
x_851 = lean::apply_1(x_848, x_0);
x_852 = l_lean_parser_number_view_to__nat___main(x_851);
x_853 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_853, 0, x_852);
x_854 = lean_expr_mk_lit(x_853);
if (x_21 == 0)
{
obj* x_855; 
x_855 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_855) == 0)
{
obj* x_857; obj* x_858; 
lean::dec(x_1);
x_857 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_857, 0, x_854);
lean::cnstr_set(x_857, 1, x_2);
x_858 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_858, 0, x_857);
return x_858;
}
else
{
obj* x_859; obj* x_862; obj* x_865; obj* x_868; obj* x_869; obj* x_870; obj* x_872; obj* x_874; obj* x_875; obj* x_878; obj* x_880; obj* x_881; obj* x_882; obj* x_883; 
x_859 = lean::cnstr_get(x_855, 0);
lean::inc(x_859);
lean::dec(x_855);
x_862 = lean::cnstr_get(x_1, 0);
lean::inc(x_862);
lean::dec(x_1);
x_865 = lean::cnstr_get(x_862, 2);
lean::inc(x_865);
lean::dec(x_862);
x_868 = l_lean_file__map_to__position(x_865, x_859);
x_869 = lean::box(0);
x_870 = lean::cnstr_get(x_868, 1);
lean::inc(x_870);
x_872 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_872);
x_874 = l_lean_kvmap_set__nat(x_869, x_872, x_870);
x_875 = lean::cnstr_get(x_868, 0);
lean::inc(x_875);
lean::dec(x_868);
x_878 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_878);
x_880 = l_lean_kvmap_set__nat(x_874, x_878, x_875);
x_881 = lean_expr_mk_mdata(x_880, x_854);
x_882 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_882, 0, x_881);
lean::cnstr_set(x_882, 1, x_2);
x_883 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_883, 0, x_882);
return x_883;
}
}
else
{
obj* x_886; obj* x_887; 
lean::dec(x_1);
lean::dec(x_0);
x_886 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_886, 0, x_854);
lean::cnstr_set(x_886, 1, x_2);
x_887 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_887, 0, x_886);
return x_887;
}
}
}
else
{
obj* x_889; obj* x_890; obj* x_893; obj* x_894; obj* x_898; 
lean::dec(x_9);
x_889 = l_lean_parser_term_borrowed_has__view;
x_890 = lean::cnstr_get(x_889, 0);
lean::inc(x_890);
lean::inc(x_0);
x_893 = lean::apply_1(x_890, x_0);
x_894 = lean::cnstr_get(x_893, 1);
lean::inc(x_894);
lean::dec(x_893);
lean::inc(x_1);
x_898 = l_lean_elaborator_to__pexpr___main(x_894, x_1, x_2);
if (lean::obj_tag(x_898) == 0)
{
obj* x_902; obj* x_904; obj* x_905; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_902 = lean::cnstr_get(x_898, 0);
lean::inc(x_902);
if (lean::is_shared(x_898)) {
 lean::dec(x_898);
 x_904 = lean::box(0);
} else {
 lean::cnstr_release(x_898, 0);
 x_904 = x_898;
}
if (lean::is_scalar(x_904)) {
 x_905 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_905 = x_904;
}
lean::cnstr_set(x_905, 0, x_902);
return x_905;
}
else
{
obj* x_906; obj* x_909; obj* x_911; obj* x_913; obj* x_914; obj* x_916; obj* x_917; 
x_906 = lean::cnstr_get(x_898, 0);
lean::inc(x_906);
lean::dec(x_898);
x_909 = lean::cnstr_get(x_906, 0);
lean::inc(x_909);
x_911 = lean::cnstr_get(x_906, 1);
lean::inc(x_911);
if (lean::is_shared(x_906)) {
 lean::dec(x_906);
 x_913 = lean::box(0);
} else {
 lean::cnstr_release(x_906, 0);
 lean::cnstr_release(x_906, 1);
 x_913 = x_906;
}
x_914 = l_lean_elaborator_to__pexpr___main___closed__32;
lean::inc(x_914);
x_916 = l_lean_elaborator_expr_mk__annotation(x_914, x_909);
if (lean::is_scalar(x_913)) {
 x_917 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_917 = x_913;
}
lean::cnstr_set(x_917, 0, x_916);
lean::cnstr_set(x_917, 1, x_911);
x_14 = x_917;
goto lbl_15;
}
}
}
else
{
obj* x_919; obj* x_920; obj* x_923; obj* x_924; obj* x_928; 
lean::dec(x_9);
x_919 = l_lean_parser_term_inaccessible_has__view;
x_920 = lean::cnstr_get(x_919, 0);
lean::inc(x_920);
lean::inc(x_0);
x_923 = lean::apply_1(x_920, x_0);
x_924 = lean::cnstr_get(x_923, 1);
lean::inc(x_924);
lean::dec(x_923);
lean::inc(x_1);
x_928 = l_lean_elaborator_to__pexpr___main(x_924, x_1, x_2);
if (lean::obj_tag(x_928) == 0)
{
obj* x_932; obj* x_934; obj* x_935; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_932 = lean::cnstr_get(x_928, 0);
lean::inc(x_932);
if (lean::is_shared(x_928)) {
 lean::dec(x_928);
 x_934 = lean::box(0);
} else {
 lean::cnstr_release(x_928, 0);
 x_934 = x_928;
}
if (lean::is_scalar(x_934)) {
 x_935 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_935 = x_934;
}
lean::cnstr_set(x_935, 0, x_932);
return x_935;
}
else
{
obj* x_936; obj* x_939; obj* x_941; obj* x_943; obj* x_944; obj* x_946; obj* x_947; 
x_936 = lean::cnstr_get(x_928, 0);
lean::inc(x_936);
lean::dec(x_928);
x_939 = lean::cnstr_get(x_936, 0);
lean::inc(x_939);
x_941 = lean::cnstr_get(x_936, 1);
lean::inc(x_941);
if (lean::is_shared(x_936)) {
 lean::dec(x_936);
 x_943 = lean::box(0);
} else {
 lean::cnstr_release(x_936, 0);
 lean::cnstr_release(x_936, 1);
 x_943 = x_936;
}
x_944 = l_lean_elaborator_to__pexpr___main___closed__33;
lean::inc(x_944);
x_946 = l_lean_elaborator_expr_mk__annotation(x_944, x_939);
if (lean::is_scalar(x_943)) {
 x_947 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_947 = x_943;
}
lean::cnstr_set(x_947, 0, x_946);
lean::cnstr_set(x_947, 1, x_941);
x_14 = x_947;
goto lbl_15;
}
}
}
else
{
obj* x_949; obj* x_950; obj* x_953; obj* x_954; obj* x_956; obj* x_957; obj* x_959; obj* x_962; 
lean::dec(x_9);
x_949 = l_lean_parser_term_explicit_has__view;
x_950 = lean::cnstr_get(x_949, 0);
lean::inc(x_950);
lean::inc(x_0);
x_953 = lean::apply_1(x_950, x_0);
x_954 = lean::cnstr_get(x_953, 0);
lean::inc(x_954);
x_956 = l_lean_parser_ident__univs_has__view;
x_957 = lean::cnstr_get(x_956, 1);
lean::inc(x_957);
x_959 = lean::cnstr_get(x_953, 1);
lean::inc(x_959);
lean::dec(x_953);
x_962 = lean::apply_1(x_957, x_959);
if (lean::obj_tag(x_954) == 0)
{
obj* x_965; 
lean::dec(x_954);
lean::inc(x_1);
x_965 = l_lean_elaborator_to__pexpr___main(x_962, x_1, x_2);
if (lean::obj_tag(x_965) == 0)
{
obj* x_969; obj* x_971; obj* x_972; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_969 = lean::cnstr_get(x_965, 0);
lean::inc(x_969);
if (lean::is_shared(x_965)) {
 lean::dec(x_965);
 x_971 = lean::box(0);
} else {
 lean::cnstr_release(x_965, 0);
 x_971 = x_965;
}
if (lean::is_scalar(x_971)) {
 x_972 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_972 = x_971;
}
lean::cnstr_set(x_972, 0, x_969);
return x_972;
}
else
{
obj* x_973; obj* x_976; obj* x_978; obj* x_980; obj* x_981; obj* x_983; obj* x_984; 
x_973 = lean::cnstr_get(x_965, 0);
lean::inc(x_973);
lean::dec(x_965);
x_976 = lean::cnstr_get(x_973, 0);
lean::inc(x_976);
x_978 = lean::cnstr_get(x_973, 1);
lean::inc(x_978);
if (lean::is_shared(x_973)) {
 lean::dec(x_973);
 x_980 = lean::box(0);
} else {
 lean::cnstr_release(x_973, 0);
 lean::cnstr_release(x_973, 1);
 x_980 = x_973;
}
x_981 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
lean::inc(x_981);
x_983 = l_lean_elaborator_expr_mk__annotation(x_981, x_976);
if (lean::is_scalar(x_980)) {
 x_984 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_984 = x_980;
}
lean::cnstr_set(x_984, 0, x_983);
lean::cnstr_set(x_984, 1, x_978);
x_14 = x_984;
goto lbl_15;
}
}
else
{
obj* x_987; 
lean::dec(x_954);
lean::inc(x_1);
x_987 = l_lean_elaborator_to__pexpr___main(x_962, x_1, x_2);
if (lean::obj_tag(x_987) == 0)
{
obj* x_991; obj* x_993; obj* x_994; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_991 = lean::cnstr_get(x_987, 0);
lean::inc(x_991);
if (lean::is_shared(x_987)) {
 lean::dec(x_987);
 x_993 = lean::box(0);
} else {
 lean::cnstr_release(x_987, 0);
 x_993 = x_987;
}
if (lean::is_scalar(x_993)) {
 x_994 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_994 = x_993;
}
lean::cnstr_set(x_994, 0, x_991);
return x_994;
}
else
{
obj* x_995; obj* x_998; obj* x_1000; obj* x_1002; obj* x_1003; obj* x_1005; obj* x_1006; 
x_995 = lean::cnstr_get(x_987, 0);
lean::inc(x_995);
lean::dec(x_987);
x_998 = lean::cnstr_get(x_995, 0);
lean::inc(x_998);
x_1000 = lean::cnstr_get(x_995, 1);
lean::inc(x_1000);
if (lean::is_shared(x_995)) {
 lean::dec(x_995);
 x_1002 = lean::box(0);
} else {
 lean::cnstr_release(x_995, 0);
 lean::cnstr_release(x_995, 1);
 x_1002 = x_995;
}
x_1003 = l_lean_elaborator_to__pexpr___main___closed__34;
lean::inc(x_1003);
x_1005 = l_lean_elaborator_expr_mk__annotation(x_1003, x_998);
if (lean::is_scalar(x_1002)) {
 x_1006 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1006 = x_1002;
}
lean::cnstr_set(x_1006, 0, x_1005);
lean::cnstr_set(x_1006, 1, x_1000);
x_14 = x_1006;
goto lbl_15;
}
}
}
}
else
{
obj* x_1008; obj* x_1009; obj* x_1012; obj* x_1013; obj* x_1015; 
lean::dec(x_9);
x_1008 = l_lean_parser_term_projection_has__view;
x_1009 = lean::cnstr_get(x_1008, 0);
lean::inc(x_1009);
lean::inc(x_0);
x_1012 = lean::apply_1(x_1009, x_0);
x_1013 = lean::cnstr_get(x_1012, 2);
lean::inc(x_1013);
x_1015 = lean::cnstr_get(x_1012, 0);
lean::inc(x_1015);
lean::dec(x_1012);
if (lean::obj_tag(x_1013) == 0)
{
obj* x_1018; obj* x_1022; 
x_1018 = lean::cnstr_get(x_1013, 0);
lean::inc(x_1018);
lean::dec(x_1013);
lean::inc(x_1);
x_1022 = l_lean_elaborator_to__pexpr___main(x_1015, x_1, x_2);
if (lean::obj_tag(x_1022) == 0)
{
obj* x_1027; obj* x_1029; obj* x_1030; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1018);
x_1027 = lean::cnstr_get(x_1022, 0);
lean::inc(x_1027);
if (lean::is_shared(x_1022)) {
 lean::dec(x_1022);
 x_1029 = lean::box(0);
} else {
 lean::cnstr_release(x_1022, 0);
 x_1029 = x_1022;
}
if (lean::is_scalar(x_1029)) {
 x_1030 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1030 = x_1029;
}
lean::cnstr_set(x_1030, 0, x_1027);
return x_1030;
}
else
{
obj* x_1031; obj* x_1034; obj* x_1036; obj* x_1038; obj* x_1039; obj* x_1042; obj* x_1043; obj* x_1044; obj* x_1046; obj* x_1047; obj* x_1048; 
x_1031 = lean::cnstr_get(x_1022, 0);
lean::inc(x_1031);
lean::dec(x_1022);
x_1034 = lean::cnstr_get(x_1031, 0);
lean::inc(x_1034);
x_1036 = lean::cnstr_get(x_1031, 1);
lean::inc(x_1036);
if (lean::is_shared(x_1031)) {
 lean::dec(x_1031);
 x_1038 = lean::box(0);
} else {
 lean::cnstr_release(x_1031, 0);
 lean::cnstr_release(x_1031, 1);
 x_1038 = x_1031;
}
x_1039 = lean::cnstr_get(x_1018, 2);
lean::inc(x_1039);
lean::dec(x_1018);
x_1042 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1042, 0, x_1039);
x_1043 = lean::box(0);
x_1044 = l_lean_elaborator_to__pexpr___main___closed__35;
lean::inc(x_1044);
x_1046 = l_lean_kvmap_insert__core___main(x_1043, x_1044, x_1042);
x_1047 = lean_expr_mk_mdata(x_1046, x_1034);
if (lean::is_scalar(x_1038)) {
 x_1048 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1048 = x_1038;
}
lean::cnstr_set(x_1048, 0, x_1047);
lean::cnstr_set(x_1048, 1, x_1036);
x_14 = x_1048;
goto lbl_15;
}
}
else
{
obj* x_1049; obj* x_1053; 
x_1049 = lean::cnstr_get(x_1013, 0);
lean::inc(x_1049);
lean::dec(x_1013);
lean::inc(x_1);
x_1053 = l_lean_elaborator_to__pexpr___main(x_1015, x_1, x_2);
if (lean::obj_tag(x_1053) == 0)
{
obj* x_1058; obj* x_1060; obj* x_1061; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1049);
x_1058 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1058);
if (lean::is_shared(x_1053)) {
 lean::dec(x_1053);
 x_1060 = lean::box(0);
} else {
 lean::cnstr_release(x_1053, 0);
 x_1060 = x_1053;
}
if (lean::is_scalar(x_1060)) {
 x_1061 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1061 = x_1060;
}
lean::cnstr_set(x_1061, 0, x_1058);
return x_1061;
}
else
{
obj* x_1062; obj* x_1065; obj* x_1067; obj* x_1069; obj* x_1070; obj* x_1071; obj* x_1072; obj* x_1073; obj* x_1075; obj* x_1076; obj* x_1077; 
x_1062 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1062);
lean::dec(x_1053);
x_1065 = lean::cnstr_get(x_1062, 0);
lean::inc(x_1065);
x_1067 = lean::cnstr_get(x_1062, 1);
lean::inc(x_1067);
if (lean::is_shared(x_1062)) {
 lean::dec(x_1062);
 x_1069 = lean::box(0);
} else {
 lean::cnstr_release(x_1062, 0);
 lean::cnstr_release(x_1062, 1);
 x_1069 = x_1062;
}
x_1070 = l_lean_parser_number_view_to__nat___main(x_1049);
x_1071 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1071, 0, x_1070);
x_1072 = lean::box(0);
x_1073 = l_lean_elaborator_to__pexpr___main___closed__35;
lean::inc(x_1073);
x_1075 = l_lean_kvmap_insert__core___main(x_1072, x_1073, x_1071);
x_1076 = lean_expr_mk_mdata(x_1075, x_1065);
if (lean::is_scalar(x_1069)) {
 x_1077 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1077 = x_1069;
}
lean::cnstr_set(x_1077, 0, x_1076);
lean::cnstr_set(x_1077, 1, x_1067);
x_14 = x_1077;
goto lbl_15;
}
}
}
}
else
{
obj* x_1079; obj* x_1080; obj* x_1083; obj* x_1084; 
lean::dec(x_9);
x_1079 = l_lean_parser_term_let_has__view;
x_1080 = lean::cnstr_get(x_1079, 0);
lean::inc(x_1080);
lean::inc(x_0);
x_1083 = lean::apply_1(x_1080, x_0);
x_1084 = lean::cnstr_get(x_1083, 1);
lean::inc(x_1084);
if (lean::obj_tag(x_1084) == 0)
{
obj* x_1086; obj* x_1089; obj* x_1091; obj* x_1093; 
x_1086 = lean::cnstr_get(x_1084, 0);
lean::inc(x_1086);
lean::dec(x_1084);
x_1089 = lean::cnstr_get(x_1086, 0);
lean::inc(x_1089);
x_1091 = lean::cnstr_get(x_1086, 1);
lean::inc(x_1091);
x_1093 = lean::cnstr_get(x_1086, 2);
lean::inc(x_1093);
lean::dec(x_1086);
if (lean::obj_tag(x_1091) == 0)
{
if (lean::obj_tag(x_1093) == 0)
{
obj* x_1098; obj* x_1102; 
lean::dec(x_1089);
lean::dec(x_1083);
x_1098 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_1098);
lean::inc(x_0);
x_1102 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1098, x_1, x_2);
if (lean::obj_tag(x_1102) == 0)
{
obj* x_1106; obj* x_1108; obj* x_1109; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1106 = lean::cnstr_get(x_1102, 0);
lean::inc(x_1106);
if (lean::is_shared(x_1102)) {
 lean::dec(x_1102);
 x_1108 = lean::box(0);
} else {
 lean::cnstr_release(x_1102, 0);
 x_1108 = x_1102;
}
if (lean::is_scalar(x_1108)) {
 x_1109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1109 = x_1108;
}
lean::cnstr_set(x_1109, 0, x_1106);
return x_1109;
}
else
{
obj* x_1110; 
x_1110 = lean::cnstr_get(x_1102, 0);
lean::inc(x_1110);
lean::dec(x_1102);
x_14 = x_1110;
goto lbl_15;
}
}
else
{
obj* x_1113; obj* x_1116; obj* x_1120; 
x_1113 = lean::cnstr_get(x_1093, 0);
lean::inc(x_1113);
lean::dec(x_1093);
x_1116 = lean::cnstr_get(x_1113, 1);
lean::inc(x_1116);
lean::dec(x_1113);
lean::inc(x_1);
x_1120 = l_lean_elaborator_to__pexpr___main(x_1116, x_1, x_2);
if (lean::obj_tag(x_1120) == 0)
{
obj* x_1126; obj* x_1128; obj* x_1129; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1089);
lean::dec(x_1083);
x_1126 = lean::cnstr_get(x_1120, 0);
lean::inc(x_1126);
if (lean::is_shared(x_1120)) {
 lean::dec(x_1120);
 x_1128 = lean::box(0);
} else {
 lean::cnstr_release(x_1120, 0);
 x_1128 = x_1120;
}
if (lean::is_scalar(x_1128)) {
 x_1129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1129 = x_1128;
}
lean::cnstr_set(x_1129, 0, x_1126);
return x_1129;
}
else
{
obj* x_1130; obj* x_1132; obj* x_1133; obj* x_1135; obj* x_1137; obj* x_1138; obj* x_1141; 
x_1130 = lean::cnstr_get(x_1120, 0);
lean::inc(x_1130);
if (lean::is_shared(x_1120)) {
 lean::dec(x_1120);
 x_1132 = lean::box(0);
} else {
 lean::cnstr_release(x_1120, 0);
 x_1132 = x_1120;
}
x_1133 = lean::cnstr_get(x_1130, 0);
lean::inc(x_1133);
x_1135 = lean::cnstr_get(x_1130, 1);
lean::inc(x_1135);
if (lean::is_shared(x_1130)) {
 lean::dec(x_1130);
 x_1137 = lean::box(0);
} else {
 lean::cnstr_release(x_1130, 0);
 lean::cnstr_release(x_1130, 1);
 x_1137 = x_1130;
}
x_1138 = lean::cnstr_get(x_1083, 3);
lean::inc(x_1138);
lean::inc(x_1);
x_1141 = l_lean_elaborator_to__pexpr___main(x_1138, x_1, x_1135);
if (lean::obj_tag(x_1141) == 0)
{
obj* x_1149; obj* x_1152; 
lean::dec(x_1133);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1137);
lean::dec(x_1089);
lean::dec(x_1083);
x_1149 = lean::cnstr_get(x_1141, 0);
lean::inc(x_1149);
lean::dec(x_1141);
if (lean::is_scalar(x_1132)) {
 x_1152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1152 = x_1132;
 lean::cnstr_set_tag(x_1132, 0);
}
lean::cnstr_set(x_1152, 0, x_1149);
return x_1152;
}
else
{
obj* x_1153; obj* x_1156; obj* x_1158; obj* x_1161; obj* x_1165; 
x_1153 = lean::cnstr_get(x_1141, 0);
lean::inc(x_1153);
lean::dec(x_1141);
x_1156 = lean::cnstr_get(x_1153, 0);
lean::inc(x_1156);
x_1158 = lean::cnstr_get(x_1153, 1);
lean::inc(x_1158);
lean::dec(x_1153);
x_1161 = lean::cnstr_get(x_1083, 5);
lean::inc(x_1161);
lean::dec(x_1083);
lean::inc(x_1);
x_1165 = l_lean_elaborator_to__pexpr___main(x_1161, x_1, x_1158);
if (lean::obj_tag(x_1165) == 0)
{
obj* x_1173; obj* x_1176; 
lean::dec(x_1133);
lean::dec(x_1156);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1137);
lean::dec(x_1089);
x_1173 = lean::cnstr_get(x_1165, 0);
lean::inc(x_1173);
lean::dec(x_1165);
if (lean::is_scalar(x_1132)) {
 x_1176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1176 = x_1132;
 lean::cnstr_set_tag(x_1132, 0);
}
lean::cnstr_set(x_1176, 0, x_1173);
return x_1176;
}
else
{
obj* x_1178; obj* x_1181; obj* x_1183; obj* x_1186; obj* x_1187; obj* x_1188; 
lean::dec(x_1132);
x_1178 = lean::cnstr_get(x_1165, 0);
lean::inc(x_1178);
lean::dec(x_1165);
x_1181 = lean::cnstr_get(x_1178, 0);
lean::inc(x_1181);
x_1183 = lean::cnstr_get(x_1178, 1);
lean::inc(x_1183);
lean::dec(x_1178);
x_1186 = l_lean_elaborator_mangle__ident(x_1089);
x_1187 = lean_expr_mk_let(x_1186, x_1133, x_1156, x_1181);
if (lean::is_scalar(x_1137)) {
 x_1188 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1188 = x_1137;
}
lean::cnstr_set(x_1188, 0, x_1187);
lean::cnstr_set(x_1188, 1, x_1183);
x_14 = x_1188;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1193; obj* x_1197; 
lean::dec(x_1093);
lean::dec(x_1089);
lean::dec(x_1091);
lean::dec(x_1083);
x_1193 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_1193);
lean::inc(x_0);
x_1197 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1193, x_1, x_2);
if (lean::obj_tag(x_1197) == 0)
{
obj* x_1201; obj* x_1203; obj* x_1204; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1201 = lean::cnstr_get(x_1197, 0);
lean::inc(x_1201);
if (lean::is_shared(x_1197)) {
 lean::dec(x_1197);
 x_1203 = lean::box(0);
} else {
 lean::cnstr_release(x_1197, 0);
 x_1203 = x_1197;
}
if (lean::is_scalar(x_1203)) {
 x_1204 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1204 = x_1203;
}
lean::cnstr_set(x_1204, 0, x_1201);
return x_1204;
}
else
{
obj* x_1205; 
x_1205 = lean::cnstr_get(x_1197, 0);
lean::inc(x_1205);
lean::dec(x_1197);
x_14 = x_1205;
goto lbl_15;
}
}
}
else
{
obj* x_1210; obj* x_1214; 
lean::dec(x_1083);
lean::dec(x_1084);
x_1210 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_1210);
lean::inc(x_0);
x_1214 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1210, x_1, x_2);
if (lean::obj_tag(x_1214) == 0)
{
obj* x_1218; obj* x_1220; obj* x_1221; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1218 = lean::cnstr_get(x_1214, 0);
lean::inc(x_1218);
if (lean::is_shared(x_1214)) {
 lean::dec(x_1214);
 x_1220 = lean::box(0);
} else {
 lean::cnstr_release(x_1214, 0);
 x_1220 = x_1214;
}
if (lean::is_scalar(x_1220)) {
 x_1221 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1221 = x_1220;
}
lean::cnstr_set(x_1221, 0, x_1218);
return x_1221;
}
else
{
obj* x_1222; 
x_1222 = lean::cnstr_get(x_1214, 0);
lean::inc(x_1222);
lean::dec(x_1214);
x_14 = x_1222;
goto lbl_15;
}
}
}
}
else
{
obj* x_1226; obj* x_1227; obj* x_1230; obj* x_1231; obj* x_1234; 
lean::dec(x_9);
x_1226 = l_lean_parser_term_show_has__view;
x_1227 = lean::cnstr_get(x_1226, 0);
lean::inc(x_1227);
lean::inc(x_0);
x_1230 = lean::apply_1(x_1227, x_0);
x_1231 = lean::cnstr_get(x_1230, 1);
lean::inc(x_1231);
lean::inc(x_1);
x_1234 = l_lean_elaborator_to__pexpr___main(x_1231, x_1, x_2);
if (lean::obj_tag(x_1234) == 0)
{
obj* x_1239; obj* x_1241; obj* x_1242; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1230);
x_1239 = lean::cnstr_get(x_1234, 0);
lean::inc(x_1239);
if (lean::is_shared(x_1234)) {
 lean::dec(x_1234);
 x_1241 = lean::box(0);
} else {
 lean::cnstr_release(x_1234, 0);
 x_1241 = x_1234;
}
if (lean::is_scalar(x_1241)) {
 x_1242 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1242 = x_1241;
}
lean::cnstr_set(x_1242, 0, x_1239);
return x_1242;
}
else
{
obj* x_1243; obj* x_1245; obj* x_1246; obj* x_1248; obj* x_1250; obj* x_1251; obj* x_1254; obj* x_1258; 
x_1243 = lean::cnstr_get(x_1234, 0);
lean::inc(x_1243);
if (lean::is_shared(x_1234)) {
 lean::dec(x_1234);
 x_1245 = lean::box(0);
} else {
 lean::cnstr_release(x_1234, 0);
 x_1245 = x_1234;
}
x_1246 = lean::cnstr_get(x_1243, 0);
lean::inc(x_1246);
x_1248 = lean::cnstr_get(x_1243, 1);
lean::inc(x_1248);
if (lean::is_shared(x_1243)) {
 lean::dec(x_1243);
 x_1250 = lean::box(0);
} else {
 lean::cnstr_release(x_1243, 0);
 lean::cnstr_release(x_1243, 1);
 x_1250 = x_1243;
}
x_1251 = lean::cnstr_get(x_1230, 3);
lean::inc(x_1251);
lean::dec(x_1230);
x_1254 = lean::cnstr_get(x_1251, 1);
lean::inc(x_1254);
lean::dec(x_1251);
lean::inc(x_1);
x_1258 = l_lean_elaborator_to__pexpr___main(x_1254, x_1, x_1248);
if (lean::obj_tag(x_1258) == 0)
{
obj* x_1264; obj* x_1267; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1246);
lean::dec(x_1250);
x_1264 = lean::cnstr_get(x_1258, 0);
lean::inc(x_1264);
lean::dec(x_1258);
if (lean::is_scalar(x_1245)) {
 x_1267 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1267 = x_1245;
 lean::cnstr_set_tag(x_1245, 0);
}
lean::cnstr_set(x_1267, 0, x_1264);
return x_1267;
}
else
{
obj* x_1269; obj* x_1272; obj* x_1274; obj* x_1277; uint8 x_1278; obj* x_1279; obj* x_1282; obj* x_1283; obj* x_1284; obj* x_1286; obj* x_1287; 
lean::dec(x_1245);
x_1269 = lean::cnstr_get(x_1258, 0);
lean::inc(x_1269);
lean::dec(x_1258);
x_1272 = lean::cnstr_get(x_1269, 0);
lean::inc(x_1272);
x_1274 = lean::cnstr_get(x_1269, 1);
lean::inc(x_1274);
lean::dec(x_1269);
x_1277 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1278 = 0;
x_1279 = l_lean_elaborator_to__pexpr___main___closed__38;
lean::inc(x_1279);
lean::inc(x_1277);
x_1282 = lean_expr_mk_lambda(x_1277, x_1278, x_1246, x_1279);
x_1283 = lean_expr_mk_app(x_1282, x_1272);
x_1284 = l_lean_elaborator_to__pexpr___main___closed__39;
lean::inc(x_1284);
x_1286 = l_lean_elaborator_expr_mk__annotation(x_1284, x_1283);
if (lean::is_scalar(x_1250)) {
 x_1287 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1287 = x_1250;
}
lean::cnstr_set(x_1287, 0, x_1286);
lean::cnstr_set(x_1287, 1, x_1274);
x_14 = x_1287;
goto lbl_15;
}
}
}
}
else
{
obj* x_1289; obj* x_1290; obj* x_1293; obj* x_1294; obj* x_1296; obj* x_1299; 
lean::dec(x_9);
x_1289 = l_lean_parser_term_have_has__view;
x_1290 = lean::cnstr_get(x_1289, 0);
lean::inc(x_1290);
lean::inc(x_0);
x_1293 = lean::apply_1(x_1290, x_0);
x_1296 = lean::cnstr_get(x_1293, 2);
lean::inc(x_1296);
lean::inc(x_1);
x_1299 = l_lean_elaborator_to__pexpr___main(x_1296, x_1, x_2);
if (lean::obj_tag(x_1299) == 0)
{
obj* x_1304; obj* x_1306; obj* x_1307; 
lean::dec(x_1293);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1304 = lean::cnstr_get(x_1299, 0);
lean::inc(x_1304);
if (lean::is_shared(x_1299)) {
 lean::dec(x_1299);
 x_1306 = lean::box(0);
} else {
 lean::cnstr_release(x_1299, 0);
 x_1306 = x_1299;
}
if (lean::is_scalar(x_1306)) {
 x_1307 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1307 = x_1306;
}
lean::cnstr_set(x_1307, 0, x_1304);
return x_1307;
}
else
{
obj* x_1308; obj* x_1310; obj* x_1311; obj* x_1313; obj* x_1315; obj* x_1316; obj* x_1319; 
x_1308 = lean::cnstr_get(x_1299, 0);
lean::inc(x_1308);
if (lean::is_shared(x_1299)) {
 lean::dec(x_1299);
 x_1310 = lean::box(0);
} else {
 lean::cnstr_release(x_1299, 0);
 x_1310 = x_1299;
}
x_1311 = lean::cnstr_get(x_1308, 0);
lean::inc(x_1311);
x_1313 = lean::cnstr_get(x_1308, 1);
lean::inc(x_1313);
if (lean::is_shared(x_1308)) {
 lean::dec(x_1308);
 x_1315 = lean::box(0);
} else {
 lean::cnstr_release(x_1308, 0);
 lean::cnstr_release(x_1308, 1);
 x_1315 = x_1308;
}
x_1316 = lean::cnstr_get(x_1293, 5);
lean::inc(x_1316);
lean::inc(x_1);
x_1319 = l_lean_elaborator_to__pexpr___main(x_1316, x_1, x_1313);
if (lean::obj_tag(x_1319) == 0)
{
obj* x_1326; obj* x_1329; 
lean::dec(x_1293);
lean::dec(x_1311);
lean::dec(x_1315);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1326 = lean::cnstr_get(x_1319, 0);
lean::inc(x_1326);
lean::dec(x_1319);
if (lean::is_scalar(x_1310)) {
 x_1329 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1329 = x_1310;
 lean::cnstr_set_tag(x_1310, 0);
}
lean::cnstr_set(x_1329, 0, x_1326);
return x_1329;
}
else
{
obj* x_1331; obj* x_1334; obj* x_1336; obj* x_1339; obj* x_1341; obj* x_1343; obj* x_1344; obj* x_1346; obj* x_1347; obj* x_1349; uint8 x_1350; obj* x_1351; obj* x_1352; 
lean::dec(x_1310);
x_1331 = lean::cnstr_get(x_1319, 0);
lean::inc(x_1331);
lean::dec(x_1319);
x_1334 = lean::cnstr_get(x_1331, 0);
lean::inc(x_1334);
x_1336 = lean::cnstr_get(x_1331, 1);
lean::inc(x_1336);
lean::dec(x_1331);
x_1339 = lean::cnstr_get(x_1293, 1);
lean::inc(x_1339);
x_1341 = l_lean_elaborator_to__pexpr___main___closed__41;
lean::inc(x_1341);
x_1343 = l_option_map___rarg(x_1341, x_1339);
x_1344 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_1344);
x_1346 = l_option_map___rarg(x_1344, x_1343);
x_1347 = l_lean_elaborator_to__pexpr___main___closed__37;
lean::inc(x_1347);
x_1349 = l_option_get__or__else___main___rarg(x_1346, x_1347);
x_1350 = 0;
x_1351 = lean_expr_mk_lambda(x_1349, x_1350, x_1311, x_1334);
if (lean::is_scalar(x_1315)) {
 x_1352 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1352 = x_1315;
}
lean::cnstr_set(x_1352, 0, x_1351);
lean::cnstr_set(x_1352, 1, x_1336);
x_1294 = x_1352;
goto lbl_1295;
}
}
lbl_1295:
{
obj* x_1353; obj* x_1355; obj* x_1357; obj* x_1358; 
x_1353 = lean::cnstr_get(x_1294, 0);
lean::inc(x_1353);
x_1355 = lean::cnstr_get(x_1294, 1);
lean::inc(x_1355);
if (lean::is_shared(x_1294)) {
 lean::dec(x_1294);
 x_1357 = lean::box(0);
} else {
 lean::cnstr_release(x_1294, 0);
 lean::cnstr_release(x_1294, 1);
 x_1357 = x_1294;
}
x_1358 = lean::cnstr_get(x_1293, 3);
lean::inc(x_1358);
lean::dec(x_1293);
if (lean::obj_tag(x_1358) == 0)
{
obj* x_1361; obj* x_1364; obj* x_1368; 
x_1361 = lean::cnstr_get(x_1358, 0);
lean::inc(x_1361);
lean::dec(x_1358);
x_1364 = lean::cnstr_get(x_1361, 1);
lean::inc(x_1364);
lean::dec(x_1361);
lean::inc(x_1);
x_1368 = l_lean_elaborator_to__pexpr___main(x_1364, x_1, x_1355);
if (lean::obj_tag(x_1368) == 0)
{
obj* x_1374; obj* x_1376; obj* x_1377; 
lean::dec(x_7);
lean::dec(x_1357);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1353);
x_1374 = lean::cnstr_get(x_1368, 0);
lean::inc(x_1374);
if (lean::is_shared(x_1368)) {
 lean::dec(x_1368);
 x_1376 = lean::box(0);
} else {
 lean::cnstr_release(x_1368, 0);
 x_1376 = x_1368;
}
if (lean::is_scalar(x_1376)) {
 x_1377 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1377 = x_1376;
}
lean::cnstr_set(x_1377, 0, x_1374);
return x_1377;
}
else
{
obj* x_1378; obj* x_1381; obj* x_1383; obj* x_1386; obj* x_1388; obj* x_1389; obj* x_1390; 
x_1378 = lean::cnstr_get(x_1368, 0);
lean::inc(x_1378);
lean::dec(x_1368);
x_1381 = lean::cnstr_get(x_1378, 0);
lean::inc(x_1381);
x_1383 = lean::cnstr_get(x_1378, 1);
lean::inc(x_1383);
lean::dec(x_1378);
x_1386 = l_lean_elaborator_to__pexpr___main___closed__40;
lean::inc(x_1386);
x_1388 = l_lean_elaborator_expr_mk__annotation(x_1386, x_1353);
x_1389 = lean_expr_mk_app(x_1388, x_1381);
if (lean::is_scalar(x_1357)) {
 x_1390 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1390 = x_1357;
}
lean::cnstr_set(x_1390, 0, x_1389);
lean::cnstr_set(x_1390, 1, x_1383);
x_14 = x_1390;
goto lbl_15;
}
}
else
{
obj* x_1391; obj* x_1394; obj* x_1397; obj* x_1401; 
x_1391 = lean::cnstr_get(x_1358, 0);
lean::inc(x_1391);
lean::dec(x_1358);
x_1394 = lean::cnstr_get(x_1391, 1);
lean::inc(x_1394);
lean::dec(x_1391);
x_1397 = lean::cnstr_get(x_1394, 1);
lean::inc(x_1397);
lean::dec(x_1394);
lean::inc(x_1);
x_1401 = l_lean_elaborator_to__pexpr___main(x_1397, x_1, x_1355);
if (lean::obj_tag(x_1401) == 0)
{
obj* x_1407; obj* x_1409; obj* x_1410; 
lean::dec(x_7);
lean::dec(x_1357);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1353);
x_1407 = lean::cnstr_get(x_1401, 0);
lean::inc(x_1407);
if (lean::is_shared(x_1401)) {
 lean::dec(x_1401);
 x_1409 = lean::box(0);
} else {
 lean::cnstr_release(x_1401, 0);
 x_1409 = x_1401;
}
if (lean::is_scalar(x_1409)) {
 x_1410 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1410 = x_1409;
}
lean::cnstr_set(x_1410, 0, x_1407);
return x_1410;
}
else
{
obj* x_1411; obj* x_1414; obj* x_1416; obj* x_1419; obj* x_1421; obj* x_1422; obj* x_1423; 
x_1411 = lean::cnstr_get(x_1401, 0);
lean::inc(x_1411);
lean::dec(x_1401);
x_1414 = lean::cnstr_get(x_1411, 0);
lean::inc(x_1414);
x_1416 = lean::cnstr_get(x_1411, 1);
lean::inc(x_1416);
lean::dec(x_1411);
x_1419 = l_lean_elaborator_to__pexpr___main___closed__40;
lean::inc(x_1419);
x_1421 = l_lean_elaborator_expr_mk__annotation(x_1419, x_1353);
x_1422 = lean_expr_mk_app(x_1421, x_1414);
if (lean::is_scalar(x_1357)) {
 x_1423 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1423 = x_1357;
}
lean::cnstr_set(x_1423, 0, x_1422);
lean::cnstr_set(x_1423, 1, x_1416);
x_14 = x_1423;
goto lbl_15;
}
}
}
}
}
else
{
lean::dec(x_9);
lean::dec(x_7);
if (x_21 == 0)
{
obj* x_1426; 
x_1426 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1426) == 0)
{
obj* x_1428; obj* x_1430; obj* x_1431; 
lean::dec(x_1);
x_1428 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_1428);
x_1430 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1430, 0, x_1428);
lean::cnstr_set(x_1430, 1, x_2);
x_1431 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1431, 0, x_1430);
return x_1431;
}
else
{
obj* x_1432; obj* x_1435; obj* x_1438; obj* x_1441; obj* x_1442; obj* x_1443; obj* x_1445; obj* x_1447; obj* x_1448; obj* x_1451; obj* x_1453; obj* x_1454; obj* x_1456; obj* x_1457; obj* x_1458; 
x_1432 = lean::cnstr_get(x_1426, 0);
lean::inc(x_1432);
lean::dec(x_1426);
x_1435 = lean::cnstr_get(x_1, 0);
lean::inc(x_1435);
lean::dec(x_1);
x_1438 = lean::cnstr_get(x_1435, 2);
lean::inc(x_1438);
lean::dec(x_1435);
x_1441 = l_lean_file__map_to__position(x_1438, x_1432);
x_1442 = lean::box(0);
x_1443 = lean::cnstr_get(x_1441, 1);
lean::inc(x_1443);
x_1445 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1445);
x_1447 = l_lean_kvmap_set__nat(x_1442, x_1445, x_1443);
x_1448 = lean::cnstr_get(x_1441, 0);
lean::inc(x_1448);
lean::dec(x_1441);
x_1451 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1451);
x_1453 = l_lean_kvmap_set__nat(x_1447, x_1451, x_1448);
x_1454 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_1454);
x_1456 = lean_expr_mk_mdata(x_1453, x_1454);
x_1457 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1457, 0, x_1456);
lean::cnstr_set(x_1457, 1, x_2);
x_1458 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1458, 0, x_1457);
return x_1458;
}
}
else
{
obj* x_1461; obj* x_1463; obj* x_1464; 
lean::dec(x_1);
lean::dec(x_0);
x_1461 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_1461);
x_1463 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1463, 0, x_1461);
lean::cnstr_set(x_1463, 1, x_2);
x_1464 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1464, 0, x_1463);
return x_1464;
}
}
}
else
{
obj* x_1466; obj* x_1467; obj* x_1470; obj* x_1471; obj* x_1474; obj* x_1475; obj* x_1477; obj* x_1479; 
lean::dec(x_9);
x_1466 = l_lean_parser_term_anonymous__constructor_has__view;
x_1467 = lean::cnstr_get(x_1466, 0);
lean::inc(x_1467);
lean::inc(x_0);
x_1470 = lean::apply_1(x_1467, x_0);
x_1471 = lean::cnstr_get(x_1470, 1);
lean::inc(x_1471);
lean::dec(x_1470);
x_1474 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_1471);
x_1475 = l_lean_expander_get__opt__type___main___closed__1;
lean::inc(x_1475);
x_1477 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_1475, x_1474);
lean::inc(x_1);
x_1479 = l_lean_elaborator_to__pexpr___main(x_1477, x_1, x_2);
if (lean::obj_tag(x_1479) == 0)
{
obj* x_1483; obj* x_1485; obj* x_1486; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1483 = lean::cnstr_get(x_1479, 0);
lean::inc(x_1483);
if (lean::is_shared(x_1479)) {
 lean::dec(x_1479);
 x_1485 = lean::box(0);
} else {
 lean::cnstr_release(x_1479, 0);
 x_1485 = x_1479;
}
if (lean::is_scalar(x_1485)) {
 x_1486 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1486 = x_1485;
}
lean::cnstr_set(x_1486, 0, x_1483);
return x_1486;
}
else
{
obj* x_1487; obj* x_1490; obj* x_1492; obj* x_1494; obj* x_1495; obj* x_1497; obj* x_1498; 
x_1487 = lean::cnstr_get(x_1479, 0);
lean::inc(x_1487);
lean::dec(x_1479);
x_1490 = lean::cnstr_get(x_1487, 0);
lean::inc(x_1490);
x_1492 = lean::cnstr_get(x_1487, 1);
lean::inc(x_1492);
if (lean::is_shared(x_1487)) {
 lean::dec(x_1487);
 x_1494 = lean::box(0);
} else {
 lean::cnstr_release(x_1487, 0);
 lean::cnstr_release(x_1487, 1);
 x_1494 = x_1487;
}
x_1495 = l_lean_elaborator_to__pexpr___main___closed__43;
lean::inc(x_1495);
x_1497 = l_lean_elaborator_expr_mk__annotation(x_1495, x_1490);
if (lean::is_scalar(x_1494)) {
 x_1498 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1498 = x_1494;
}
lean::cnstr_set(x_1498, 0, x_1497);
lean::cnstr_set(x_1498, 1, x_1492);
x_14 = x_1498;
goto lbl_15;
}
}
}
else
{
obj* x_1500; obj* x_1501; obj* x_1504; obj* x_1505; obj* x_1506; obj* x_1508; obj* x_1510; 
lean::dec(x_9);
x_1500 = l_lean_parser_term_sort__app_has__view;
x_1501 = lean::cnstr_get(x_1500, 0);
lean::inc(x_1501);
lean::inc(x_0);
x_1504 = lean::apply_1(x_1501, x_0);
x_1505 = l_lean_parser_term_sort_has__view;
x_1506 = lean::cnstr_get(x_1505, 0);
lean::inc(x_1506);
x_1508 = lean::cnstr_get(x_1504, 0);
lean::inc(x_1508);
x_1510 = lean::apply_1(x_1506, x_1508);
if (lean::obj_tag(x_1510) == 0)
{
obj* x_1512; obj* x_1516; 
lean::dec(x_1510);
x_1512 = lean::cnstr_get(x_1504, 1);
lean::inc(x_1512);
lean::dec(x_1504);
lean::inc(x_1);
x_1516 = l_lean_elaborator_to__level___main(x_1512, x_1, x_2);
if (lean::obj_tag(x_1516) == 0)
{
obj* x_1520; obj* x_1522; obj* x_1523; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1520 = lean::cnstr_get(x_1516, 0);
lean::inc(x_1520);
if (lean::is_shared(x_1516)) {
 lean::dec(x_1516);
 x_1522 = lean::box(0);
} else {
 lean::cnstr_release(x_1516, 0);
 x_1522 = x_1516;
}
if (lean::is_scalar(x_1522)) {
 x_1523 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1523 = x_1522;
}
lean::cnstr_set(x_1523, 0, x_1520);
return x_1523;
}
else
{
obj* x_1524; obj* x_1527; obj* x_1529; obj* x_1531; obj* x_1532; obj* x_1533; 
x_1524 = lean::cnstr_get(x_1516, 0);
lean::inc(x_1524);
lean::dec(x_1516);
x_1527 = lean::cnstr_get(x_1524, 0);
lean::inc(x_1527);
x_1529 = lean::cnstr_get(x_1524, 1);
lean::inc(x_1529);
if (lean::is_shared(x_1524)) {
 lean::dec(x_1524);
 x_1531 = lean::box(0);
} else {
 lean::cnstr_release(x_1524, 0);
 lean::cnstr_release(x_1524, 1);
 x_1531 = x_1524;
}
x_1532 = lean_expr_mk_sort(x_1527);
if (lean::is_scalar(x_1531)) {
 x_1533 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1533 = x_1531;
}
lean::cnstr_set(x_1533, 0, x_1532);
lean::cnstr_set(x_1533, 1, x_1529);
x_14 = x_1533;
goto lbl_15;
}
}
else
{
obj* x_1535; obj* x_1539; 
lean::dec(x_1510);
x_1535 = lean::cnstr_get(x_1504, 1);
lean::inc(x_1535);
lean::dec(x_1504);
lean::inc(x_1);
x_1539 = l_lean_elaborator_to__level___main(x_1535, x_1, x_2);
if (lean::obj_tag(x_1539) == 0)
{
obj* x_1543; obj* x_1545; obj* x_1546; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1543 = lean::cnstr_get(x_1539, 0);
lean::inc(x_1543);
if (lean::is_shared(x_1539)) {
 lean::dec(x_1539);
 x_1545 = lean::box(0);
} else {
 lean::cnstr_release(x_1539, 0);
 x_1545 = x_1539;
}
if (lean::is_scalar(x_1545)) {
 x_1546 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1546 = x_1545;
}
lean::cnstr_set(x_1546, 0, x_1543);
return x_1546;
}
else
{
obj* x_1547; obj* x_1550; obj* x_1552; obj* x_1554; obj* x_1555; obj* x_1556; obj* x_1557; 
x_1547 = lean::cnstr_get(x_1539, 0);
lean::inc(x_1547);
lean::dec(x_1539);
x_1550 = lean::cnstr_get(x_1547, 0);
lean::inc(x_1550);
x_1552 = lean::cnstr_get(x_1547, 1);
lean::inc(x_1552);
if (lean::is_shared(x_1547)) {
 lean::dec(x_1547);
 x_1554 = lean::box(0);
} else {
 lean::cnstr_release(x_1547, 0);
 lean::cnstr_release(x_1547, 1);
 x_1554 = x_1547;
}
x_1555 = level_mk_succ(x_1550);
x_1556 = lean_expr_mk_sort(x_1555);
if (lean::is_scalar(x_1554)) {
 x_1557 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1557 = x_1554;
}
lean::cnstr_set(x_1557, 0, x_1556);
lean::cnstr_set(x_1557, 1, x_1552);
x_14 = x_1557;
goto lbl_15;
}
}
}
}
else
{
obj* x_1560; obj* x_1561; obj* x_1564; 
lean::dec(x_9);
lean::dec(x_7);
x_1560 = l_lean_parser_term_sort_has__view;
x_1561 = lean::cnstr_get(x_1560, 0);
lean::inc(x_1561);
lean::inc(x_0);
x_1564 = lean::apply_1(x_1561, x_0);
if (lean::obj_tag(x_1564) == 0)
{
lean::dec(x_1564);
if (x_21 == 0)
{
obj* x_1566; 
x_1566 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1566) == 0)
{
obj* x_1568; obj* x_1570; obj* x_1571; 
lean::dec(x_1);
x_1568 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_1568);
x_1570 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1570, 0, x_1568);
lean::cnstr_set(x_1570, 1, x_2);
x_1571 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1571, 0, x_1570);
return x_1571;
}
else
{
obj* x_1572; obj* x_1575; obj* x_1578; obj* x_1581; obj* x_1582; obj* x_1583; obj* x_1585; obj* x_1587; obj* x_1588; obj* x_1591; obj* x_1593; obj* x_1594; obj* x_1596; obj* x_1597; obj* x_1598; 
x_1572 = lean::cnstr_get(x_1566, 0);
lean::inc(x_1572);
lean::dec(x_1566);
x_1575 = lean::cnstr_get(x_1, 0);
lean::inc(x_1575);
lean::dec(x_1);
x_1578 = lean::cnstr_get(x_1575, 2);
lean::inc(x_1578);
lean::dec(x_1575);
x_1581 = l_lean_file__map_to__position(x_1578, x_1572);
x_1582 = lean::box(0);
x_1583 = lean::cnstr_get(x_1581, 1);
lean::inc(x_1583);
x_1585 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1585);
x_1587 = l_lean_kvmap_set__nat(x_1582, x_1585, x_1583);
x_1588 = lean::cnstr_get(x_1581, 0);
lean::inc(x_1588);
lean::dec(x_1581);
x_1591 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1591);
x_1593 = l_lean_kvmap_set__nat(x_1587, x_1591, x_1588);
x_1594 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_1594);
x_1596 = lean_expr_mk_mdata(x_1593, x_1594);
x_1597 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1597, 0, x_1596);
lean::cnstr_set(x_1597, 1, x_2);
x_1598 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1598, 0, x_1597);
return x_1598;
}
}
else
{
obj* x_1601; obj* x_1603; obj* x_1604; 
lean::dec(x_1);
lean::dec(x_0);
x_1601 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_1601);
x_1603 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1603, 0, x_1601);
lean::cnstr_set(x_1603, 1, x_2);
x_1604 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1604, 0, x_1603);
return x_1604;
}
}
else
{
lean::dec(x_1564);
if (x_21 == 0)
{
obj* x_1606; 
x_1606 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1606) == 0)
{
obj* x_1608; obj* x_1610; obj* x_1611; 
lean::dec(x_1);
x_1608 = l_lean_elaborator_to__pexpr___main___closed__44;
lean::inc(x_1608);
x_1610 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1610, 0, x_1608);
lean::cnstr_set(x_1610, 1, x_2);
x_1611 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1611, 0, x_1610);
return x_1611;
}
else
{
obj* x_1612; obj* x_1615; obj* x_1618; obj* x_1621; obj* x_1622; obj* x_1623; obj* x_1625; obj* x_1627; obj* x_1628; obj* x_1631; obj* x_1633; obj* x_1634; obj* x_1636; obj* x_1637; obj* x_1638; 
x_1612 = lean::cnstr_get(x_1606, 0);
lean::inc(x_1612);
lean::dec(x_1606);
x_1615 = lean::cnstr_get(x_1, 0);
lean::inc(x_1615);
lean::dec(x_1);
x_1618 = lean::cnstr_get(x_1615, 2);
lean::inc(x_1618);
lean::dec(x_1615);
x_1621 = l_lean_file__map_to__position(x_1618, x_1612);
x_1622 = lean::box(0);
x_1623 = lean::cnstr_get(x_1621, 1);
lean::inc(x_1623);
x_1625 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1625);
x_1627 = l_lean_kvmap_set__nat(x_1622, x_1625, x_1623);
x_1628 = lean::cnstr_get(x_1621, 0);
lean::inc(x_1628);
lean::dec(x_1621);
x_1631 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1631);
x_1633 = l_lean_kvmap_set__nat(x_1627, x_1631, x_1628);
x_1634 = l_lean_elaborator_to__pexpr___main___closed__44;
lean::inc(x_1634);
x_1636 = lean_expr_mk_mdata(x_1633, x_1634);
x_1637 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1637, 0, x_1636);
lean::cnstr_set(x_1637, 1, x_2);
x_1638 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1638, 0, x_1637);
return x_1638;
}
}
else
{
obj* x_1641; obj* x_1643; obj* x_1644; 
lean::dec(x_1);
lean::dec(x_0);
x_1641 = l_lean_elaborator_to__pexpr___main___closed__44;
lean::inc(x_1641);
x_1643 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1643, 0, x_1641);
lean::cnstr_set(x_1643, 1, x_2);
x_1644 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1644, 0, x_1643);
return x_1644;
}
}
}
}
else
{
obj* x_1646; obj* x_1647; obj* x_1650; obj* x_1651; 
lean::dec(x_9);
x_1646 = l_lean_parser_term_pi_has__view;
x_1647 = lean::cnstr_get(x_1646, 0);
lean::inc(x_1647);
lean::inc(x_0);
x_1650 = lean::apply_1(x_1647, x_0);
x_1651 = lean::cnstr_get(x_1650, 1);
lean::inc(x_1651);
if (lean::obj_tag(x_1651) == 0)
{
obj* x_1655; obj* x_1659; 
lean::dec(x_1650);
lean::dec(x_1651);
x_1655 = l_lean_elaborator_to__pexpr___main___closed__45;
lean::inc(x_1);
lean::inc(x_1655);
lean::inc(x_0);
x_1659 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1655, x_1, x_2);
if (lean::obj_tag(x_1659) == 0)
{
obj* x_1663; obj* x_1665; obj* x_1666; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1663 = lean::cnstr_get(x_1659, 0);
lean::inc(x_1663);
if (lean::is_shared(x_1659)) {
 lean::dec(x_1659);
 x_1665 = lean::box(0);
} else {
 lean::cnstr_release(x_1659, 0);
 x_1665 = x_1659;
}
if (lean::is_scalar(x_1665)) {
 x_1666 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1666 = x_1665;
}
lean::cnstr_set(x_1666, 0, x_1663);
return x_1666;
}
else
{
obj* x_1667; 
x_1667 = lean::cnstr_get(x_1659, 0);
lean::inc(x_1667);
lean::dec(x_1659);
x_14 = x_1667;
goto lbl_15;
}
}
else
{
obj* x_1670; obj* x_1673; obj* x_1674; obj* x_1676; obj* x_1678; obj* x_1679; obj* x_1681; obj* x_1685; 
x_1670 = lean::cnstr_get(x_1651, 0);
lean::inc(x_1670);
lean::dec(x_1651);
x_1673 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1670);
x_1674 = lean::cnstr_get(x_1673, 0);
lean::inc(x_1674);
x_1676 = lean::cnstr_get(x_1673, 1);
lean::inc(x_1676);
if (lean::is_shared(x_1673)) {
 lean::dec(x_1673);
 x_1678 = lean::box(0);
} else {
 lean::cnstr_release(x_1673, 0);
 lean::cnstr_release(x_1673, 1);
 x_1678 = x_1673;
}
x_1679 = lean::cnstr_get(x_1676, 0);
lean::inc(x_1679);
x_1681 = lean::cnstr_get(x_1676, 1);
lean::inc(x_1681);
lean::dec(x_1676);
lean::inc(x_1);
x_1685 = l_lean_elaborator_to__pexpr___main(x_1681, x_1, x_2);
if (lean::obj_tag(x_1685) == 0)
{
obj* x_1693; obj* x_1695; obj* x_1696; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1650);
lean::dec(x_1678);
lean::dec(x_1674);
lean::dec(x_1679);
x_1693 = lean::cnstr_get(x_1685, 0);
lean::inc(x_1693);
if (lean::is_shared(x_1685)) {
 lean::dec(x_1685);
 x_1695 = lean::box(0);
} else {
 lean::cnstr_release(x_1685, 0);
 x_1695 = x_1685;
}
if (lean::is_scalar(x_1695)) {
 x_1696 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1696 = x_1695;
}
lean::cnstr_set(x_1696, 0, x_1693);
return x_1696;
}
else
{
obj* x_1697; obj* x_1699; obj* x_1700; obj* x_1702; obj* x_1705; obj* x_1709; 
x_1697 = lean::cnstr_get(x_1685, 0);
lean::inc(x_1697);
if (lean::is_shared(x_1685)) {
 lean::dec(x_1685);
 x_1699 = lean::box(0);
} else {
 lean::cnstr_release(x_1685, 0);
 x_1699 = x_1685;
}
x_1700 = lean::cnstr_get(x_1697, 0);
lean::inc(x_1700);
x_1702 = lean::cnstr_get(x_1697, 1);
lean::inc(x_1702);
lean::dec(x_1697);
x_1705 = lean::cnstr_get(x_1650, 3);
lean::inc(x_1705);
lean::dec(x_1650);
lean::inc(x_1);
x_1709 = l_lean_elaborator_to__pexpr___main(x_1705, x_1, x_1702);
if (lean::obj_tag(x_1709) == 0)
{
obj* x_1717; obj* x_1720; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1678);
lean::dec(x_1674);
lean::dec(x_1679);
lean::dec(x_1700);
x_1717 = lean::cnstr_get(x_1709, 0);
lean::inc(x_1717);
lean::dec(x_1709);
if (lean::is_scalar(x_1699)) {
 x_1720 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1720 = x_1699;
 lean::cnstr_set_tag(x_1699, 0);
}
lean::cnstr_set(x_1720, 0, x_1717);
return x_1720;
}
else
{
obj* x_1722; obj* x_1725; obj* x_1727; obj* x_1730; uint8 x_1731; obj* x_1733; obj* x_1734; 
lean::dec(x_1699);
x_1722 = lean::cnstr_get(x_1709, 0);
lean::inc(x_1722);
lean::dec(x_1709);
x_1725 = lean::cnstr_get(x_1722, 0);
lean::inc(x_1725);
x_1727 = lean::cnstr_get(x_1722, 1);
lean::inc(x_1727);
lean::dec(x_1722);
x_1730 = l_lean_elaborator_mangle__ident(x_1679);
x_1731 = lean::unbox(x_1674);
lean::dec(x_1674);
x_1733 = lean_expr_mk_pi(x_1730, x_1731, x_1700, x_1725);
if (lean::is_scalar(x_1678)) {
 x_1734 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1734 = x_1678;
}
lean::cnstr_set(x_1734, 0, x_1733);
lean::cnstr_set(x_1734, 1, x_1727);
x_14 = x_1734;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1736; obj* x_1737; obj* x_1740; obj* x_1741; 
lean::dec(x_9);
x_1736 = l_lean_parser_term_lambda_has__view;
x_1737 = lean::cnstr_get(x_1736, 0);
lean::inc(x_1737);
lean::inc(x_0);
x_1740 = lean::apply_1(x_1737, x_0);
x_1741 = lean::cnstr_get(x_1740, 1);
lean::inc(x_1741);
if (lean::obj_tag(x_1741) == 0)
{
obj* x_1745; obj* x_1749; 
lean::dec(x_1741);
lean::dec(x_1740);
x_1745 = l_lean_elaborator_to__pexpr___main___closed__46;
lean::inc(x_1);
lean::inc(x_1745);
lean::inc(x_0);
x_1749 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1745, x_1, x_2);
if (lean::obj_tag(x_1749) == 0)
{
obj* x_1753; obj* x_1755; obj* x_1756; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1753 = lean::cnstr_get(x_1749, 0);
lean::inc(x_1753);
if (lean::is_shared(x_1749)) {
 lean::dec(x_1749);
 x_1755 = lean::box(0);
} else {
 lean::cnstr_release(x_1749, 0);
 x_1755 = x_1749;
}
if (lean::is_scalar(x_1755)) {
 x_1756 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1756 = x_1755;
}
lean::cnstr_set(x_1756, 0, x_1753);
return x_1756;
}
else
{
obj* x_1757; 
x_1757 = lean::cnstr_get(x_1749, 0);
lean::inc(x_1757);
lean::dec(x_1749);
x_14 = x_1757;
goto lbl_15;
}
}
else
{
obj* x_1760; obj* x_1763; obj* x_1764; obj* x_1766; obj* x_1768; obj* x_1769; obj* x_1771; obj* x_1775; 
x_1760 = lean::cnstr_get(x_1741, 0);
lean::inc(x_1760);
lean::dec(x_1741);
x_1763 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1760);
x_1764 = lean::cnstr_get(x_1763, 0);
lean::inc(x_1764);
x_1766 = lean::cnstr_get(x_1763, 1);
lean::inc(x_1766);
if (lean::is_shared(x_1763)) {
 lean::dec(x_1763);
 x_1768 = lean::box(0);
} else {
 lean::cnstr_release(x_1763, 0);
 lean::cnstr_release(x_1763, 1);
 x_1768 = x_1763;
}
x_1769 = lean::cnstr_get(x_1766, 0);
lean::inc(x_1769);
x_1771 = lean::cnstr_get(x_1766, 1);
lean::inc(x_1771);
lean::dec(x_1766);
lean::inc(x_1);
x_1775 = l_lean_elaborator_to__pexpr___main(x_1771, x_1, x_2);
if (lean::obj_tag(x_1775) == 0)
{
obj* x_1783; obj* x_1785; obj* x_1786; 
lean::dec(x_1769);
lean::dec(x_1768);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1764);
lean::dec(x_1740);
x_1783 = lean::cnstr_get(x_1775, 0);
lean::inc(x_1783);
if (lean::is_shared(x_1775)) {
 lean::dec(x_1775);
 x_1785 = lean::box(0);
} else {
 lean::cnstr_release(x_1775, 0);
 x_1785 = x_1775;
}
if (lean::is_scalar(x_1785)) {
 x_1786 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1786 = x_1785;
}
lean::cnstr_set(x_1786, 0, x_1783);
return x_1786;
}
else
{
obj* x_1787; obj* x_1789; obj* x_1790; obj* x_1792; obj* x_1795; obj* x_1799; 
x_1787 = lean::cnstr_get(x_1775, 0);
lean::inc(x_1787);
if (lean::is_shared(x_1775)) {
 lean::dec(x_1775);
 x_1789 = lean::box(0);
} else {
 lean::cnstr_release(x_1775, 0);
 x_1789 = x_1775;
}
x_1790 = lean::cnstr_get(x_1787, 0);
lean::inc(x_1790);
x_1792 = lean::cnstr_get(x_1787, 1);
lean::inc(x_1792);
lean::dec(x_1787);
x_1795 = lean::cnstr_get(x_1740, 3);
lean::inc(x_1795);
lean::dec(x_1740);
lean::inc(x_1);
x_1799 = l_lean_elaborator_to__pexpr___main(x_1795, x_1, x_1792);
if (lean::obj_tag(x_1799) == 0)
{
obj* x_1807; obj* x_1810; 
lean::dec(x_1769);
lean::dec(x_1768);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1764);
lean::dec(x_1790);
x_1807 = lean::cnstr_get(x_1799, 0);
lean::inc(x_1807);
lean::dec(x_1799);
if (lean::is_scalar(x_1789)) {
 x_1810 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1810 = x_1789;
 lean::cnstr_set_tag(x_1789, 0);
}
lean::cnstr_set(x_1810, 0, x_1807);
return x_1810;
}
else
{
obj* x_1812; obj* x_1815; obj* x_1817; obj* x_1820; uint8 x_1821; obj* x_1823; obj* x_1824; 
lean::dec(x_1789);
x_1812 = lean::cnstr_get(x_1799, 0);
lean::inc(x_1812);
lean::dec(x_1799);
x_1815 = lean::cnstr_get(x_1812, 0);
lean::inc(x_1815);
x_1817 = lean::cnstr_get(x_1812, 1);
lean::inc(x_1817);
lean::dec(x_1812);
x_1820 = l_lean_elaborator_mangle__ident(x_1769);
x_1821 = lean::unbox(x_1764);
lean::dec(x_1764);
x_1823 = lean_expr_mk_lambda(x_1820, x_1821, x_1790, x_1815);
if (lean::is_scalar(x_1768)) {
 x_1824 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1824 = x_1768;
}
lean::cnstr_set(x_1824, 0, x_1823);
lean::cnstr_set(x_1824, 1, x_1817);
x_14 = x_1824;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1826; obj* x_1827; obj* x_1830; obj* x_1831; obj* x_1834; 
lean::dec(x_9);
x_1826 = l_lean_parser_term_app_has__view;
x_1827 = lean::cnstr_get(x_1826, 0);
lean::inc(x_1827);
lean::inc(x_0);
x_1830 = lean::apply_1(x_1827, x_0);
x_1831 = lean::cnstr_get(x_1830, 0);
lean::inc(x_1831);
lean::inc(x_1);
x_1834 = l_lean_elaborator_to__pexpr___main(x_1831, x_1, x_2);
if (lean::obj_tag(x_1834) == 0)
{
obj* x_1839; obj* x_1841; obj* x_1842; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1830);
x_1839 = lean::cnstr_get(x_1834, 0);
lean::inc(x_1839);
if (lean::is_shared(x_1834)) {
 lean::dec(x_1834);
 x_1841 = lean::box(0);
} else {
 lean::cnstr_release(x_1834, 0);
 x_1841 = x_1834;
}
if (lean::is_scalar(x_1841)) {
 x_1842 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1842 = x_1841;
}
lean::cnstr_set(x_1842, 0, x_1839);
return x_1842;
}
else
{
obj* x_1843; obj* x_1845; obj* x_1846; obj* x_1848; obj* x_1850; obj* x_1851; obj* x_1855; 
x_1843 = lean::cnstr_get(x_1834, 0);
lean::inc(x_1843);
if (lean::is_shared(x_1834)) {
 lean::dec(x_1834);
 x_1845 = lean::box(0);
} else {
 lean::cnstr_release(x_1834, 0);
 x_1845 = x_1834;
}
x_1846 = lean::cnstr_get(x_1843, 0);
lean::inc(x_1846);
x_1848 = lean::cnstr_get(x_1843, 1);
lean::inc(x_1848);
if (lean::is_shared(x_1843)) {
 lean::dec(x_1843);
 x_1850 = lean::box(0);
} else {
 lean::cnstr_release(x_1843, 0);
 lean::cnstr_release(x_1843, 1);
 x_1850 = x_1843;
}
x_1851 = lean::cnstr_get(x_1830, 1);
lean::inc(x_1851);
lean::dec(x_1830);
lean::inc(x_1);
x_1855 = l_lean_elaborator_to__pexpr___main(x_1851, x_1, x_1848);
if (lean::obj_tag(x_1855) == 0)
{
obj* x_1861; obj* x_1864; 
lean::dec(x_1850);
lean::dec(x_1846);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1861 = lean::cnstr_get(x_1855, 0);
lean::inc(x_1861);
lean::dec(x_1855);
if (lean::is_scalar(x_1845)) {
 x_1864 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1864 = x_1845;
 lean::cnstr_set_tag(x_1845, 0);
}
lean::cnstr_set(x_1864, 0, x_1861);
return x_1864;
}
else
{
obj* x_1866; obj* x_1869; obj* x_1871; obj* x_1874; obj* x_1875; 
lean::dec(x_1845);
x_1866 = lean::cnstr_get(x_1855, 0);
lean::inc(x_1866);
lean::dec(x_1855);
x_1869 = lean::cnstr_get(x_1866, 0);
lean::inc(x_1869);
x_1871 = lean::cnstr_get(x_1866, 1);
lean::inc(x_1871);
lean::dec(x_1866);
x_1874 = lean_expr_mk_app(x_1846, x_1869);
if (lean::is_scalar(x_1850)) {
 x_1875 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1875 = x_1850;
}
lean::cnstr_set(x_1875, 0, x_1874);
lean::cnstr_set(x_1875, 1, x_1871);
x_14 = x_1875;
goto lbl_15;
}
}
}
}
else
{
obj* x_1877; obj* x_1878; obj* x_1881; obj* x_1882; obj* x_1884; 
lean::dec(x_9);
x_1877 = l_lean_parser_ident__univs_has__view;
x_1878 = lean::cnstr_get(x_1877, 0);
lean::inc(x_1878);
lean::inc(x_0);
x_1881 = lean::apply_1(x_1878, x_0);
x_1882 = lean::cnstr_get(x_1881, 0);
lean::inc(x_1882);
x_1884 = lean::cnstr_get(x_1881, 1);
lean::inc(x_1884);
lean::dec(x_1881);
if (lean::obj_tag(x_1884) == 0)
{
obj* x_1888; obj* x_1889; obj* x_1891; obj* x_1892; obj* x_1895; obj* x_1896; obj* x_1897; obj* x_1899; obj* x_1900; obj* x_1901; uint8 x_1902; 
lean::inc(x_1882);
x_1888 = l_lean_elaborator_mangle__ident(x_1882);
x_1889 = lean::box(0);
lean::inc(x_1889);
x_1891 = lean_expr_mk_const(x_1888, x_1889);
x_1892 = lean::cnstr_get(x_1882, 3);
lean::inc(x_1892);
lean::dec(x_1882);
x_1895 = lean::mk_nat_obj(0u);
x_1896 = l_list_enum__from___main___rarg(x_1895, x_1892);
x_1897 = l_lean_elaborator_to__pexpr___main___closed__47;
lean::inc(x_1897);
x_1899 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(x_1897, x_1896);
x_1900 = lean_expr_mk_mdata(x_1899, x_1891);
x_1901 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1902 = lean_name_dec_eq(x_7, x_1901);
lean::dec(x_7);
if (x_1902 == 0)
{
obj* x_1904; 
x_1904 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1904) == 0)
{
obj* x_1907; obj* x_1908; 
lean::dec(x_1);
lean::dec(x_1889);
x_1907 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1907, 0, x_1900);
lean::cnstr_set(x_1907, 1, x_2);
x_1908 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1908, 0, x_1907);
return x_1908;
}
else
{
obj* x_1909; obj* x_1912; obj* x_1915; obj* x_1918; obj* x_1919; obj* x_1921; obj* x_1923; obj* x_1924; obj* x_1927; obj* x_1929; obj* x_1930; obj* x_1931; obj* x_1932; 
x_1909 = lean::cnstr_get(x_1904, 0);
lean::inc(x_1909);
lean::dec(x_1904);
x_1912 = lean::cnstr_get(x_1, 0);
lean::inc(x_1912);
lean::dec(x_1);
x_1915 = lean::cnstr_get(x_1912, 2);
lean::inc(x_1915);
lean::dec(x_1912);
x_1918 = l_lean_file__map_to__position(x_1915, x_1909);
x_1919 = lean::cnstr_get(x_1918, 1);
lean::inc(x_1919);
x_1921 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1921);
x_1923 = l_lean_kvmap_set__nat(x_1889, x_1921, x_1919);
x_1924 = lean::cnstr_get(x_1918, 0);
lean::inc(x_1924);
lean::dec(x_1918);
x_1927 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1927);
x_1929 = l_lean_kvmap_set__nat(x_1923, x_1927, x_1924);
x_1930 = lean_expr_mk_mdata(x_1929, x_1900);
x_1931 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1931, 0, x_1930);
lean::cnstr_set(x_1931, 1, x_2);
x_1932 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1932, 0, x_1931);
return x_1932;
}
}
else
{
obj* x_1936; obj* x_1937; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1889);
x_1936 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1936, 0, x_1900);
lean::cnstr_set(x_1936, 1, x_2);
x_1937 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1937, 0, x_1936);
return x_1937;
}
}
else
{
obj* x_1938; obj* x_1941; obj* x_1945; 
x_1938 = lean::cnstr_get(x_1884, 0);
lean::inc(x_1938);
lean::dec(x_1884);
x_1941 = lean::cnstr_get(x_1938, 1);
lean::inc(x_1941);
lean::dec(x_1938);
lean::inc(x_1);
x_1945 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_1941, x_1, x_2);
if (lean::obj_tag(x_1945) == 0)
{
obj* x_1950; obj* x_1952; obj* x_1953; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1882);
x_1950 = lean::cnstr_get(x_1945, 0);
lean::inc(x_1950);
if (lean::is_shared(x_1945)) {
 lean::dec(x_1945);
 x_1952 = lean::box(0);
} else {
 lean::cnstr_release(x_1945, 0);
 x_1952 = x_1945;
}
if (lean::is_scalar(x_1952)) {
 x_1953 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1953 = x_1952;
}
lean::cnstr_set(x_1953, 0, x_1950);
return x_1953;
}
else
{
obj* x_1954; obj* x_1957; obj* x_1959; obj* x_1961; obj* x_1963; obj* x_1964; obj* x_1965; obj* x_1968; obj* x_1969; obj* x_1970; obj* x_1972; obj* x_1973; obj* x_1974; 
x_1954 = lean::cnstr_get(x_1945, 0);
lean::inc(x_1954);
lean::dec(x_1945);
x_1957 = lean::cnstr_get(x_1954, 0);
lean::inc(x_1957);
x_1959 = lean::cnstr_get(x_1954, 1);
lean::inc(x_1959);
if (lean::is_shared(x_1954)) {
 lean::dec(x_1954);
 x_1961 = lean::box(0);
} else {
 lean::cnstr_release(x_1954, 0);
 lean::cnstr_release(x_1954, 1);
 x_1961 = x_1954;
}
lean::inc(x_1882);
x_1963 = l_lean_elaborator_mangle__ident(x_1882);
x_1964 = lean_expr_mk_const(x_1963, x_1957);
x_1965 = lean::cnstr_get(x_1882, 3);
lean::inc(x_1965);
lean::dec(x_1882);
x_1968 = lean::mk_nat_obj(0u);
x_1969 = l_list_enum__from___main___rarg(x_1968, x_1965);
x_1970 = l_lean_elaborator_to__pexpr___main___closed__47;
lean::inc(x_1970);
x_1972 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(x_1970, x_1969);
x_1973 = lean_expr_mk_mdata(x_1972, x_1964);
if (lean::is_scalar(x_1961)) {
 x_1974 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1974 = x_1961;
}
lean::cnstr_set(x_1974, 0, x_1973);
lean::cnstr_set(x_1974, 1, x_1959);
x_14 = x_1974;
goto lbl_15;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_1978; obj* x_1980; obj* x_1981; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1978 = lean::cnstr_get(x_12, 0);
lean::inc(x_1978);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_1980 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_1980 = x_12;
}
if (lean::is_scalar(x_1980)) {
 x_1981 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1981 = x_1980;
}
lean::cnstr_set(x_1981, 0, x_1978);
return x_1981;
}
else
{
obj* x_1982; obj* x_1984; obj* x_1985; obj* x_1987; obj* x_1989; obj* x_1990; uint8 x_1991; 
x_1982 = lean::cnstr_get(x_12, 0);
lean::inc(x_1982);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_1984 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_1984 = x_12;
}
x_1985 = lean::cnstr_get(x_1982, 0);
lean::inc(x_1985);
x_1987 = lean::cnstr_get(x_1982, 1);
lean::inc(x_1987);
if (lean::is_shared(x_1982)) {
 lean::dec(x_1982);
 x_1989 = lean::box(0);
} else {
 lean::cnstr_release(x_1982, 0);
 lean::cnstr_release(x_1982, 1);
 x_1989 = x_1982;
}
x_1990 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1991 = lean_name_dec_eq(x_7, x_1990);
lean::dec(x_7);
if (x_1991 == 0)
{
obj* x_1993; 
x_1993 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1993) == 0)
{
obj* x_1995; obj* x_1996; 
lean::dec(x_1);
if (lean::is_scalar(x_1989)) {
 x_1995 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1995 = x_1989;
}
lean::cnstr_set(x_1995, 0, x_1985);
lean::cnstr_set(x_1995, 1, x_1987);
if (lean::is_scalar(x_1984)) {
 x_1996 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1996 = x_1984;
}
lean::cnstr_set(x_1996, 0, x_1995);
return x_1996;
}
else
{
obj* x_1997; obj* x_2000; obj* x_2003; obj* x_2006; obj* x_2007; obj* x_2008; obj* x_2010; obj* x_2012; obj* x_2013; obj* x_2016; obj* x_2018; obj* x_2019; obj* x_2020; obj* x_2021; 
x_1997 = lean::cnstr_get(x_1993, 0);
lean::inc(x_1997);
lean::dec(x_1993);
x_2000 = lean::cnstr_get(x_1, 0);
lean::inc(x_2000);
lean::dec(x_1);
x_2003 = lean::cnstr_get(x_2000, 2);
lean::inc(x_2003);
lean::dec(x_2000);
x_2006 = l_lean_file__map_to__position(x_2003, x_1997);
x_2007 = lean::box(0);
x_2008 = lean::cnstr_get(x_2006, 1);
lean::inc(x_2008);
x_2010 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_2010);
x_2012 = l_lean_kvmap_set__nat(x_2007, x_2010, x_2008);
x_2013 = lean::cnstr_get(x_2006, 0);
lean::inc(x_2013);
lean::dec(x_2006);
x_2016 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_2016);
x_2018 = l_lean_kvmap_set__nat(x_2012, x_2016, x_2013);
x_2019 = lean_expr_mk_mdata(x_2018, x_1985);
if (lean::is_scalar(x_1989)) {
 x_2020 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2020 = x_1989;
}
lean::cnstr_set(x_2020, 0, x_2019);
lean::cnstr_set(x_2020, 1, x_1987);
if (lean::is_scalar(x_1984)) {
 x_2021 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2021 = x_1984;
}
lean::cnstr_set(x_2021, 0, x_2020);
return x_2021;
}
}
else
{
obj* x_2024; obj* x_2025; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_1989)) {
 x_2024 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2024 = x_1989;
}
lean::cnstr_set(x_2024, 0, x_1985);
lean::cnstr_set(x_2024, 1, x_1987);
if (lean::is_scalar(x_1984)) {
 x_2025 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2025 = x_1984;
}
lean::cnstr_set(x_2025, 0, x_2024);
return x_2025;
}
}
}
lbl_15:
{
obj* x_2026; obj* x_2028; obj* x_2030; obj* x_2031; uint8 x_2032; 
x_2026 = lean::cnstr_get(x_14, 0);
lean::inc(x_2026);
x_2028 = lean::cnstr_get(x_14, 1);
lean::inc(x_2028);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_2030 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_2030 = x_14;
}
x_2031 = l_lean_elaborator_to__pexpr___main___closed__2;
x_2032 = lean_name_dec_eq(x_7, x_2031);
lean::dec(x_7);
if (x_2032 == 0)
{
obj* x_2034; 
x_2034 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_2034) == 0)
{
obj* x_2036; obj* x_2037; 
lean::dec(x_1);
if (lean::is_scalar(x_2030)) {
 x_2036 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2036 = x_2030;
}
lean::cnstr_set(x_2036, 0, x_2026);
lean::cnstr_set(x_2036, 1, x_2028);
x_2037 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2037, 0, x_2036);
return x_2037;
}
else
{
obj* x_2038; obj* x_2041; obj* x_2044; obj* x_2047; obj* x_2048; obj* x_2049; obj* x_2051; obj* x_2053; obj* x_2054; obj* x_2057; obj* x_2059; obj* x_2060; obj* x_2061; obj* x_2062; 
x_2038 = lean::cnstr_get(x_2034, 0);
lean::inc(x_2038);
lean::dec(x_2034);
x_2041 = lean::cnstr_get(x_1, 0);
lean::inc(x_2041);
lean::dec(x_1);
x_2044 = lean::cnstr_get(x_2041, 2);
lean::inc(x_2044);
lean::dec(x_2041);
x_2047 = l_lean_file__map_to__position(x_2044, x_2038);
x_2048 = lean::box(0);
x_2049 = lean::cnstr_get(x_2047, 1);
lean::inc(x_2049);
x_2051 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_2051);
x_2053 = l_lean_kvmap_set__nat(x_2048, x_2051, x_2049);
x_2054 = lean::cnstr_get(x_2047, 0);
lean::inc(x_2054);
lean::dec(x_2047);
x_2057 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_2057);
x_2059 = l_lean_kvmap_set__nat(x_2053, x_2057, x_2054);
x_2060 = lean_expr_mk_mdata(x_2059, x_2026);
if (lean::is_scalar(x_2030)) {
 x_2061 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2061 = x_2030;
}
lean::cnstr_set(x_2061, 0, x_2060);
lean::cnstr_set(x_2061, 1, x_2028);
x_2062 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2062, 0, x_2061);
return x_2062;
}
}
else
{
obj* x_2065; obj* x_2066; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_2030)) {
 x_2065 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2065 = x_2030;
}
lean::cnstr_set(x_2065, 0, x_2026);
lean::cnstr_set(x_2065, 1, x_2028);
x_2066 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2066, 0, x_2065);
return x_2066;
}
}
lbl_17:
{
obj* x_2067; obj* x_2069; obj* x_2071; 
x_2067 = lean::cnstr_get(x_16, 0);
lean::inc(x_2067);
x_2069 = lean::cnstr_get(x_16, 1);
lean::inc(x_2069);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_2071 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_2071 = x_16;
}
if (lean::obj_tag(x_2067) == 0)
{
obj* x_2074; obj* x_2078; 
lean::dec(x_9);
lean::dec(x_2071);
x_2074 = l_lean_elaborator_to__pexpr___main___closed__5;
lean::inc(x_1);
lean::inc(x_2074);
lean::inc(x_0);
x_2078 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2074, x_1, x_2069);
if (lean::obj_tag(x_2078) == 0)
{
obj* x_2082; obj* x_2084; obj* x_2085; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_2082 = lean::cnstr_get(x_2078, 0);
lean::inc(x_2082);
if (lean::is_shared(x_2078)) {
 lean::dec(x_2078);
 x_2084 = lean::box(0);
} else {
 lean::cnstr_release(x_2078, 0);
 x_2084 = x_2078;
}
if (lean::is_scalar(x_2084)) {
 x_2085 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2085 = x_2084;
}
lean::cnstr_set(x_2085, 0, x_2082);
return x_2085;
}
else
{
obj* x_2086; 
x_2086 = lean::cnstr_get(x_2078, 0);
lean::inc(x_2086);
lean::dec(x_2078);
x_14 = x_2086;
goto lbl_15;
}
}
else
{
obj* x_2089; obj* x_2091; obj* x_2094; obj* x_2095; obj* x_2096; obj* x_2097; obj* x_2099; obj* x_2100; obj* x_2101; obj* x_2102; obj* x_2103; 
x_2089 = lean::cnstr_get(x_2067, 0);
lean::inc(x_2089);
x_2091 = lean::cnstr_get(x_2067, 1);
lean::inc(x_2091);
lean::dec(x_2067);
x_2094 = lean::box(0);
x_2095 = lean::mk_nat_obj(0u);
x_2096 = l_list_length__aux___main___rarg(x_9, x_2095);
x_2097 = l_lean_elaborator_to__pexpr___main___closed__6;
lean::inc(x_2097);
x_2099 = l_lean_kvmap_set__nat(x_2094, x_2097, x_2096);
x_2100 = l_list_reverse___rarg(x_2091);
x_2101 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_2089, x_2100);
x_2102 = lean_expr_mk_mdata(x_2099, x_2101);
if (lean::is_scalar(x_2071)) {
 x_2103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2103 = x_2071;
}
lean::cnstr_set(x_2103, 0, x_2102);
lean::cnstr_set(x_2103, 1, x_2069);
x_14 = x_2103;
goto lbl_15;
}
}
}
default:
{
obj* x_2104; 
x_2104 = lean::box(0);
x_3 = x_2104;
goto lbl_4;
}
}
lbl_4:
{
obj* x_2107; obj* x_2108; obj* x_2109; obj* x_2110; obj* x_2112; obj* x_2114; 
lean::dec(x_3);
lean::inc(x_0);
x_2107 = l_lean_parser_syntax_to__format___main(x_0);
x_2108 = lean::mk_nat_obj(80u);
x_2109 = l_lean_format_pretty(x_2107, x_2108);
x_2110 = l_lean_elaborator_to__pexpr___main___closed__1;
lean::inc(x_2110);
x_2112 = lean::string_append(x_2110, x_2109);
lean::dec(x_2109);
x_2114 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2112, x_1, x_2);
return x_2114;
}
}
}
obj* l_lean_elaborator_to__pexpr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_to__pexpr___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_elaborator_get__namespace___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = lean::cnstr_get(x_0, 4);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_1, 4);
lean::inc(x_3);
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_0);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
obj* l_lean_elaborator_get__namespace(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_get__namespace___rarg), 1, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(obj* x_0, obj* x_1, obj* x_2) {
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
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_10, x_1, x_2);
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
x_28 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_4, x_1, x_2);
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
x_55 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_36, x_1, x_2);
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
x_62 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_30, x_1, x_2);
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
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; 
lean::inc(x_2);
lean::inc(x_1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 2);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_11);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_2);
x_16 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(x_9, x_1, x_15);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_11, x_17);
lean::dec(x_17);
lean::dec(x_11);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_16);
lean::cnstr_set(x_21, 2, x_18);
return x_21;
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set(x_3, 2, x_1);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(obj* x_0, obj* x_1) {
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
x_12 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(x_0, x_7, x_9);
x_0 = x_12;
x_1 = x_4;
goto _start;
}
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
lean::inc(x_1);
x_3 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(x_1, x_0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(obj* x_0, obj* x_1, obj* x_2) {
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
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_10, x_1, x_2);
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
x_28 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_4, x_1, x_2);
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
x_55 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_36, x_1, x_2);
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
x_62 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_30, x_1, x_2);
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
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; 
lean::inc(x_2);
lean::inc(x_1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 2);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_11);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_2);
x_16 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(x_9, x_1, x_15);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_11, x_17);
lean::dec(x_17);
lean::dec(x_11);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_16);
lean::cnstr_set(x_21, 2, x_18);
return x_21;
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set(x_3, 2, x_1);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(obj* x_0, obj* x_1) {
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
x_12 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__9(x_0, x_7, x_9);
x_0 = x_12;
x_1 = x_4;
goto _start;
}
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1;
lean::inc(x_1);
x_3 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(x_1, x_0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(obj* x_0, obj* x_1, obj* x_2) {
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
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_10, x_1, x_2);
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
x_28 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_4, x_1, x_2);
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
x_55 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_36, x_1, x_2);
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
x_62 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_30, x_1, x_2);
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
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(x_4);
x_8 = lean::box(0);
x_9 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(x_7, x_2, x_8);
return x_9;
}
}
}
obj* l_lean_elaborator_old__elab__command(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
lean::inc(x_3);
x_8 = l_lean_elaborator_get__namespace___rarg(x_3);
switch (lean::obj_tag(x_1)) {
case 10:
{
obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_30; obj* x_32; obj* x_33; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_4, 2);
lean::inc(x_16);
x_18 = l_lean_parser_syntax_get__pos(x_0);
x_19 = lean::mk_nat_obj(0u);
x_20 = l_option_get__or__else___main___rarg(x_18, x_19);
x_21 = l_lean_file__map_to__position(x_16, x_20);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_24);
x_26 = l_lean_kvmap_set__nat(x_11, x_24, x_22);
x_27 = lean::cnstr_get(x_21, 0);
lean::inc(x_27);
lean::dec(x_21);
x_30 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_30);
x_32 = l_lean_kvmap_set__nat(x_26, x_30, x_27);
x_33 = lean_expr_mk_mdata(x_32, x_13);
x_9 = x_33;
goto lbl_10;
}
default:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
}
lbl_10:
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_9);
x_38 = lean::cnstr_get(x_8, 0);
lean::inc(x_38);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_40 = x_8;
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
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_67; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_82; 
x_42 = lean::cnstr_get(x_8, 0);
lean::inc(x_42);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_44 = x_8;
}
x_45 = lean::cnstr_get(x_42, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
if (lean::is_shared(x_42)) {
 lean::dec(x_42);
 x_49 = lean::box(0);
} else {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_49 = x_42;
}
x_50 = lean::cnstr_get(x_4, 0);
lean::inc(x_50);
lean::dec(x_4);
x_53 = lean::cnstr_get(x_3, 8);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_3, 9);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_3, 4);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_57, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_59, 0);
lean::inc(x_61);
lean::dec(x_59);
x_64 = l_list_reverse___rarg(x_61);
x_65 = lean::cnstr_get(x_57, 2);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_65, 0);
lean::inc(x_67);
lean::dec(x_65);
x_70 = l_list_reverse___rarg(x_67);
x_71 = lean::cnstr_get(x_57, 3);
lean::inc(x_71);
x_73 = l_rbtree_to__list___rarg(x_71);
x_74 = lean::cnstr_get(x_57, 6);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_3, 10);
lean::inc(x_76);
x_78 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_78, 0, x_53);
lean::cnstr_set(x_78, 1, x_55);
lean::cnstr_set(x_78, 2, x_64);
lean::cnstr_set(x_78, 3, x_70);
lean::cnstr_set(x_78, 4, x_73);
lean::cnstr_set(x_78, 5, x_74);
lean::cnstr_set(x_78, 6, x_76);
lean::cnstr_set(x_78, 7, x_45);
x_79 = lean_elaborator_elaborate_command(x_50, x_9, x_78);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
if (lean::obj_tag(x_80) == 0)
{
obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_3);
lean::dec(x_57);
x_87 = lean::cnstr_get(x_47, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_47, 1);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_47, 2);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_47, 3);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_47, 4);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_47, 5);
lean::inc(x_97);
x_99 = l_list_append___rarg(x_82, x_97);
x_100 = lean::cnstr_get(x_47, 6);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_47, 7);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_47, 8);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_47, 9);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_47, 10);
lean::inc(x_108);
lean::dec(x_47);
x_111 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_111, 0, x_87);
lean::cnstr_set(x_111, 1, x_89);
lean::cnstr_set(x_111, 2, x_91);
lean::cnstr_set(x_111, 3, x_93);
lean::cnstr_set(x_111, 4, x_95);
lean::cnstr_set(x_111, 5, x_99);
lean::cnstr_set(x_111, 6, x_100);
lean::cnstr_set(x_111, 7, x_102);
lean::cnstr_set(x_111, 8, x_104);
lean::cnstr_set(x_111, 9, x_106);
lean::cnstr_set(x_111, 10, x_108);
x_112 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_49;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_111);
if (lean::is_scalar(x_44)) {
 x_114 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_114 = x_44;
}
lean::cnstr_set(x_114, 0, x_113);
return x_114;
}
else
{
obj* x_116; obj* x_119; obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_134; obj* x_136; obj* x_138; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_147; obj* x_149; obj* x_150; obj* x_152; obj* x_154; obj* x_157; obj* x_159; obj* x_161; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_47);
x_116 = lean::cnstr_get(x_80, 0);
lean::inc(x_116);
lean::dec(x_80);
x_119 = lean::cnstr_get(x_3, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_3, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_3, 2);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_3, 3);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_57, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_116, 2);
lean::inc(x_129);
x_131 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
lean::inc(x_131);
x_133 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(x_131, x_129);
x_134 = lean::cnstr_get(x_116, 3);
lean::inc(x_134);
x_136 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1;
lean::inc(x_136);
x_138 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(x_136, x_134);
x_139 = lean::cnstr_get(x_116, 4);
lean::inc(x_139);
x_141 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(x_139);
x_142 = lean::cnstr_get(x_57, 4);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_57, 5);
lean::inc(x_144);
lean::dec(x_57);
x_147 = lean::cnstr_get(x_116, 5);
lean::inc(x_147);
x_149 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_149, 0, x_127);
lean::cnstr_set(x_149, 1, x_133);
lean::cnstr_set(x_149, 2, x_138);
lean::cnstr_set(x_149, 3, x_141);
lean::cnstr_set(x_149, 4, x_142);
lean::cnstr_set(x_149, 5, x_144);
lean::cnstr_set(x_149, 6, x_147);
x_150 = lean::cnstr_get(x_3, 5);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_3, 6);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_3, 7);
lean::inc(x_154);
lean::dec(x_3);
x_157 = lean::cnstr_get(x_116, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_116, 1);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_116, 6);
lean::inc(x_161);
lean::dec(x_116);
x_164 = l_list_append___rarg(x_82, x_150);
x_165 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_165, 0, x_119);
lean::cnstr_set(x_165, 1, x_121);
lean::cnstr_set(x_165, 2, x_123);
lean::cnstr_set(x_165, 3, x_125);
lean::cnstr_set(x_165, 4, x_149);
lean::cnstr_set(x_165, 5, x_164);
lean::cnstr_set(x_165, 6, x_152);
lean::cnstr_set(x_165, 7, x_154);
lean::cnstr_set(x_165, 8, x_157);
lean::cnstr_set(x_165, 9, x_159);
lean::cnstr_set(x_165, 10, x_161);
x_166 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_49;
}
lean::cnstr_set(x_167, 0, x_166);
lean::cnstr_set(x_167, 1, x_165);
if (lean::is_scalar(x_44)) {
 x_168 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_168 = x_44;
}
lean::cnstr_set(x_168, 0, x_167);
return x_168;
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_names__to__pexpr___spec__1(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_7 = lean::box(0);
x_8 = lean_expr_mk_const(x_2, x_7);
x_9 = l_list_map___main___at_lean_elaborator_names__to__pexpr___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_lean_elaborator_names__to__pexpr(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = l_list_map___main___at_lean_elaborator_names__to__pexpr___spec__1(x_0);
x_2 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_2);
x_4 = l_lean_expr_mk__capp(x_2, x_1);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
lean::inc(x_1);
x_13 = l_lean_elaborator_to__pexpr___main(x_7, x_1, x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
}
x_29 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_36; 
lean::dec(x_11);
lean::dec(x_24);
lean::dec(x_28);
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
lean::dec(x_29);
if (lean::is_scalar(x_23)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_23;
 lean::cnstr_set_tag(x_23, 0);
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
if (lean::is_scalar(x_11)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_11;
}
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_28)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_28;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_23)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_23;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::inc(x_1);
x_18 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_15, x_1, x_2);
if (lean::obj_tag(x_18) == 0)
{
obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_12);
x_23 = lean::cnstr_get(x_18, 0);
lean::inc(x_23);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_25 = x_18;
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; 
x_27 = lean::cnstr_get(x_18, 0);
lean::inc(x_27);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_29 = x_18;
}
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
if (lean::is_shared(x_27)) {
 lean::dec(x_27);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_27, 0);
 lean::cnstr_release(x_27, 1);
 x_34 = x_27;
}
x_35 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(x_9, x_1, x_32);
if (lean::obj_tag(x_35) == 0)
{
obj* x_40; obj* x_43; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_34);
lean::dec(x_30);
x_40 = lean::cnstr_get(x_35, 0);
lean::inc(x_40);
lean::dec(x_35);
if (lean::is_scalar(x_29)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_29;
 lean::cnstr_set_tag(x_29, 0);
}
lean::cnstr_set(x_43, 0, x_40);
return x_43;
}
else
{
obj* x_44; obj* x_47; obj* x_49; obj* x_52; obj* x_55; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_44 = lean::cnstr_get(x_35, 0);
lean::inc(x_44);
lean::dec(x_35);
x_47 = lean::cnstr_get(x_44, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_44, 1);
lean::inc(x_49);
lean::dec(x_44);
x_52 = lean::cnstr_get(x_12, 0);
lean::inc(x_52);
lean::dec(x_12);
x_55 = lean::cnstr_get(x_52, 2);
lean::inc(x_55);
lean::dec(x_52);
x_58 = l_lean_expr_mk__capp(x_55, x_30);
if (lean::is_scalar(x_11)) {
 x_59 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_59 = x_11;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_47);
if (lean::is_scalar(x_34)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_34;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_49);
if (lean::is_scalar(x_29)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_29;
}
lean::cnstr_set(x_61, 0, x_60);
return x_61;
}
}
}
}
}
obj* l_lean_elaborator_attrs__to__pexpr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(x_0, x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_7 = x_6;
}
lean::cnstr_set(x_7, 0, x_4);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
}
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_15 = x_8;
}
x_16 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_16);
x_18 = l_lean_expr_mk__capp(x_16, x_11);
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_13);
if (lean::is_scalar(x_10)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_10;
}
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("noncomputable");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("meta");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; uint8 x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("private");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = 1;
x_5 = l_lean_kvmap_set__bool(x_0, x_3, x_4);
return x_5;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; uint8 x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("protected");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = 1;
x_5 = l_lean_kvmap_set__bool(x_0, x_3, x_4);
return x_5;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("doc_string");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("private");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("protected");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_decl__modifiers__to__pexpr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; uint8 x_10; obj* x_11; uint8 x_13; obj* x_14; obj* x_17; 
x_3 = lean::box(0);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
x_10 = l_option_is__some___main___rarg(x_8);
x_11 = lean::cnstr_get(x_0, 4);
lean::inc(x_11);
x_13 = l_option_is__some___main___rarg(x_11);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
lean::dec(x_0);
if (lean::obj_tag(x_4) == 0)
{
if (lean::obj_tag(x_6) == 0)
{
x_17 = x_3;
goto lbl_18;
}
else
{
obj* x_19; 
x_19 = lean::cnstr_get(x_6, 0);
lean::inc(x_19);
lean::dec(x_6);
if (lean::obj_tag(x_19) == 0)
{
obj* x_23; 
lean::dec(x_19);
x_23 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
lean::inc(x_23);
x_17 = x_23;
goto lbl_18;
}
else
{
obj* x_26; 
lean::dec(x_19);
x_26 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
lean::inc(x_26);
x_17 = x_26;
goto lbl_18;
}
}
}
else
{
obj* x_28; obj* x_31; 
x_28 = lean::cnstr_get(x_4, 0);
lean::inc(x_28);
lean::dec(x_4);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
if (lean::obj_tag(x_31) == 0)
{
if (lean::obj_tag(x_6) == 0)
{
x_17 = x_3;
goto lbl_18;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_6, 0);
lean::inc(x_34);
lean::dec(x_6);
if (lean::obj_tag(x_34) == 0)
{
obj* x_38; 
lean::dec(x_34);
x_38 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
lean::inc(x_38);
x_17 = x_38;
goto lbl_18;
}
else
{
obj* x_41; 
lean::dec(x_34);
x_41 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
lean::inc(x_41);
x_17 = x_41;
goto lbl_18;
}
}
}
else
{
obj* x_43; obj* x_46; obj* x_49; obj* x_52; 
x_43 = lean::cnstr_get(x_31, 0);
lean::inc(x_43);
lean::dec(x_31);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
x_49 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
lean::inc(x_49);
lean::inc(x_3);
x_52 = l_lean_kvmap_set__string(x_3, x_49, x_46);
if (lean::obj_tag(x_6) == 0)
{
x_17 = x_52;
goto lbl_18;
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_6, 0);
lean::inc(x_53);
lean::dec(x_6);
if (lean::obj_tag(x_53) == 0)
{
obj* x_57; uint8 x_58; obj* x_60; 
lean::dec(x_53);
x_57 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
x_58 = 1;
lean::inc(x_57);
x_60 = l_lean_kvmap_set__bool(x_52, x_57, x_58);
x_17 = x_60;
goto lbl_18;
}
else
{
obj* x_62; uint8 x_63; obj* x_65; 
lean::dec(x_53);
x_62 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
x_63 = 1;
lean::inc(x_62);
x_65 = l_lean_kvmap_set__bool(x_52, x_62, x_63);
x_17 = x_65;
goto lbl_18;
}
}
}
}
lbl_18:
{
obj* x_66; obj* x_68; obj* x_69; obj* x_71; 
x_66 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
lean::inc(x_66);
x_68 = l_lean_kvmap_set__bool(x_17, x_66, x_10);
x_69 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
lean::inc(x_69);
x_71 = l_lean_kvmap_set__bool(x_68, x_69, x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_72; 
x_72 = l_lean_elaborator_attrs__to__pexpr(x_3, x_1, x_2);
if (lean::obj_tag(x_72) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_71);
x_74 = lean::cnstr_get(x_72, 0);
lean::inc(x_74);
if (lean::is_shared(x_72)) {
 lean::dec(x_72);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_72, 0);
 x_76 = x_72;
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
obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_78 = lean::cnstr_get(x_72, 0);
lean::inc(x_78);
if (lean::is_shared(x_72)) {
 lean::dec(x_72);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_72, 0);
 x_80 = x_72;
}
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 1);
lean::inc(x_83);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_85 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_release(x_78, 1);
 x_85 = x_78;
}
x_86 = lean_expr_mk_mdata(x_71, x_81);
if (lean::is_scalar(x_85)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_85;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_83);
if (lean::is_scalar(x_80)) {
 x_88 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_88 = x_80;
}
lean::cnstr_set(x_88, 0, x_87);
return x_88;
}
}
else
{
obj* x_90; obj* x_93; obj* x_96; 
lean::dec(x_3);
x_90 = lean::cnstr_get(x_14, 0);
lean::inc(x_90);
lean::dec(x_14);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_lean_elaborator_attrs__to__pexpr(x_93, x_1, x_2);
if (lean::obj_tag(x_96) == 0)
{
obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_71);
x_98 = lean::cnstr_get(x_96, 0);
lean::inc(x_98);
if (lean::is_shared(x_96)) {
 lean::dec(x_96);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_96, 0);
 x_100 = x_96;
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
return x_101;
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_102 = lean::cnstr_get(x_96, 0);
lean::inc(x_102);
if (lean::is_shared(x_96)) {
 lean::dec(x_96);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_96, 0);
 x_104 = x_96;
}
x_105 = lean::cnstr_get(x_102, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_102, 1);
lean::inc(x_107);
if (lean::is_shared(x_102)) {
 lean::dec(x_102);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_102, 0);
 lean::cnstr_release(x_102, 1);
 x_109 = x_102;
}
x_110 = lean_expr_mk_mdata(x_71, x_105);
if (lean::is_scalar(x_109)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_109;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_107);
if (lean::is_scalar(x_104)) {
 x_112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_112 = x_104;
}
lean::cnstr_set(x_112, 0, x_111);
return x_112;
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_ident__univ__params__to__pexpr___spec__1(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = level_mk_param(x_7);
x_9 = l_list_map___main___at_lean_elaborator_ident__univ__params__to__pexpr___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_lean_elaborator_ident__univ__params__to__pexpr(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = l_lean_elaborator_mangle__ident(x_1);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean_expr_mk_const(x_3, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_list_map___main___at_lean_elaborator_ident__univ__params__to__pexpr___spec__1(x_12);
x_16 = lean_expr_mk_const(x_3, x_15);
return x_16;
}
}
}
obj* l_lean_elaborator_locally___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 4);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_locally___rarg___lambda__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_23; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 5);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 6);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_1, 7);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_1, 8);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_1, 9);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_1, 10);
lean::inc(x_20);
lean::dec(x_1);
x_23 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_23, 0, x_2);
lean::cnstr_set(x_23, 1, x_4);
lean::cnstr_set(x_23, 2, x_6);
lean::cnstr_set(x_23, 3, x_8);
lean::cnstr_set(x_23, 4, x_0);
lean::cnstr_set(x_23, 5, x_10);
lean::cnstr_set(x_23, 6, x_12);
lean::cnstr_set(x_23, 7, x_14);
lean::cnstr_set(x_23, 8, x_16);
lean::cnstr_set(x_23, 9, x_18);
lean::cnstr_set(x_23, 10, x_20);
return x_23;
}
}
obj* l_lean_elaborator_locally___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg___lambda__2), 2, 1);
lean::closure_set(x_7, 0, x_1);
x_8 = lean::apply_1(x_4, x_7);
return x_8;
}
}
obj* l_lean_elaborator_locally___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg___lambda__3), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_2, x_4);
return x_5;
}
}
obj* _init_l_lean_elaborator_locally___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* l_lean_elaborator_locally___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
x_16 = l_lean_elaborator_locally___rarg___closed__1;
lean::inc(x_16);
x_18 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_16, x_14);
lean::inc(x_3);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg___lambda__4), 4, 3);
lean::closure_set(x_20, 0, x_1);
lean::closure_set(x_20, 1, x_3);
lean::closure_set(x_20, 2, x_2);
x_21 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_18, x_20);
return x_21;
}
}
obj* l_lean_elaborator_locally(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg), 3, 0);
return x_2;
}
}
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_24; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
x_12 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_7);
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
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
lean::dec(x_15);
lean::inc(x_1);
x_24 = l_lean_elaborator_to__pexpr___main(x_20, x_1, x_2);
if (lean::obj_tag(x_24) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_13);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_17);
lean::dec(x_18);
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_33 = x_24;
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
return x_34;
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_43; 
x_35 = lean::cnstr_get(x_24, 0);
lean::inc(x_35);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_37 = x_24;
}
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
x_43 = l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(x_9, x_1, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_49; obj* x_52; 
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_17);
lean::dec(x_18);
lean::dec(x_38);
x_49 = lean::cnstr_get(x_43, 0);
lean::inc(x_49);
lean::dec(x_43);
if (lean::is_scalar(x_37)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_37;
 lean::cnstr_set_tag(x_37, 0);
}
lean::cnstr_set(x_52, 0, x_49);
return x_52;
}
else
{
obj* x_53; obj* x_56; obj* x_58; obj* x_61; uint8 x_62; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_53 = lean::cnstr_get(x_43, 0);
lean::inc(x_53);
lean::dec(x_43);
x_56 = lean::cnstr_get(x_53, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_53, 1);
lean::inc(x_58);
lean::dec(x_53);
x_61 = l_lean_elaborator_mangle__ident(x_18);
x_62 = lean::unbox(x_13);
lean::dec(x_13);
lean::inc(x_61);
x_65 = lean_expr_local(x_61, x_61, x_38, x_62);
if (lean::is_scalar(x_11)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_11;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_56);
if (lean::is_scalar(x_17)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_17;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_58);
if (lean::is_scalar(x_37)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_37;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
}
}
obj* l_lean_elaborator_simple__binders__to__pexpr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(x_0, x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_7 = x_6;
}
lean::cnstr_set(x_7, 0, x_4);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
}
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_15 = x_8;
}
x_16 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_16);
x_18 = l_lean_expr_mk__capp(x_16, x_11);
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_13);
if (lean::is_scalar(x_10)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_10;
}
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
lean::inc(x_1);
x_13 = l_lean_elaborator_to__pexpr___main(x_7, x_1, x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
}
x_29 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_36; 
lean::dec(x_11);
lean::dec(x_24);
lean::dec(x_28);
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
lean::dec(x_29);
if (lean::is_scalar(x_23)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_23;
 lean::cnstr_set_tag(x_23, 0);
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
if (lean::is_scalar(x_11)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_11;
}
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_28)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_28;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_23)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_23;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_17; 
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
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
lean::inc(x_2);
x_17 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_14, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_17, 0);
lean::inc(x_23);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_25 = x_17;
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_39; 
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_29 = x_17;
}
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
if (lean::is_shared(x_27)) {
 lean::dec(x_27);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_27, 0);
 lean::cnstr_release(x_27, 1);
 x_34 = x_27;
}
x_35 = lean::cnstr_get(x_9, 3);
lean::inc(x_35);
lean::dec(x_9);
lean::inc(x_2);
x_39 = l_lean_elaborator_to__pexpr___main(x_35, x_2, x_32);
if (lean::obj_tag(x_39) == 0)
{
obj* x_46; obj* x_49; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_34);
lean::dec(x_30);
x_46 = lean::cnstr_get(x_39, 0);
lean::inc(x_46);
lean::dec(x_39);
if (lean::is_scalar(x_29)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_29;
 lean::cnstr_set_tag(x_29, 0);
}
lean::cnstr_set(x_49, 0, x_46);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; 
x_50 = lean::cnstr_get(x_39, 0);
lean::inc(x_50);
lean::dec(x_39);
x_53 = lean::cnstr_get(x_0, 0);
lean::inc(x_53);
x_55 = l_lean_elaborator_mangle__ident(x_53);
x_56 = lean::cnstr_get(x_50, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_50, 1);
lean::inc(x_58);
if (lean::is_shared(x_50)) {
 lean::dec(x_50);
 x_60 = lean::box(0);
} else {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 1);
 x_60 = x_50;
}
x_61 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_0, x_11, x_2, x_58);
if (lean::obj_tag(x_61) == 0)
{
obj* x_68; obj* x_71; 
lean::dec(x_13);
lean::dec(x_60);
lean::dec(x_34);
lean::dec(x_30);
lean::dec(x_55);
lean::dec(x_56);
x_68 = lean::cnstr_get(x_61, 0);
lean::inc(x_68);
lean::dec(x_61);
if (lean::is_scalar(x_29)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_29;
 lean::cnstr_set_tag(x_29, 0);
}
lean::cnstr_set(x_71, 0, x_68);
return x_71;
}
else
{
obj* x_72; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_72 = lean::cnstr_get(x_61, 0);
lean::inc(x_72);
lean::dec(x_61);
x_75 = lean::cnstr_get(x_72, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_72, 1);
lean::inc(x_77);
if (lean::is_shared(x_72)) {
 lean::dec(x_72);
 x_79 = lean::box(0);
} else {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_79 = x_72;
}
if (lean::is_scalar(x_34)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_34;
}
lean::cnstr_set(x_80, 0, x_30);
lean::cnstr_set(x_80, 1, x_56);
if (lean::is_scalar(x_60)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_60;
}
lean::cnstr_set(x_81, 0, x_55);
lean::cnstr_set(x_81, 1, x_80);
if (lean::is_scalar(x_13)) {
 x_82 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_82 = x_13;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_75);
if (lean::is_scalar(x_79)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_79;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_77);
if (lean::is_scalar(x_29)) {
 x_84 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_84 = x_29;
}
lean::cnstr_set(x_84, 0, x_83);
return x_84;
}
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(obj* x_0) {
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(x_4);
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
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; 
lean::inc(x_2);
lean::inc(x_1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 2);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_11);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_2);
x_16 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(x_9, x_1, x_15);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_11, x_17);
lean::dec(x_17);
lean::dec(x_11);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_16);
lean::cnstr_set(x_21, 2, x_18);
return x_21;
}
}
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(obj* x_0) {
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(x_4);
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
obj* l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
lean::inc(x_2);
x_8 = level_mk_param(x_2);
x_9 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_0, x_2, x_8);
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(obj* x_0) {
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(x_4);
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
obj* _init_l_lean_elaborator_elab__def__like___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elab_def_like: unexpected input");
return x_0;
}
}
obj* _init_l_lean_elaborator_elab__def__like___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("defs");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
}
}
obj* l_lean_elaborator_elab__def__like(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 3);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 4);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
lean::dec(x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_27; obj* x_29; 
lean::dec(x_12);
lean::dec(x_17);
lean::dec(x_15);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
x_27 = l_lean_elaborator_elab__def__like___closed__1;
lean::inc(x_27);
x_29 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_27, x_4, x_5);
return x_29;
}
else
{
obj* x_30; obj* x_34; 
x_30 = lean::cnstr_get(x_15, 0);
lean::inc(x_30);
lean::dec(x_15);
lean::inc(x_4);
x_34 = l_lean_elaborator_decl__modifiers__to__pexpr(x_1, x_4, x_5);
if (lean::obj_tag(x_34) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_12);
lean::dec(x_17);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_30);
x_43 = lean::cnstr_get(x_34, 0);
lean::inc(x_43);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_45 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 x_45 = x_34;
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
return x_46;
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_47 = lean::cnstr_get(x_34, 0);
lean::inc(x_47);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_49 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 x_49 = x_34;
}
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_54 = x_47;
}
x_55 = lean::box(0);
x_56 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_56, 0, x_3);
x_57 = lean_expr_mk_lit(x_56);
if (lean::obj_tag(x_6) == 0)
{
obj* x_61; obj* x_63; 
x_61 = l_lean_expander_get__opt__type___main(x_17);
lean::inc(x_4);
x_63 = l_lean_elaborator_to__pexpr___main(x_61, x_4, x_52);
if (lean::obj_tag(x_6) == 0)
{
if (lean::obj_tag(x_63) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_54);
lean::dec(x_55);
x_74 = lean::cnstr_get(x_63, 0);
lean::inc(x_74);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_76 = x_63;
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
obj* x_78; 
x_78 = lean::cnstr_get(x_63, 0);
lean::inc(x_78);
lean::dec(x_63);
x_58 = x_55;
x_59 = x_78;
goto lbl_60;
}
}
else
{
obj* x_81; 
x_81 = lean::cnstr_get(x_6, 0);
lean::inc(x_81);
lean::dec(x_6);
if (lean::obj_tag(x_63) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_81);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_54);
lean::dec(x_55);
x_95 = lean::cnstr_get(x_63, 0);
lean::inc(x_95);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_97 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_97 = x_63;
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
obj* x_99; obj* x_102; obj* x_105; 
x_99 = lean::cnstr_get(x_63, 0);
lean::inc(x_99);
lean::dec(x_63);
x_102 = lean::cnstr_get(x_81, 1);
lean::inc(x_102);
lean::dec(x_81);
x_105 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(x_102);
x_58 = x_105;
x_59 = x_99;
goto lbl_60;
}
}
}
else
{
obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_118; obj* x_120; obj* x_122; obj* x_126; obj* x_127; obj* x_128; obj* x_130; obj* x_132; obj* x_134; obj* x_136; obj* x_139; obj* x_140; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_153; obj* x_154; obj* x_156; 
x_106 = lean::cnstr_get(x_6, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_52, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_52, 1);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_52, 2);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_52, 3);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_52, 4);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_116, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_116, 1);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_106, 1);
lean::inc(x_122);
lean::dec(x_106);
lean::inc(x_122);
x_126 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(x_122);
x_127 = l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(x_120, x_126);
x_128 = lean::cnstr_get(x_116, 2);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_116, 3);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_116, 4);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_116, 5);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_116, 6);
lean::inc(x_136);
lean::dec(x_116);
x_139 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_139, 0, x_118);
lean::cnstr_set(x_139, 1, x_127);
lean::cnstr_set(x_139, 2, x_128);
lean::cnstr_set(x_139, 3, x_130);
lean::cnstr_set(x_139, 4, x_132);
lean::cnstr_set(x_139, 5, x_134);
lean::cnstr_set(x_139, 6, x_136);
x_140 = lean::cnstr_get(x_52, 5);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_52, 6);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_52, 7);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_52, 8);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_52, 9);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_52, 10);
lean::inc(x_150);
lean::dec(x_52);
x_153 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_153, 0, x_108);
lean::cnstr_set(x_153, 1, x_110);
lean::cnstr_set(x_153, 2, x_112);
lean::cnstr_set(x_153, 3, x_114);
lean::cnstr_set(x_153, 4, x_139);
lean::cnstr_set(x_153, 5, x_140);
lean::cnstr_set(x_153, 6, x_142);
lean::cnstr_set(x_153, 7, x_144);
lean::cnstr_set(x_153, 8, x_146);
lean::cnstr_set(x_153, 9, x_148);
lean::cnstr_set(x_153, 10, x_150);
x_154 = l_lean_expander_get__opt__type___main(x_17);
lean::inc(x_4);
x_156 = l_lean_elaborator_to__pexpr___main(x_154, x_4, x_153);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_122);
if (lean::obj_tag(x_156) == 0)
{
obj* x_168; obj* x_170; obj* x_171; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_54);
lean::dec(x_55);
x_168 = lean::cnstr_get(x_156, 0);
lean::inc(x_168);
if (lean::is_shared(x_156)) {
 lean::dec(x_156);
 x_170 = lean::box(0);
} else {
 lean::cnstr_release(x_156, 0);
 x_170 = x_156;
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
obj* x_172; 
x_172 = lean::cnstr_get(x_156, 0);
lean::inc(x_172);
lean::dec(x_156);
x_58 = x_55;
x_59 = x_172;
goto lbl_60;
}
}
else
{
lean::dec(x_6);
if (lean::obj_tag(x_156) == 0)
{
obj* x_187; obj* x_189; obj* x_190; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_54);
lean::dec(x_55);
lean::dec(x_122);
x_187 = lean::cnstr_get(x_156, 0);
lean::inc(x_187);
if (lean::is_shared(x_156)) {
 lean::dec(x_156);
 x_189 = lean::box(0);
} else {
 lean::cnstr_release(x_156, 0);
 x_189 = x_156;
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_187);
return x_190;
}
else
{
obj* x_191; obj* x_194; 
x_191 = lean::cnstr_get(x_156, 0);
lean::inc(x_191);
lean::dec(x_156);
x_194 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(x_122);
x_58 = x_194;
x_59 = x_191;
goto lbl_60;
}
}
}
lbl_60:
{
obj* x_195; obj* x_197; obj* x_200; obj* x_201; obj* x_203; uint8 x_204; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_213; 
x_195 = lean::cnstr_get(x_59, 0);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_59, 1);
lean::inc(x_197);
lean::dec(x_59);
x_200 = l_lean_elaborator_names__to__pexpr(x_58);
x_201 = lean::cnstr_get(x_8, 0);
lean::inc(x_201);
x_203 = l_lean_elaborator_mangle__ident(x_201);
x_204 = 4;
lean::inc(x_195);
lean::inc(x_203);
x_207 = lean_expr_local(x_203, x_203, x_195, x_204);
lean::inc(x_55);
x_209 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_209, 0, x_207);
lean::cnstr_set(x_209, 1, x_55);
x_210 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_210);
x_212 = l_lean_expr_mk__capp(x_210, x_209);
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_218; obj* x_221; obj* x_225; 
lean::dec(x_195);
lean::dec(x_8);
lean::dec(x_54);
x_218 = lean::cnstr_get(x_12, 0);
lean::inc(x_218);
lean::dec(x_12);
x_221 = lean::cnstr_get(x_218, 1);
lean::inc(x_221);
lean::dec(x_218);
lean::inc(x_4);
x_225 = l_lean_elaborator_to__pexpr___main(x_221, x_4, x_197);
if (lean::obj_tag(x_225) == 0)
{
obj* x_235; obj* x_237; obj* x_238; 
lean::dec(x_212);
lean::dec(x_200);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_55);
x_235 = lean::cnstr_get(x_225, 0);
lean::inc(x_235);
if (lean::is_shared(x_225)) {
 lean::dec(x_225);
 x_237 = lean::box(0);
} else {
 lean::cnstr_release(x_225, 0);
 x_237 = x_225;
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
obj* x_239; 
x_239 = lean::cnstr_get(x_225, 0);
lean::inc(x_239);
lean::dec(x_225);
x_213 = x_239;
goto lbl_214;
}
}
case 1:
{
obj* x_245; obj* x_246; 
lean::dec(x_12);
lean::dec(x_8);
lean::inc(x_55);
x_245 = l_lean_elaborator_mk__eqns(x_195, x_55);
if (lean::is_scalar(x_54)) {
 x_246 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_246 = x_54;
}
lean::cnstr_set(x_246, 0, x_245);
lean::cnstr_set(x_246, 1, x_197);
x_213 = x_246;
goto lbl_214;
}
default:
{
obj* x_247; obj* x_251; 
x_247 = lean::cnstr_get(x_12, 0);
lean::inc(x_247);
lean::dec(x_12);
lean::inc(x_4);
x_251 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_8, x_247, x_4, x_197);
if (lean::obj_tag(x_251) == 0)
{
obj* x_263; obj* x_265; obj* x_266; 
lean::dec(x_195);
lean::dec(x_212);
lean::dec(x_200);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_54);
lean::dec(x_55);
x_263 = lean::cnstr_get(x_251, 0);
lean::inc(x_263);
if (lean::is_shared(x_251)) {
 lean::dec(x_251);
 x_265 = lean::box(0);
} else {
 lean::cnstr_release(x_251, 0);
 x_265 = x_251;
}
if (lean::is_scalar(x_265)) {
 x_266 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_266 = x_265;
}
lean::cnstr_set(x_266, 0, x_263);
return x_266;
}
else
{
obj* x_267; obj* x_270; obj* x_272; obj* x_275; obj* x_276; 
x_267 = lean::cnstr_get(x_251, 0);
lean::inc(x_267);
lean::dec(x_251);
x_270 = lean::cnstr_get(x_267, 0);
lean::inc(x_270);
x_272 = lean::cnstr_get(x_267, 1);
lean::inc(x_272);
lean::dec(x_267);
x_275 = l_lean_elaborator_mk__eqns(x_195, x_270);
if (lean::is_scalar(x_54)) {
 x_276 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_276 = x_54;
}
lean::cnstr_set(x_276, 0, x_275);
lean::cnstr_set(x_276, 1, x_272);
x_213 = x_276;
goto lbl_214;
}
}
}
lbl_214:
{
obj* x_277; obj* x_279; obj* x_283; 
x_277 = lean::cnstr_get(x_213, 0);
lean::inc(x_277);
x_279 = lean::cnstr_get(x_213, 1);
lean::inc(x_279);
lean::dec(x_213);
lean::inc(x_4);
x_283 = l_lean_elaborator_simple__binders__to__pexpr(x_30, x_4, x_279);
if (lean::obj_tag(x_283) == 0)
{
obj* x_292; obj* x_295; 
lean::dec(x_212);
lean::dec(x_200);
lean::dec(x_277);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_50);
lean::dec(x_57);
lean::dec(x_55);
x_292 = lean::cnstr_get(x_283, 0);
lean::inc(x_292);
lean::dec(x_283);
if (lean::is_scalar(x_49)) {
 x_295 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_295 = x_49;
 lean::cnstr_set_tag(x_49, 0);
}
lean::cnstr_set(x_295, 0, x_292);
return x_295;
}
else
{
obj* x_297; obj* x_300; obj* x_302; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_312; obj* x_313; obj* x_315; obj* x_316; 
lean::dec(x_49);
x_297 = lean::cnstr_get(x_283, 0);
lean::inc(x_297);
lean::dec(x_283);
x_300 = lean::cnstr_get(x_297, 0);
lean::inc(x_300);
x_302 = lean::cnstr_get(x_297, 1);
lean::inc(x_302);
lean::dec(x_297);
x_305 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_305, 0, x_277);
lean::cnstr_set(x_305, 1, x_55);
x_306 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_306, 0, x_300);
lean::cnstr_set(x_306, 1, x_305);
x_307 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_307, 0, x_212);
lean::cnstr_set(x_307, 1, x_306);
x_308 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_308, 0, x_200);
lean::cnstr_set(x_308, 1, x_307);
x_309 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_309, 0, x_57);
lean::cnstr_set(x_309, 1, x_308);
x_310 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_310, 0, x_50);
lean::cnstr_set(x_310, 1, x_309);
lean::inc(x_210);
x_312 = l_lean_expr_mk__capp(x_210, x_310);
x_313 = l_lean_elaborator_elab__def__like___closed__2;
lean::inc(x_313);
x_315 = lean_expr_mk_mdata(x_313, x_312);
x_316 = l_lean_elaborator_old__elab__command(x_0, x_315, x_4, x_302);
return x_316;
}
}
}
}
}
}
}
obj* _init_l_lean_elaborator_infer__mod__to__pexpr___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_infer__mod__to__pexpr___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_infer__mod__to__pexpr___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(2u);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
obj* l_lean_elaborator_infer__mod__to__pexpr(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_lean_elaborator_infer__mod__to__pexpr___closed__1;
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
lean::dec(x_3);
x_7 = l_lean_elaborator_infer__mod__to__pexpr___closed__2;
lean::inc(x_7);
return x_7;
}
else
{
obj* x_10; 
lean::dec(x_3);
x_10 = l_lean_elaborator_infer__mod__to__pexpr___closed__3;
lean::inc(x_10);
return x_10;
}
}
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("declaration.elaborate: unexpected input");
return x_0;
}
}
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
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
x_16 = lean::cnstr_get(x_9, 3);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
if (lean::obj_tag(x_18) == 0)
{
obj* x_26; obj* x_30; 
lean::dec(x_9);
lean::dec(x_18);
lean::dec(x_20);
x_26 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_26);
lean::inc(x_0);
x_30 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_26, x_2, x_3);
if (lean::obj_tag(x_30) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_35 = lean::cnstr_get(x_30, 0);
lean::inc(x_35);
if (lean::is_shared(x_30)) {
 lean::dec(x_30);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_30, 0);
 x_37 = x_30;
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
return x_38;
}
else
{
obj* x_39; 
x_39 = lean::cnstr_get(x_30, 0);
lean::inc(x_39);
lean::dec(x_30);
x_14 = x_39;
goto lbl_15;
}
}
else
{
obj* x_42; 
x_42 = lean::cnstr_get(x_18, 0);
lean::inc(x_42);
lean::dec(x_18);
if (lean::obj_tag(x_42) == 0)
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_46; obj* x_50; 
lean::dec(x_9);
x_46 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_46);
lean::inc(x_0);
x_50 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_46, x_2, x_3);
if (lean::obj_tag(x_50) == 0)
{
obj* x_55; obj* x_57; obj* x_58; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_55 = lean::cnstr_get(x_50, 0);
lean::inc(x_55);
if (lean::is_shared(x_50)) {
 lean::dec(x_50);
 x_57 = lean::box(0);
} else {
 lean::cnstr_release(x_50, 0);
 x_57 = x_50;
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
obj* x_59; 
x_59 = lean::cnstr_get(x_50, 0);
lean::inc(x_59);
lean::dec(x_50);
x_14 = x_59;
goto lbl_15;
}
}
else
{
obj* x_62; obj* x_65; obj* x_69; 
x_62 = lean::cnstr_get(x_20, 0);
lean::inc(x_62);
lean::dec(x_20);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
lean::inc(x_2);
x_69 = l_lean_elaborator_to__pexpr___main(x_65, x_2, x_3);
if (lean::obj_tag(x_69) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_75 = lean::cnstr_get(x_69, 0);
lean::inc(x_75);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 x_77 = x_69;
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
obj* x_79; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_90; uint8 x_91; obj* x_93; obj* x_94; 
x_79 = lean::cnstr_get(x_69, 0);
lean::inc(x_79);
lean::dec(x_69);
x_82 = lean::cnstr_get(x_79, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_79, 1);
lean::inc(x_84);
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 lean::cnstr_release(x_79, 1);
 x_86 = x_79;
}
x_87 = lean::cnstr_get(x_9, 1);
lean::inc(x_87);
lean::dec(x_9);
x_90 = l_lean_elaborator_mangle__ident(x_87);
x_91 = 0;
lean::inc(x_90);
x_93 = lean_expr_local(x_90, x_90, x_82, x_91);
if (lean::is_scalar(x_86)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_86;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_84);
x_14 = x_94;
goto lbl_15;
}
}
}
else
{
obj* x_98; obj* x_102; 
lean::dec(x_9);
lean::dec(x_20);
lean::dec(x_42);
x_98 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_98);
lean::inc(x_0);
x_102 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_98, x_2, x_3);
if (lean::obj_tag(x_102) == 0)
{
obj* x_107; obj* x_109; obj* x_110; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_107 = lean::cnstr_get(x_102, 0);
lean::inc(x_107);
if (lean::is_shared(x_102)) {
 lean::dec(x_102);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_102, 0);
 x_109 = x_102;
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
return x_110;
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_102, 0);
lean::inc(x_111);
lean::dec(x_102);
x_14 = x_111;
goto lbl_15;
}
}
}
lbl_15:
{
obj* x_114; obj* x_116; obj* x_118; obj* x_119; 
x_114 = lean::cnstr_get(x_14, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_14, 1);
lean::inc(x_116);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_118 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_118 = x_14;
}
x_119 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_11, x_2, x_116);
if (lean::obj_tag(x_119) == 0)
{
obj* x_123; obj* x_125; obj* x_126; 
lean::dec(x_13);
lean::dec(x_114);
lean::dec(x_118);
x_123 = lean::cnstr_get(x_119, 0);
lean::inc(x_123);
if (lean::is_shared(x_119)) {
 lean::dec(x_119);
 x_125 = lean::box(0);
} else {
 lean::cnstr_release(x_119, 0);
 x_125 = x_119;
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_123);
return x_126;
}
else
{
obj* x_127; obj* x_129; obj* x_130; obj* x_132; obj* x_135; obj* x_136; obj* x_137; 
x_127 = lean::cnstr_get(x_119, 0);
lean::inc(x_127);
if (lean::is_shared(x_119)) {
 lean::dec(x_119);
 x_129 = lean::box(0);
} else {
 lean::cnstr_release(x_119, 0);
 x_129 = x_119;
}
x_130 = lean::cnstr_get(x_127, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_127, 1);
lean::inc(x_132);
lean::dec(x_127);
if (lean::is_scalar(x_13)) {
 x_135 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_135 = x_13;
}
lean::cnstr_set(x_135, 0, x_114);
lean::cnstr_set(x_135, 1, x_130);
if (lean::is_scalar(x_118)) {
 x_136 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_136 = x_118;
}
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_132);
if (lean::is_scalar(x_129)) {
 x_137 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_137 = x_129;
}
lean::cnstr_set(x_137, 0, x_136);
return x_137;
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
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
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_lean_elaborator_infer__mod__to__pexpr(x_7);
x_11 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(x_4);
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
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(obj* x_0) {
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_4);
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
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(obj* x_0) {
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(x_4);
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
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
lean::inc(x_2);
x_8 = level_mk_param(x_2);
x_9 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_0, x_2, x_8);
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(obj* x_0) {
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(x_4);
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
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_16; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
lean::inc(x_1);
x_16 = l_lean_elaborator_to__pexpr___main(x_12, x_1, x_2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_22 = x_16;
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; 
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_26 = x_16;
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 x_31 = x_24;
}
x_32 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_9, x_1, x_29);
if (lean::obj_tag(x_32) == 0)
{
obj* x_36; obj* x_39; 
lean::dec(x_11);
lean::dec(x_27);
lean::dec(x_31);
x_36 = lean::cnstr_get(x_32, 0);
lean::inc(x_36);
lean::dec(x_32);
if (lean::is_scalar(x_26)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_26;
 lean::cnstr_set_tag(x_26, 0);
}
lean::cnstr_set(x_39, 0, x_36);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_32, 0);
lean::inc(x_40);
lean::dec(x_32);
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
if (lean::is_scalar(x_11)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_11;
}
lean::cnstr_set(x_48, 0, x_27);
lean::cnstr_set(x_48, 1, x_43);
if (lean::is_scalar(x_31)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_31;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
if (lean::is_scalar(x_26)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_26;
}
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(obj* x_0) {
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(x_4);
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
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
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
switch (lean::obj_tag(x_9)) {
case 0:
{
obj* x_16; obj* x_19; 
x_16 = lean::cnstr_get(x_9, 0);
lean::inc(x_16);
lean::dec(x_9);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::obj_tag(x_19) == 0)
{
obj* x_23; obj* x_27; 
lean::dec(x_19);
x_23 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_23);
lean::inc(x_0);
x_27 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_23, x_2, x_3);
if (lean::obj_tag(x_27) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_27, 0);
lean::inc(x_32);
if (lean::is_shared(x_27)) {
 lean::dec(x_27);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_27, 0);
 x_34 = x_27;
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
x_36 = lean::cnstr_get(x_27, 0);
lean::inc(x_36);
lean::dec(x_27);
x_14 = x_36;
goto lbl_15;
}
}
else
{
obj* x_39; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; 
x_39 = lean::cnstr_get(x_19, 0);
lean::inc(x_39);
lean::dec(x_19);
x_42 = 0;
x_43 = lean::box(x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_39);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_3);
x_14 = x_45;
goto lbl_15;
}
}
case 1:
{
obj* x_46; obj* x_49; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; 
x_46 = lean::cnstr_get(x_9, 0);
lean::inc(x_46);
lean::dec(x_9);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_52 = 1;
x_53 = lean::box(x_52);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_49);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_3);
x_14 = x_55;
goto lbl_15;
}
case 2:
{
obj* x_56; obj* x_59; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; 
x_56 = lean::cnstr_get(x_9, 0);
lean::inc(x_56);
lean::dec(x_9);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
x_62 = 2;
x_63 = lean::box(x_62);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_59);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_3);
x_14 = x_65;
goto lbl_15;
}
default:
{
obj* x_66; obj* x_69; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; 
x_66 = lean::cnstr_get(x_9, 0);
lean::inc(x_66);
lean::dec(x_9);
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
lean::dec(x_66);
x_72 = 3;
x_73 = lean::box(x_72);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_69);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_3);
x_14 = x_75;
goto lbl_15;
}
}
lbl_15:
{
obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_86; obj* x_88; obj* x_91; obj* x_93; 
x_76 = lean::cnstr_get(x_14, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_14, 1);
lean::inc(x_78);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_80 = x_14;
}
x_81 = lean::cnstr_get(x_76, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_76, 1);
lean::inc(x_83);
lean::dec(x_76);
x_86 = lean::cnstr_get(x_83, 2);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_86, 1);
lean::inc(x_88);
lean::dec(x_86);
x_91 = l_lean_expander_get__opt__type___main(x_88);
lean::inc(x_2);
x_93 = l_lean_elaborator_to__pexpr___main(x_91, x_2, x_78);
if (lean::obj_tag(x_93) == 0)
{
obj* x_101; obj* x_103; obj* x_104; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_81);
lean::dec(x_80);
lean::dec(x_83);
x_101 = lean::cnstr_get(x_93, 0);
lean::inc(x_101);
if (lean::is_shared(x_93)) {
 lean::dec(x_93);
 x_103 = lean::box(0);
} else {
 lean::cnstr_release(x_93, 0);
 x_103 = x_93;
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_101);
return x_104;
}
else
{
obj* x_105; obj* x_107; obj* x_108; obj* x_110; obj* x_113; 
x_105 = lean::cnstr_get(x_93, 0);
lean::inc(x_105);
if (lean::is_shared(x_93)) {
 lean::dec(x_93);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_93, 0);
 x_107 = x_93;
}
x_108 = lean::cnstr_get(x_105, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_105, 1);
lean::inc(x_110);
lean::dec(x_105);
x_113 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_11, x_2, x_110);
if (lean::obj_tag(x_113) == 0)
{
obj* x_119; obj* x_122; 
lean::dec(x_13);
lean::dec(x_81);
lean::dec(x_80);
lean::dec(x_83);
lean::dec(x_108);
x_119 = lean::cnstr_get(x_113, 0);
lean::inc(x_119);
lean::dec(x_113);
if (lean::is_scalar(x_107)) {
 x_122 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_122 = x_107;
 lean::cnstr_set_tag(x_107, 0);
}
lean::cnstr_set(x_122, 0, x_119);
return x_122;
}
else
{
obj* x_123; obj* x_126; obj* x_128; obj* x_131; obj* x_132; uint8 x_133; obj* x_138; obj* x_139; obj* x_141; obj* x_142; obj* x_143; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
x_123 = lean::cnstr_get(x_113, 0);
lean::inc(x_123);
lean::dec(x_113);
x_126 = lean::cnstr_get(x_123, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_123, 1);
lean::inc(x_128);
lean::dec(x_123);
x_131 = l_lean_elaborator_mk__eqns___closed__1;
x_132 = l_lean_elaborator_dummy;
x_133 = lean::unbox(x_81);
lean::dec(x_81);
lean::inc(x_132);
lean::inc(x_131);
lean::inc(x_131);
x_138 = lean_expr_local(x_131, x_131, x_132, x_133);
x_139 = lean::cnstr_get(x_83, 0);
lean::inc(x_139);
x_141 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(x_139);
x_142 = l_lean_elaborator_names__to__pexpr(x_141);
x_143 = lean::cnstr_get(x_83, 1);
lean::inc(x_143);
lean::dec(x_83);
x_146 = l_lean_elaborator_infer__mod__to__pexpr(x_143);
x_147 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_148 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_148 = x_13;
}
lean::cnstr_set(x_148, 0, x_108);
lean::cnstr_set(x_148, 1, x_147);
x_149 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_149, 0, x_146);
lean::cnstr_set(x_149, 1, x_148);
x_150 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_150, 0, x_142);
lean::cnstr_set(x_150, 1, x_149);
x_151 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_151, 0, x_138);
lean::cnstr_set(x_151, 1, x_150);
lean::inc(x_131);
x_153 = l_lean_expr_mk__capp(x_131, x_151);
x_154 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_126);
if (lean::is_scalar(x_80)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_80;
}
lean::cnstr_set(x_155, 0, x_154);
lean::cnstr_set(x_155, 1, x_128);
if (lean::is_scalar(x_107)) {
 x_156 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_156 = x_107;
}
lean::cnstr_set(x_156, 0, x_155);
return x_156;
}
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(obj* x_0) {
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(x_4);
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
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(obj* x_0) {
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(x_4);
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
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
lean::inc(x_2);
x_8 = level_mk_param(x_2);
x_9 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_0, x_2, x_8);
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(obj* x_0) {
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
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(x_4);
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
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string(".");
lean::inc(x_0);
x_3 = l_lean_name_to__string__with__sep___main(x_1, x_0);
x_4 = l_lean_parser_substring_of__string(x_3);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set(x_9, 2, x_0);
lean::cnstr_set(x_9, 3, x_0);
lean::cnstr_set(x_9, 4, x_0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_0);
return x_10;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("def");
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
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("constant");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("inductives");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_lean_elaborator_infer__mod__to__pexpr(x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("structure");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("mk");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_2, 4);
lean::inc(x_3);
x_7 = l_lean_parser_command_declaration_has__view;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::inc(x_0);
x_11 = lean::apply_1(x_8, x_0);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_14; obj* x_17; obj* x_19; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_11, 0);
lean::inc(x_19);
lean::dec(x_11);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_23; obj* x_24; 
lean::dec(x_17);
x_23 = lean::mk_nat_obj(1u);
x_24 = l_lean_elaborator_elab__def__like(x_0, x_19, x_14, x_23, x_1, x_2);
x_5 = x_24;
goto lbl_6;
}
case 1:
{
obj* x_26; obj* x_27; 
lean::dec(x_17);
x_26 = lean::mk_nat_obj(5u);
x_27 = l_lean_elaborator_elab__def__like(x_0, x_19, x_14, x_26, x_1, x_2);
x_5 = x_27;
goto lbl_6;
}
default:
{
obj* x_29; obj* x_30; 
lean::dec(x_17);
x_29 = lean::mk_nat_obj(0u);
x_30 = l_lean_elaborator_elab__def__like(x_0, x_19, x_14, x_29, x_1, x_2);
x_5 = x_30;
goto lbl_6;
}
}
}
case 1:
{
obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
x_31 = lean::cnstr_get(x_12, 0);
lean::inc(x_31);
lean::dec(x_12);
x_34 = lean::cnstr_get(x_11, 0);
lean::inc(x_34);
lean::dec(x_11);
x_37 = lean::box(0);
x_38 = lean::cnstr_get(x_31, 1);
lean::inc(x_38);
x_40 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
lean::inc(x_40);
x_42 = l_option_get__or__else___main___rarg(x_38, x_40);
x_43 = lean::cnstr_get(x_31, 2);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_43, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_43, 1);
lean::inc(x_47);
lean::dec(x_43);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_47);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_45);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::cnstr_get(x_31, 3);
lean::inc(x_52);
lean::dec(x_31);
x_55 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_37);
lean::cnstr_set(x_57, 2, x_42);
lean::cnstr_set(x_57, 3, x_51);
lean::cnstr_set(x_57, 4, x_52);
x_58 = lean::mk_nat_obj(3u);
x_59 = l_lean_elaborator_elab__def__like(x_0, x_34, x_57, x_58, x_1, x_2);
x_5 = x_59;
goto lbl_6;
}
case 2:
{
obj* x_60; obj* x_63; obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_74; obj* x_75; obj* x_76; obj* x_79; obj* x_80; obj* x_83; obj* x_84; obj* x_85; 
x_60 = lean::cnstr_get(x_12, 0);
lean::inc(x_60);
lean::dec(x_12);
x_63 = lean::cnstr_get(x_11, 0);
lean::inc(x_63);
lean::dec(x_11);
x_66 = lean::box(0);
x_67 = lean::cnstr_get(x_60, 1);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_67, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_67, 1);
lean::inc(x_71);
lean::dec(x_67);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_71);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_69);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::cnstr_get(x_60, 2);
lean::inc(x_76);
lean::dec(x_60);
x_79 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
x_80 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
lean::inc(x_80);
lean::inc(x_79);
x_83 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_83, 0, x_79);
lean::cnstr_set(x_83, 1, x_66);
lean::cnstr_set(x_83, 2, x_80);
lean::cnstr_set(x_83, 3, x_75);
lean::cnstr_set(x_83, 4, x_76);
x_84 = lean::mk_nat_obj(2u);
x_85 = l_lean_elaborator_elab__def__like(x_0, x_63, x_83, x_84, x_1, x_2);
x_5 = x_85;
goto lbl_6;
}
case 3:
{
obj* x_86; obj* x_89; obj* x_91; obj* x_94; obj* x_96; 
x_86 = lean::cnstr_get(x_12, 0);
lean::inc(x_86);
lean::dec(x_12);
x_89 = lean::cnstr_get(x_86, 1);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_86, 2);
lean::inc(x_91);
lean::dec(x_86);
x_94 = lean::cnstr_get(x_91, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_91, 1);
lean::inc(x_96);
lean::dec(x_91);
if (lean::obj_tag(x_94) == 0)
{
obj* x_103; obj* x_105; 
lean::dec(x_11);
lean::dec(x_89);
lean::dec(x_94);
lean::dec(x_96);
x_103 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_103);
x_105 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_103, x_1, x_2);
x_5 = x_105;
goto lbl_6;
}
else
{
obj* x_106; 
x_106 = lean::cnstr_get(x_94, 0);
lean::inc(x_106);
lean::dec(x_94);
if (lean::obj_tag(x_106) == 0)
{
obj* x_109; obj* x_113; 
x_109 = lean::cnstr_get(x_11, 0);
lean::inc(x_109);
lean::dec(x_11);
lean::inc(x_1);
x_113 = l_lean_elaborator_decl__modifiers__to__pexpr(x_109, x_1, x_2);
if (lean::obj_tag(x_113) == 0)
{
obj* x_118; obj* x_120; obj* x_121; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_89);
lean::dec(x_96);
x_118 = lean::cnstr_get(x_113, 0);
lean::inc(x_118);
if (lean::is_shared(x_113)) {
 lean::dec(x_113);
 x_120 = lean::box(0);
} else {
 lean::cnstr_release(x_113, 0);
 x_120 = x_113;
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_118);
x_5 = x_121;
goto lbl_6;
}
else
{
obj* x_122; obj* x_124; obj* x_125; obj* x_127; obj* x_130; obj* x_134; 
x_122 = lean::cnstr_get(x_113, 0);
lean::inc(x_122);
if (lean::is_shared(x_113)) {
 lean::dec(x_113);
 x_124 = lean::box(0);
} else {
 lean::cnstr_release(x_113, 0);
 x_124 = x_113;
}
x_125 = lean::cnstr_get(x_122, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_122, 1);
lean::inc(x_127);
lean::dec(x_122);
x_130 = lean::cnstr_get(x_96, 1);
lean::inc(x_130);
lean::dec(x_96);
lean::inc(x_1);
x_134 = l_lean_elaborator_to__pexpr___main(x_130, x_1, x_127);
if (lean::obj_tag(x_134) == 0)
{
obj* x_139; obj* x_142; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_89);
lean::dec(x_125);
x_139 = lean::cnstr_get(x_134, 0);
lean::inc(x_139);
lean::dec(x_134);
if (lean::is_scalar(x_124)) {
 x_142 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_142 = x_124;
 lean::cnstr_set_tag(x_124, 0);
}
lean::cnstr_set(x_142, 0, x_139);
x_5 = x_142;
goto lbl_6;
}
else
{
obj* x_144; obj* x_147; obj* x_149; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_159; obj* x_160; obj* x_162; obj* x_163; 
lean::dec(x_124);
x_144 = lean::cnstr_get(x_134, 0);
lean::inc(x_144);
lean::dec(x_134);
x_147 = lean::cnstr_get(x_144, 0);
lean::inc(x_147);
x_149 = lean::cnstr_get(x_144, 1);
lean::inc(x_149);
lean::dec(x_144);
x_152 = lean::box(0);
x_153 = l_lean_elaborator_ident__univ__params__to__pexpr(x_89);
x_154 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_154, 0, x_147);
lean::cnstr_set(x_154, 1, x_152);
x_155 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_155, 0, x_153);
lean::cnstr_set(x_155, 1, x_154);
x_156 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_156, 0, x_125);
lean::cnstr_set(x_156, 1, x_155);
x_157 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_157);
x_159 = l_lean_expr_mk__capp(x_157, x_156);
x_160 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3;
lean::inc(x_160);
x_162 = lean_expr_mk_mdata(x_160, x_159);
x_163 = l_lean_elaborator_old__elab__command(x_0, x_162, x_1, x_149);
x_5 = x_163;
goto lbl_6;
}
}
}
else
{
obj* x_168; obj* x_170; 
lean::dec(x_11);
lean::dec(x_89);
lean::dec(x_96);
lean::dec(x_106);
x_168 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_168);
x_170 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_168, x_1, x_2);
x_5 = x_170;
goto lbl_6;
}
}
}
case 4:
{
obj* x_171; obj* x_174; obj* x_176; obj* x_178; obj* x_180; obj* x_182; 
x_171 = lean::cnstr_get(x_12, 0);
lean::inc(x_171);
lean::dec(x_12);
x_174 = lean::cnstr_get(x_171, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_171, 2);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_171, 3);
lean::inc(x_178);
x_180 = lean::cnstr_get(x_171, 4);
lean::inc(x_180);
x_182 = lean::cnstr_get(x_171, 6);
lean::inc(x_182);
lean::dec(x_171);
if (lean::obj_tag(x_174) == 0)
{
obj* x_185; obj* x_187; 
x_185 = lean::cnstr_get(x_180, 0);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_180, 1);
lean::inc(x_187);
lean::dec(x_180);
if (lean::obj_tag(x_185) == 0)
{
obj* x_196; obj* x_198; 
lean::dec(x_187);
lean::dec(x_176);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_11);
lean::dec(x_185);
x_196 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_196);
x_198 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_196, x_1, x_2);
x_5 = x_198;
goto lbl_6;
}
else
{
obj* x_199; obj* x_202; obj* x_207; 
x_199 = lean::cnstr_get(x_185, 0);
lean::inc(x_199);
lean::dec(x_185);
x_202 = lean::cnstr_get(x_11, 0);
lean::inc(x_202);
lean::dec(x_11);
lean::inc(x_1);
lean::inc(x_202);
x_207 = l_lean_elaborator_decl__modifiers__to__pexpr(x_202, x_1, x_2);
if (lean::obj_tag(x_207) == 0)
{
obj* x_216; obj* x_218; obj* x_219; 
lean::dec(x_199);
lean::dec(x_187);
lean::dec(x_202);
lean::dec(x_176);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
x_216 = lean::cnstr_get(x_207, 0);
lean::inc(x_216);
if (lean::is_shared(x_207)) {
 lean::dec(x_207);
 x_218 = lean::box(0);
} else {
 lean::cnstr_release(x_207, 0);
 x_218 = x_207;
}
if (lean::is_scalar(x_218)) {
 x_219 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_219 = x_218;
}
lean::cnstr_set(x_219, 0, x_216);
x_5 = x_219;
goto lbl_6;
}
else
{
obj* x_220; obj* x_222; obj* x_223; obj* x_225; obj* x_228; obj* x_229; obj* x_231; 
x_220 = lean::cnstr_get(x_207, 0);
lean::inc(x_220);
if (lean::is_shared(x_207)) {
 lean::dec(x_207);
 x_222 = lean::box(0);
} else {
 lean::cnstr_release(x_207, 0);
 x_222 = x_207;
}
x_223 = lean::cnstr_get(x_220, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_220, 1);
lean::inc(x_225);
lean::dec(x_220);
x_228 = lean::box(0);
x_231 = lean::cnstr_get(x_202, 1);
lean::inc(x_231);
lean::dec(x_202);
if (lean::obj_tag(x_231) == 0)
{
x_229 = x_228;
goto lbl_230;
}
else
{
obj* x_234; obj* x_237; 
x_234 = lean::cnstr_get(x_231, 0);
lean::inc(x_234);
lean::dec(x_231);
x_237 = lean::cnstr_get(x_234, 1);
lean::inc(x_237);
lean::dec(x_234);
x_229 = x_237;
goto lbl_230;
}
lbl_230:
{
obj* x_241; 
lean::inc(x_1);
x_241 = l_lean_elaborator_attrs__to__pexpr(x_229, x_1, x_225);
if (lean::obj_tag(x_241) == 0)
{
obj* x_251; obj* x_254; 
lean::dec(x_199);
lean::dec(x_187);
lean::dec(x_223);
lean::dec(x_228);
lean::dec(x_176);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
x_251 = lean::cnstr_get(x_241, 0);
lean::inc(x_251);
lean::dec(x_241);
if (lean::is_scalar(x_222)) {
 x_254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_254 = x_222;
 lean::cnstr_set_tag(x_222, 0);
}
lean::cnstr_set(x_254, 0, x_251);
x_5 = x_254;
goto lbl_6;
}
else
{
obj* x_255; obj* x_257; obj* x_258; obj* x_260; obj* x_264; obj* x_265; obj* x_267; obj* x_268; obj* x_269; 
x_255 = lean::cnstr_get(x_241, 0);
lean::inc(x_255);
if (lean::is_shared(x_241)) {
 lean::dec(x_241);
 x_257 = lean::box(0);
} else {
 lean::cnstr_release(x_241, 0);
 x_257 = x_241;
}
x_258 = lean::cnstr_get(x_255, 0);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_255, 1);
lean::inc(x_260);
lean::dec(x_255);
lean::inc(x_228);
x_264 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_264, 0, x_258);
lean::cnstr_set(x_264, 1, x_228);
x_265 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_265);
x_267 = l_lean_expr_mk__capp(x_265, x_264);
if (lean::obj_tag(x_176) == 0)
{
obj* x_271; obj* x_273; 
x_271 = l_lean_expander_get__opt__type___main(x_187);
lean::inc(x_1);
x_273 = l_lean_elaborator_to__pexpr___main(x_271, x_1, x_260);
if (lean::obj_tag(x_176) == 0)
{
if (lean::obj_tag(x_273) == 0)
{
obj* x_283; obj* x_286; 
lean::dec(x_199);
lean::dec(x_222);
lean::dec(x_223);
lean::dec(x_228);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_267);
x_283 = lean::cnstr_get(x_273, 0);
lean::inc(x_283);
lean::dec(x_273);
if (lean::is_scalar(x_257)) {
 x_286 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_286 = x_257;
 lean::cnstr_set_tag(x_257, 0);
}
lean::cnstr_set(x_286, 0, x_283);
x_5 = x_286;
goto lbl_6;
}
else
{
obj* x_288; 
lean::dec(x_257);
x_288 = lean::cnstr_get(x_273, 0);
lean::inc(x_288);
lean::dec(x_273);
x_268 = x_228;
x_269 = x_288;
goto lbl_270;
}
}
else
{
obj* x_291; 
x_291 = lean::cnstr_get(x_176, 0);
lean::inc(x_291);
lean::dec(x_176);
if (lean::obj_tag(x_273) == 0)
{
obj* x_304; obj* x_307; 
lean::dec(x_199);
lean::dec(x_222);
lean::dec(x_223);
lean::dec(x_228);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_291);
lean::dec(x_267);
x_304 = lean::cnstr_get(x_273, 0);
lean::inc(x_304);
lean::dec(x_273);
if (lean::is_scalar(x_257)) {
 x_307 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_307 = x_257;
 lean::cnstr_set_tag(x_257, 0);
}
lean::cnstr_set(x_307, 0, x_304);
x_5 = x_307;
goto lbl_6;
}
else
{
obj* x_309; obj* x_312; obj* x_315; 
lean::dec(x_257);
x_309 = lean::cnstr_get(x_273, 0);
lean::inc(x_309);
lean::dec(x_273);
x_312 = lean::cnstr_get(x_291, 1);
lean::inc(x_312);
lean::dec(x_291);
x_315 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_312);
x_268 = x_315;
x_269 = x_309;
goto lbl_270;
}
}
}
else
{
obj* x_316; obj* x_318; obj* x_320; obj* x_322; obj* x_324; obj* x_326; obj* x_328; obj* x_330; obj* x_332; obj* x_336; obj* x_337; obj* x_338; obj* x_340; obj* x_342; obj* x_344; obj* x_346; obj* x_349; obj* x_350; obj* x_352; obj* x_354; obj* x_356; obj* x_358; obj* x_360; obj* x_363; obj* x_364; obj* x_366; 
x_316 = lean::cnstr_get(x_176, 0);
lean::inc(x_316);
x_318 = lean::cnstr_get(x_260, 0);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_260, 1);
lean::inc(x_320);
x_322 = lean::cnstr_get(x_260, 2);
lean::inc(x_322);
x_324 = lean::cnstr_get(x_260, 3);
lean::inc(x_324);
x_326 = lean::cnstr_get(x_260, 4);
lean::inc(x_326);
x_328 = lean::cnstr_get(x_326, 0);
lean::inc(x_328);
x_330 = lean::cnstr_get(x_326, 1);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_316, 1);
lean::inc(x_332);
lean::dec(x_316);
lean::inc(x_332);
x_336 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(x_332);
x_337 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__5(x_330, x_336);
x_338 = lean::cnstr_get(x_326, 2);
lean::inc(x_338);
x_340 = lean::cnstr_get(x_326, 3);
lean::inc(x_340);
x_342 = lean::cnstr_get(x_326, 4);
lean::inc(x_342);
x_344 = lean::cnstr_get(x_326, 5);
lean::inc(x_344);
x_346 = lean::cnstr_get(x_326, 6);
lean::inc(x_346);
lean::dec(x_326);
x_349 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_349, 0, x_328);
lean::cnstr_set(x_349, 1, x_337);
lean::cnstr_set(x_349, 2, x_338);
lean::cnstr_set(x_349, 3, x_340);
lean::cnstr_set(x_349, 4, x_342);
lean::cnstr_set(x_349, 5, x_344);
lean::cnstr_set(x_349, 6, x_346);
x_350 = lean::cnstr_get(x_260, 5);
lean::inc(x_350);
x_352 = lean::cnstr_get(x_260, 6);
lean::inc(x_352);
x_354 = lean::cnstr_get(x_260, 7);
lean::inc(x_354);
x_356 = lean::cnstr_get(x_260, 8);
lean::inc(x_356);
x_358 = lean::cnstr_get(x_260, 9);
lean::inc(x_358);
x_360 = lean::cnstr_get(x_260, 10);
lean::inc(x_360);
lean::dec(x_260);
x_363 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_363, 0, x_318);
lean::cnstr_set(x_363, 1, x_320);
lean::cnstr_set(x_363, 2, x_322);
lean::cnstr_set(x_363, 3, x_324);
lean::cnstr_set(x_363, 4, x_349);
lean::cnstr_set(x_363, 5, x_350);
lean::cnstr_set(x_363, 6, x_352);
lean::cnstr_set(x_363, 7, x_354);
lean::cnstr_set(x_363, 8, x_356);
lean::cnstr_set(x_363, 9, x_358);
lean::cnstr_set(x_363, 10, x_360);
x_364 = l_lean_expander_get__opt__type___main(x_187);
lean::inc(x_1);
x_366 = l_lean_elaborator_to__pexpr___main(x_364, x_1, x_363);
if (lean::obj_tag(x_176) == 0)
{
lean::dec(x_332);
if (lean::obj_tag(x_366) == 0)
{
obj* x_377; obj* x_380; 
lean::dec(x_199);
lean::dec(x_222);
lean::dec(x_223);
lean::dec(x_228);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_267);
x_377 = lean::cnstr_get(x_366, 0);
lean::inc(x_377);
lean::dec(x_366);
if (lean::is_scalar(x_257)) {
 x_380 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_380 = x_257;
 lean::cnstr_set_tag(x_257, 0);
}
lean::cnstr_set(x_380, 0, x_377);
x_5 = x_380;
goto lbl_6;
}
else
{
obj* x_382; 
lean::dec(x_257);
x_382 = lean::cnstr_get(x_366, 0);
lean::inc(x_382);
lean::dec(x_366);
x_268 = x_228;
x_269 = x_382;
goto lbl_270;
}
}
else
{
lean::dec(x_176);
if (lean::obj_tag(x_366) == 0)
{
obj* x_396; obj* x_399; 
lean::dec(x_199);
lean::dec(x_222);
lean::dec(x_223);
lean::dec(x_228);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_267);
lean::dec(x_332);
x_396 = lean::cnstr_get(x_366, 0);
lean::inc(x_396);
lean::dec(x_366);
if (lean::is_scalar(x_257)) {
 x_399 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_399 = x_257;
 lean::cnstr_set_tag(x_257, 0);
}
lean::cnstr_set(x_399, 0, x_396);
x_5 = x_399;
goto lbl_6;
}
else
{
obj* x_401; obj* x_404; 
lean::dec(x_257);
x_401 = lean::cnstr_get(x_366, 0);
lean::inc(x_401);
lean::dec(x_366);
x_404 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(x_332);
x_268 = x_404;
x_269 = x_401;
goto lbl_270;
}
}
}
lbl_270:
{
obj* x_405; obj* x_407; obj* x_411; 
x_405 = lean::cnstr_get(x_269, 0);
lean::inc(x_405);
x_407 = lean::cnstr_get(x_269, 1);
lean::inc(x_407);
lean::dec(x_269);
lean::inc(x_1);
x_411 = l_lean_elaborator_simple__binders__to__pexpr(x_199, x_1, x_407);
if (lean::obj_tag(x_411) == 0)
{
obj* x_421; obj* x_424; 
lean::dec(x_223);
lean::dec(x_228);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_267);
lean::dec(x_405);
lean::dec(x_268);
x_421 = lean::cnstr_get(x_411, 0);
lean::inc(x_421);
lean::dec(x_411);
if (lean::is_scalar(x_222)) {
 x_424 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_424 = x_222;
 lean::cnstr_set_tag(x_222, 0);
}
lean::cnstr_set(x_424, 0, x_421);
x_5 = x_424;
goto lbl_6;
}
else
{
obj* x_425; obj* x_428; obj* x_430; obj* x_436; 
x_425 = lean::cnstr_get(x_411, 0);
lean::inc(x_425);
lean::dec(x_411);
x_428 = lean::cnstr_get(x_425, 0);
lean::inc(x_428);
x_430 = lean::cnstr_get(x_425, 1);
lean::inc(x_430);
lean::dec(x_425);
lean::inc(x_1);
lean::inc(x_182);
lean::inc(x_0);
x_436 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_182, x_1, x_430);
if (lean::obj_tag(x_436) == 0)
{
obj* x_447; obj* x_450; 
lean::dec(x_223);
lean::dec(x_228);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_267);
lean::dec(x_428);
lean::dec(x_405);
lean::dec(x_268);
x_447 = lean::cnstr_get(x_436, 0);
lean::inc(x_447);
lean::dec(x_436);
if (lean::is_scalar(x_222)) {
 x_450 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_450 = x_222;
 lean::cnstr_set_tag(x_222, 0);
}
lean::cnstr_set(x_450, 0, x_447);
x_5 = x_450;
goto lbl_6;
}
else
{
obj* x_452; obj* x_455; obj* x_457; obj* x_460; obj* x_461; obj* x_464; uint8 x_465; obj* x_467; obj* x_469; obj* x_471; obj* x_473; obj* x_475; obj* x_477; obj* x_478; obj* x_480; obj* x_482; obj* x_484; obj* x_485; obj* x_486; obj* x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_493; obj* x_494; obj* x_496; obj* x_497; 
lean::dec(x_222);
x_452 = lean::cnstr_get(x_436, 0);
lean::inc(x_452);
lean::dec(x_436);
x_455 = lean::cnstr_get(x_452, 0);
lean::inc(x_455);
x_457 = lean::cnstr_get(x_452, 1);
lean::inc(x_457);
lean::dec(x_452);
x_460 = l_lean_elaborator_names__to__pexpr(x_268);
x_461 = lean::cnstr_get(x_178, 0);
lean::inc(x_461);
lean::dec(x_178);
x_464 = l_lean_elaborator_mangle__ident(x_461);
x_465 = 0;
lean::inc(x_464);
x_467 = lean_expr_local(x_464, x_464, x_405, x_465);
lean::inc(x_228);
x_469 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_469, 0, x_467);
lean::cnstr_set(x_469, 1, x_228);
lean::inc(x_265);
x_471 = l_lean_expr_mk__capp(x_265, x_469);
lean::inc(x_265);
x_473 = l_lean_expr_mk__capp(x_265, x_455);
lean::inc(x_228);
x_475 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_475, 0, x_473);
lean::cnstr_set(x_475, 1, x_228);
lean::inc(x_265);
x_477 = l_lean_expr_mk__capp(x_265, x_475);
x_478 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(x_182);
lean::inc(x_265);
x_480 = l_lean_expr_mk__capp(x_265, x_478);
lean::inc(x_228);
x_482 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_482, 0, x_480);
lean::cnstr_set(x_482, 1, x_228);
lean::inc(x_265);
x_484 = l_lean_expr_mk__capp(x_265, x_482);
x_485 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_485, 0, x_484);
lean::cnstr_set(x_485, 1, x_228);
x_486 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_486, 0, x_477);
lean::cnstr_set(x_486, 1, x_485);
x_487 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_487, 0, x_428);
lean::cnstr_set(x_487, 1, x_486);
x_488 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_488, 0, x_471);
lean::cnstr_set(x_488, 1, x_487);
x_489 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_489, 0, x_460);
lean::cnstr_set(x_489, 1, x_488);
x_490 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_490, 0, x_267);
lean::cnstr_set(x_490, 1, x_489);
x_491 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_491, 0, x_223);
lean::cnstr_set(x_491, 1, x_490);
lean::inc(x_265);
x_493 = l_lean_expr_mk__capp(x_265, x_491);
x_494 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
lean::inc(x_494);
x_496 = lean_expr_mk_mdata(x_494, x_493);
x_497 = l_lean_elaborator_old__elab__command(x_0, x_496, x_1, x_457);
x_5 = x_497;
goto lbl_6;
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
obj* x_504; obj* x_506; 
lean::dec(x_180);
lean::dec(x_176);
lean::dec(x_174);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_11);
x_504 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_504);
x_506 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_504, x_1, x_2);
x_5 = x_506;
goto lbl_6;
}
}
default:
{
obj* x_507; obj* x_510; obj* x_512; obj* x_514; obj* x_516; obj* x_518; obj* x_520; obj* x_522; 
x_507 = lean::cnstr_get(x_12, 0);
lean::inc(x_507);
lean::dec(x_12);
x_510 = lean::cnstr_get(x_507, 0);
lean::inc(x_510);
x_512 = lean::cnstr_get(x_507, 1);
lean::inc(x_512);
x_514 = lean::cnstr_get(x_507, 2);
lean::inc(x_514);
x_516 = lean::cnstr_get(x_507, 3);
lean::inc(x_516);
x_518 = lean::cnstr_get(x_507, 4);
lean::inc(x_518);
x_520 = lean::cnstr_get(x_507, 6);
lean::inc(x_520);
x_522 = lean::cnstr_get(x_507, 7);
lean::inc(x_522);
lean::dec(x_507);
if (lean::obj_tag(x_510) == 0)
{
obj* x_526; obj* x_528; 
lean::dec(x_510);
x_526 = lean::cnstr_get(x_516, 0);
lean::inc(x_526);
x_528 = lean::cnstr_get(x_516, 1);
lean::inc(x_528);
lean::dec(x_516);
if (lean::obj_tag(x_526) == 0)
{
obj* x_539; obj* x_541; 
lean::dec(x_512);
lean::dec(x_11);
lean::dec(x_522);
lean::dec(x_528);
lean::dec(x_526);
lean::dec(x_514);
lean::dec(x_520);
lean::dec(x_518);
x_539 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_539);
x_541 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_539, x_1, x_2);
x_5 = x_541;
goto lbl_6;
}
else
{
obj* x_542; obj* x_545; obj* x_549; 
x_542 = lean::cnstr_get(x_526, 0);
lean::inc(x_542);
lean::dec(x_526);
x_545 = lean::cnstr_get(x_11, 0);
lean::inc(x_545);
lean::dec(x_11);
lean::inc(x_1);
x_549 = l_lean_elaborator_decl__modifiers__to__pexpr(x_545, x_1, x_2);
if (lean::obj_tag(x_549) == 0)
{
obj* x_559; obj* x_561; obj* x_562; 
lean::dec(x_512);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_542);
lean::dec(x_522);
lean::dec(x_528);
lean::dec(x_514);
lean::dec(x_520);
lean::dec(x_518);
x_559 = lean::cnstr_get(x_549, 0);
lean::inc(x_559);
if (lean::is_shared(x_549)) {
 lean::dec(x_549);
 x_561 = lean::box(0);
} else {
 lean::cnstr_release(x_549, 0);
 x_561 = x_549;
}
if (lean::is_scalar(x_561)) {
 x_562 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_562 = x_561;
}
lean::cnstr_set(x_562, 0, x_559);
x_5 = x_562;
goto lbl_6;
}
else
{
obj* x_563; obj* x_565; obj* x_566; obj* x_568; obj* x_571; obj* x_572; obj* x_573; 
x_563 = lean::cnstr_get(x_549, 0);
lean::inc(x_563);
if (lean::is_shared(x_549)) {
 lean::dec(x_549);
 x_565 = lean::box(0);
} else {
 lean::cnstr_release(x_549, 0);
 x_565 = x_549;
}
x_566 = lean::cnstr_get(x_563, 0);
lean::inc(x_566);
x_568 = lean::cnstr_get(x_563, 1);
lean::inc(x_568);
lean::dec(x_563);
x_571 = lean::box(0);
if (lean::obj_tag(x_512) == 0)
{
obj* x_575; obj* x_577; 
x_575 = l_lean_expander_get__opt__type___main(x_528);
lean::inc(x_1);
x_577 = l_lean_elaborator_to__pexpr___main(x_575, x_1, x_568);
if (lean::obj_tag(x_512) == 0)
{
if (lean::obj_tag(x_577) == 0)
{
obj* x_588; obj* x_590; obj* x_591; 
lean::dec(x_565);
lean::dec(x_566);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_542);
lean::dec(x_522);
lean::dec(x_514);
lean::dec(x_520);
lean::dec(x_518);
lean::dec(x_571);
x_588 = lean::cnstr_get(x_577, 0);
lean::inc(x_588);
if (lean::is_shared(x_577)) {
 lean::dec(x_577);
 x_590 = lean::box(0);
} else {
 lean::cnstr_release(x_577, 0);
 x_590 = x_577;
}
if (lean::is_scalar(x_590)) {
 x_591 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_591 = x_590;
}
lean::cnstr_set(x_591, 0, x_588);
x_5 = x_591;
goto lbl_6;
}
else
{
obj* x_592; 
x_592 = lean::cnstr_get(x_577, 0);
lean::inc(x_592);
lean::dec(x_577);
x_572 = x_571;
x_573 = x_592;
goto lbl_574;
}
}
else
{
obj* x_595; 
x_595 = lean::cnstr_get(x_512, 0);
lean::inc(x_595);
lean::dec(x_512);
if (lean::obj_tag(x_577) == 0)
{
obj* x_609; obj* x_611; obj* x_612; 
lean::dec(x_565);
lean::dec(x_566);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_542);
lean::dec(x_522);
lean::dec(x_514);
lean::dec(x_520);
lean::dec(x_518);
lean::dec(x_595);
lean::dec(x_571);
x_609 = lean::cnstr_get(x_577, 0);
lean::inc(x_609);
if (lean::is_shared(x_577)) {
 lean::dec(x_577);
 x_611 = lean::box(0);
} else {
 lean::cnstr_release(x_577, 0);
 x_611 = x_577;
}
if (lean::is_scalar(x_611)) {
 x_612 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_612 = x_611;
}
lean::cnstr_set(x_612, 0, x_609);
x_5 = x_612;
goto lbl_6;
}
else
{
obj* x_613; obj* x_616; obj* x_619; 
x_613 = lean::cnstr_get(x_577, 0);
lean::inc(x_613);
lean::dec(x_577);
x_616 = lean::cnstr_get(x_595, 1);
lean::inc(x_616);
lean::dec(x_595);
x_619 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(x_616);
x_572 = x_619;
x_573 = x_613;
goto lbl_574;
}
}
}
else
{
obj* x_620; obj* x_622; obj* x_624; obj* x_626; obj* x_628; obj* x_630; obj* x_632; obj* x_634; obj* x_636; obj* x_640; obj* x_641; obj* x_642; obj* x_644; obj* x_646; obj* x_648; obj* x_650; obj* x_653; obj* x_654; obj* x_656; obj* x_658; obj* x_660; obj* x_662; obj* x_664; obj* x_667; obj* x_668; obj* x_670; 
x_620 = lean::cnstr_get(x_512, 0);
lean::inc(x_620);
x_622 = lean::cnstr_get(x_568, 0);
lean::inc(x_622);
x_624 = lean::cnstr_get(x_568, 1);
lean::inc(x_624);
x_626 = lean::cnstr_get(x_568, 2);
lean::inc(x_626);
x_628 = lean::cnstr_get(x_568, 3);
lean::inc(x_628);
x_630 = lean::cnstr_get(x_568, 4);
lean::inc(x_630);
x_632 = lean::cnstr_get(x_630, 0);
lean::inc(x_632);
x_634 = lean::cnstr_get(x_630, 1);
lean::inc(x_634);
x_636 = lean::cnstr_get(x_620, 1);
lean::inc(x_636);
lean::dec(x_620);
lean::inc(x_636);
x_640 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(x_636);
x_641 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(x_634, x_640);
x_642 = lean::cnstr_get(x_630, 2);
lean::inc(x_642);
x_644 = lean::cnstr_get(x_630, 3);
lean::inc(x_644);
x_646 = lean::cnstr_get(x_630, 4);
lean::inc(x_646);
x_648 = lean::cnstr_get(x_630, 5);
lean::inc(x_648);
x_650 = lean::cnstr_get(x_630, 6);
lean::inc(x_650);
lean::dec(x_630);
x_653 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_653, 0, x_632);
lean::cnstr_set(x_653, 1, x_641);
lean::cnstr_set(x_653, 2, x_642);
lean::cnstr_set(x_653, 3, x_644);
lean::cnstr_set(x_653, 4, x_646);
lean::cnstr_set(x_653, 5, x_648);
lean::cnstr_set(x_653, 6, x_650);
x_654 = lean::cnstr_get(x_568, 5);
lean::inc(x_654);
x_656 = lean::cnstr_get(x_568, 6);
lean::inc(x_656);
x_658 = lean::cnstr_get(x_568, 7);
lean::inc(x_658);
x_660 = lean::cnstr_get(x_568, 8);
lean::inc(x_660);
x_662 = lean::cnstr_get(x_568, 9);
lean::inc(x_662);
x_664 = lean::cnstr_get(x_568, 10);
lean::inc(x_664);
lean::dec(x_568);
x_667 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_667, 0, x_622);
lean::cnstr_set(x_667, 1, x_624);
lean::cnstr_set(x_667, 2, x_626);
lean::cnstr_set(x_667, 3, x_628);
lean::cnstr_set(x_667, 4, x_653);
lean::cnstr_set(x_667, 5, x_654);
lean::cnstr_set(x_667, 6, x_656);
lean::cnstr_set(x_667, 7, x_658);
lean::cnstr_set(x_667, 8, x_660);
lean::cnstr_set(x_667, 9, x_662);
lean::cnstr_set(x_667, 10, x_664);
x_668 = l_lean_expander_get__opt__type___main(x_528);
lean::inc(x_1);
x_670 = l_lean_elaborator_to__pexpr___main(x_668, x_1, x_667);
if (lean::obj_tag(x_512) == 0)
{
lean::dec(x_636);
if (lean::obj_tag(x_670) == 0)
{
obj* x_682; obj* x_684; obj* x_685; 
lean::dec(x_565);
lean::dec(x_566);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_542);
lean::dec(x_522);
lean::dec(x_514);
lean::dec(x_520);
lean::dec(x_518);
lean::dec(x_571);
x_682 = lean::cnstr_get(x_670, 0);
lean::inc(x_682);
if (lean::is_shared(x_670)) {
 lean::dec(x_670);
 x_684 = lean::box(0);
} else {
 lean::cnstr_release(x_670, 0);
 x_684 = x_670;
}
if (lean::is_scalar(x_684)) {
 x_685 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_685 = x_684;
}
lean::cnstr_set(x_685, 0, x_682);
x_5 = x_685;
goto lbl_6;
}
else
{
obj* x_686; 
x_686 = lean::cnstr_get(x_670, 0);
lean::inc(x_686);
lean::dec(x_670);
x_572 = x_571;
x_573 = x_686;
goto lbl_574;
}
}
else
{
lean::dec(x_512);
if (lean::obj_tag(x_670) == 0)
{
obj* x_701; obj* x_703; obj* x_704; 
lean::dec(x_565);
lean::dec(x_566);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_542);
lean::dec(x_522);
lean::dec(x_514);
lean::dec(x_520);
lean::dec(x_518);
lean::dec(x_571);
lean::dec(x_636);
x_701 = lean::cnstr_get(x_670, 0);
lean::inc(x_701);
if (lean::is_shared(x_670)) {
 lean::dec(x_670);
 x_703 = lean::box(0);
} else {
 lean::cnstr_release(x_670, 0);
 x_703 = x_670;
}
if (lean::is_scalar(x_703)) {
 x_704 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_704 = x_703;
}
lean::cnstr_set(x_704, 0, x_701);
x_5 = x_704;
goto lbl_6;
}
else
{
obj* x_705; obj* x_708; 
x_705 = lean::cnstr_get(x_670, 0);
lean::inc(x_705);
lean::dec(x_670);
x_708 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(x_636);
x_572 = x_708;
x_573 = x_705;
goto lbl_574;
}
}
}
lbl_574:
{
obj* x_709; obj* x_711; obj* x_715; 
x_709 = lean::cnstr_get(x_573, 0);
lean::inc(x_709);
x_711 = lean::cnstr_get(x_573, 1);
lean::inc(x_711);
lean::dec(x_573);
lean::inc(x_1);
x_715 = l_lean_elaborator_simple__binders__to__pexpr(x_542, x_1, x_711);
if (lean::obj_tag(x_715) == 0)
{
obj* x_726; obj* x_729; 
lean::dec(x_709);
lean::dec(x_566);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_522);
lean::dec(x_514);
lean::dec(x_520);
lean::dec(x_518);
lean::dec(x_571);
lean::dec(x_572);
x_726 = lean::cnstr_get(x_715, 0);
lean::inc(x_726);
lean::dec(x_715);
if (lean::is_scalar(x_565)) {
 x_729 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_729 = x_565;
 lean::cnstr_set_tag(x_565, 0);
}
lean::cnstr_set(x_729, 0, x_726);
x_5 = x_729;
goto lbl_6;
}
else
{
obj* x_730; obj* x_733; obj* x_735; obj* x_738; obj* x_739; obj* x_742; obj* x_743; uint8 x_744; obj* x_747; obj* x_748; 
x_730 = lean::cnstr_get(x_715, 0);
lean::inc(x_730);
lean::dec(x_715);
x_733 = lean::cnstr_get(x_730, 0);
lean::inc(x_733);
x_735 = lean::cnstr_get(x_730, 1);
lean::inc(x_735);
lean::dec(x_730);
x_738 = l_lean_elaborator_names__to__pexpr(x_572);
x_739 = lean::cnstr_get(x_514, 0);
lean::inc(x_739);
lean::dec(x_514);
x_742 = l_lean_elaborator_mangle__ident(x_739);
x_743 = l_lean_elaborator_dummy;
x_744 = 0;
lean::inc(x_743);
lean::inc(x_742);
x_747 = lean_expr_local(x_742, x_742, x_743, x_744);
if (lean::obj_tag(x_518) == 0)
{
x_748 = x_571;
goto lbl_749;
}
else
{
obj* x_750; obj* x_753; 
x_750 = lean::cnstr_get(x_518, 0);
lean::inc(x_750);
lean::dec(x_518);
x_753 = lean::cnstr_get(x_750, 1);
lean::inc(x_753);
lean::dec(x_750);
x_748 = x_753;
goto lbl_749;
}
lbl_749:
{
obj* x_757; 
lean::inc(x_1);
x_757 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_748, x_1, x_735);
if (lean::obj_tag(x_757) == 0)
{
obj* x_768; obj* x_771; 
lean::dec(x_747);
lean::dec(x_709);
lean::dec(x_566);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_522);
lean::dec(x_520);
lean::dec(x_571);
lean::dec(x_733);
lean::dec(x_738);
x_768 = lean::cnstr_get(x_757, 0);
lean::inc(x_768);
lean::dec(x_757);
if (lean::is_scalar(x_565)) {
 x_771 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_771 = x_565;
 lean::cnstr_set_tag(x_565, 0);
}
lean::cnstr_set(x_771, 0, x_768);
x_5 = x_771;
goto lbl_6;
}
else
{
obj* x_772; obj* x_775; obj* x_777; obj* x_780; obj* x_782; obj* x_785; obj* x_786; 
x_772 = lean::cnstr_get(x_757, 0);
lean::inc(x_772);
lean::dec(x_757);
x_775 = lean::cnstr_get(x_772, 0);
lean::inc(x_775);
x_777 = lean::cnstr_get(x_772, 1);
lean::inc(x_777);
lean::dec(x_772);
x_780 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_780);
x_782 = l_lean_expr_mk__capp(x_780, x_775);
lean::inc(x_1);
lean::inc(x_0);
x_785 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_522, x_1, x_777);
if (lean::obj_tag(x_520) == 0)
{
obj* x_788; 
x_788 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7;
lean::inc(x_788);
x_786 = x_788;
goto lbl_787;
}
else
{
obj* x_790; obj* x_792; obj* x_795; 
x_790 = lean::cnstr_get(x_520, 0);
lean::inc(x_790);
x_792 = lean::cnstr_get(x_790, 0);
lean::inc(x_792);
lean::dec(x_790);
x_795 = l_lean_elaborator_mangle__ident(x_792);
x_786 = x_795;
goto lbl_787;
}
lbl_787:
{
obj* x_798; 
lean::inc(x_743);
lean::inc(x_786);
x_798 = lean_expr_local(x_786, x_786, x_743, x_744);
if (lean::obj_tag(x_520) == 0)
{
if (lean::obj_tag(x_785) == 0)
{
obj* x_809; obj* x_812; 
lean::dec(x_747);
lean::dec(x_709);
lean::dec(x_566);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_798);
lean::dec(x_571);
lean::dec(x_733);
lean::dec(x_782);
lean::dec(x_738);
x_809 = lean::cnstr_get(x_785, 0);
lean::inc(x_809);
lean::dec(x_785);
if (lean::is_scalar(x_565)) {
 x_812 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_812 = x_565;
 lean::cnstr_set_tag(x_565, 0);
}
lean::cnstr_set(x_812, 0, x_809);
x_5 = x_812;
goto lbl_6;
}
else
{
obj* x_814; obj* x_817; obj* x_819; obj* x_823; obj* x_824; obj* x_825; obj* x_827; obj* x_828; obj* x_829; obj* x_830; obj* x_831; obj* x_832; obj* x_833; obj* x_834; obj* x_836; obj* x_837; obj* x_839; obj* x_840; 
lean::dec(x_565);
x_814 = lean::cnstr_get(x_785, 0);
lean::inc(x_814);
lean::dec(x_785);
x_817 = lean::cnstr_get(x_814, 0);
lean::inc(x_817);
x_819 = lean::cnstr_get(x_814, 1);
lean::inc(x_819);
lean::dec(x_814);
lean::inc(x_780);
x_823 = l_lean_expr_mk__capp(x_780, x_817);
x_824 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_824, 0, x_823);
lean::cnstr_set(x_824, 1, x_571);
x_825 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5;
lean::inc(x_825);
x_827 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_827, 0, x_825);
lean::cnstr_set(x_827, 1, x_824);
x_828 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_828, 0, x_798);
lean::cnstr_set(x_828, 1, x_827);
x_829 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_829, 0, x_709);
lean::cnstr_set(x_829, 1, x_828);
x_830 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_830, 0, x_782);
lean::cnstr_set(x_830, 1, x_829);
x_831 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_831, 0, x_733);
lean::cnstr_set(x_831, 1, x_830);
x_832 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_832, 0, x_747);
lean::cnstr_set(x_832, 1, x_831);
x_833 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_833, 0, x_738);
lean::cnstr_set(x_833, 1, x_832);
x_834 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_834, 0, x_566);
lean::cnstr_set(x_834, 1, x_833);
lean::inc(x_780);
x_836 = l_lean_expr_mk__capp(x_780, x_834);
x_837 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
lean::inc(x_837);
x_839 = lean_expr_mk_mdata(x_837, x_836);
x_840 = l_lean_elaborator_old__elab__command(x_0, x_839, x_1, x_819);
x_5 = x_840;
goto lbl_6;
}
}
else
{
obj* x_841; 
x_841 = lean::cnstr_get(x_520, 0);
lean::inc(x_841);
lean::dec(x_520);
if (lean::obj_tag(x_785) == 0)
{
obj* x_855; obj* x_858; 
lean::dec(x_747);
lean::dec(x_709);
lean::dec(x_566);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_798);
lean::dec(x_841);
lean::dec(x_571);
lean::dec(x_733);
lean::dec(x_782);
lean::dec(x_738);
x_855 = lean::cnstr_get(x_785, 0);
lean::inc(x_855);
lean::dec(x_785);
if (lean::is_scalar(x_565)) {
 x_858 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_858 = x_565;
 lean::cnstr_set_tag(x_565, 0);
}
lean::cnstr_set(x_858, 0, x_855);
x_5 = x_858;
goto lbl_6;
}
else
{
obj* x_860; obj* x_863; obj* x_865; obj* x_868; obj* x_871; obj* x_873; obj* x_874; obj* x_875; obj* x_876; obj* x_877; obj* x_878; obj* x_879; obj* x_880; obj* x_881; obj* x_882; obj* x_884; obj* x_885; obj* x_887; obj* x_888; 
lean::dec(x_565);
x_860 = lean::cnstr_get(x_785, 0);
lean::inc(x_860);
lean::dec(x_785);
x_863 = lean::cnstr_get(x_860, 0);
lean::inc(x_863);
x_865 = lean::cnstr_get(x_860, 1);
lean::inc(x_865);
lean::dec(x_860);
x_868 = lean::cnstr_get(x_841, 1);
lean::inc(x_868);
lean::dec(x_841);
x_871 = l_lean_elaborator_infer__mod__to__pexpr(x_868);
lean::inc(x_780);
x_873 = l_lean_expr_mk__capp(x_780, x_863);
x_874 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_874, 0, x_873);
lean::cnstr_set(x_874, 1, x_571);
x_875 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_875, 0, x_871);
lean::cnstr_set(x_875, 1, x_874);
x_876 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_876, 0, x_798);
lean::cnstr_set(x_876, 1, x_875);
x_877 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_877, 0, x_709);
lean::cnstr_set(x_877, 1, x_876);
x_878 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_878, 0, x_782);
lean::cnstr_set(x_878, 1, x_877);
x_879 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_879, 0, x_733);
lean::cnstr_set(x_879, 1, x_878);
x_880 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_880, 0, x_747);
lean::cnstr_set(x_880, 1, x_879);
x_881 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_881, 0, x_738);
lean::cnstr_set(x_881, 1, x_880);
x_882 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_882, 0, x_566);
lean::cnstr_set(x_882, 1, x_881);
lean::inc(x_780);
x_884 = l_lean_expr_mk__capp(x_780, x_882);
x_885 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
lean::inc(x_885);
x_887 = lean_expr_mk_mdata(x_885, x_884);
x_888 = l_lean_elaborator_old__elab__command(x_0, x_887, x_1, x_865);
x_5 = x_888;
goto lbl_6;
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
obj* x_897; obj* x_899; 
lean::dec(x_512);
lean::dec(x_510);
lean::dec(x_11);
lean::dec(x_522);
lean::dec(x_516);
lean::dec(x_514);
lean::dec(x_520);
lean::dec(x_518);
x_897 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_897);
x_899 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_897, x_1, x_2);
x_5 = x_899;
goto lbl_6;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_901; obj* x_903; obj* x_904; 
lean::dec(x_3);
x_901 = lean::cnstr_get(x_5, 0);
lean::inc(x_901);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_903 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_903 = x_5;
}
if (lean::is_scalar(x_903)) {
 x_904 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_904 = x_903;
}
lean::cnstr_set(x_904, 0, x_901);
return x_904;
}
else
{
obj* x_905; obj* x_907; obj* x_908; obj* x_910; obj* x_911; obj* x_913; obj* x_915; obj* x_917; obj* x_919; obj* x_921; obj* x_923; obj* x_925; obj* x_927; obj* x_929; obj* x_932; obj* x_933; obj* x_934; obj* x_935; 
x_905 = lean::cnstr_get(x_5, 0);
lean::inc(x_905);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_907 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_907 = x_5;
}
x_908 = lean::cnstr_get(x_905, 1);
lean::inc(x_908);
if (lean::is_shared(x_905)) {
 lean::dec(x_905);
 x_910 = lean::box(0);
} else {
 lean::cnstr_release(x_905, 0);
 lean::cnstr_release(x_905, 1);
 x_910 = x_905;
}
x_911 = lean::cnstr_get(x_908, 0);
lean::inc(x_911);
x_913 = lean::cnstr_get(x_908, 1);
lean::inc(x_913);
x_915 = lean::cnstr_get(x_908, 2);
lean::inc(x_915);
x_917 = lean::cnstr_get(x_908, 3);
lean::inc(x_917);
x_919 = lean::cnstr_get(x_908, 5);
lean::inc(x_919);
x_921 = lean::cnstr_get(x_908, 6);
lean::inc(x_921);
x_923 = lean::cnstr_get(x_908, 7);
lean::inc(x_923);
x_925 = lean::cnstr_get(x_908, 8);
lean::inc(x_925);
x_927 = lean::cnstr_get(x_908, 9);
lean::inc(x_927);
x_929 = lean::cnstr_get(x_908, 10);
lean::inc(x_929);
lean::dec(x_908);
x_932 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_932, 0, x_911);
lean::cnstr_set(x_932, 1, x_913);
lean::cnstr_set(x_932, 2, x_915);
lean::cnstr_set(x_932, 3, x_917);
lean::cnstr_set(x_932, 4, x_3);
lean::cnstr_set(x_932, 5, x_919);
lean::cnstr_set(x_932, 6, x_921);
lean::cnstr_set(x_932, 7, x_923);
lean::cnstr_set(x_932, 8, x_925);
lean::cnstr_set(x_932, 9, x_927);
lean::cnstr_set(x_932, 10, x_929);
x_933 = lean::box(0);
if (lean::is_scalar(x_910)) {
 x_934 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_934 = x_910;
}
lean::cnstr_set(x_934, 0, x_933);
lean::cnstr_set(x_934, 1, x_932);
if (lean::is_scalar(x_907)) {
 x_935 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_935 = x_907;
}
lean::cnstr_set(x_935, 0, x_934);
return x_935;
}
}
}
}
obj* l_lean_elaborator_declaration_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_2, x_1);
return x_5;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; 
lean::inc(x_2);
lean::inc(x_1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 2);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_11);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_2);
x_16 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(x_9, x_1, x_15);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_11, x_17);
lean::dec(x_17);
lean::dec(x_11);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_16);
lean::cnstr_set(x_21, 2, x_18);
return x_21;
}
}
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; uint8 x_29; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_10 = x_0;
}
lean::inc(x_6);
x_14 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_6);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 lean::cnstr_release(x_17, 1);
 x_24 = x_17;
}
x_27 = l_lean_expander_binding__annotation__update;
lean::inc(x_27);
x_29 = l_lean_parser_syntax_is__of__kind___main(x_27, x_22);
if (x_29 == 0)
{
uint8 x_33; obj* x_34; obj* x_35; 
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_20);
x_33 = 1;
x_34 = lean::box(x_33);
if (lean::is_scalar(x_24)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_24;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_2);
x_11 = x_35;
goto lbl_12;
}
else
{
obj* x_37; 
lean::dec(x_24);
x_37 = lean::box(0);
x_25 = x_37;
goto lbl_26;
}
lbl_12:
{
obj* x_38; obj* x_40; obj* x_42; obj* x_43; 
x_38 = lean::cnstr_get(x_11, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_11, 1);
lean::inc(x_40);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_42 = x_11;
}
x_43 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_8, x_1, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_42);
lean::dec(x_38);
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
obj* x_52; obj* x_54; obj* x_55; obj* x_57; uint8 x_60; 
x_52 = lean::cnstr_get(x_43, 0);
lean::inc(x_52);
if (lean::is_shared(x_43)) {
 lean::dec(x_43);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_43, 0);
 x_54 = x_43;
}
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 1);
lean::inc(x_57);
lean::dec(x_52);
x_60 = lean::unbox(x_38);
lean::dec(x_38);
if (x_60 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_6);
lean::dec(x_10);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_55);
lean::cnstr_set(x_64, 1, x_57);
if (lean::is_scalar(x_54)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_54;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; 
if (lean::is_scalar(x_10)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_10;
}
lean::cnstr_set(x_66, 0, x_6);
lean::cnstr_set(x_66, 1, x_55);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_57);
if (lean::is_scalar(x_54)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_54;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
lbl_26:
{
obj* x_70; obj* x_71; obj* x_73; obj* x_77; 
lean::dec(x_25);
x_70 = l_lean_elaborator_mangle__ident(x_20);
x_71 = lean::cnstr_get(x_2, 4);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_71, 2);
lean::inc(x_73);
lean::inc(x_70);
lean::inc(x_73);
x_77 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_73, x_70);
if (lean::obj_tag(x_77) == 0)
{
obj* x_81; obj* x_82; obj* x_85; obj* x_86; obj* x_89; obj* x_90; obj* x_91; obj* x_94; 
lean::dec(x_15);
lean::dec(x_71);
lean::dec(x_73);
x_81 = lean::box(0);
x_82 = l_lean_name_to__string___closed__1;
lean::inc(x_70);
lean::inc(x_82);
x_85 = l_lean_name_to__string__with__sep___main(x_82, x_70);
x_86 = l_lean_parser_substring_of__string(x_85);
lean::inc(x_81);
lean::inc(x_81);
x_89 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_89, 0, x_81);
lean::cnstr_set(x_89, 1, x_86);
lean::cnstr_set(x_89, 2, x_70);
lean::cnstr_set(x_89, 3, x_81);
lean::cnstr_set(x_89, 4, x_81);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
x_91 = l_string_join___closed__1;
lean::inc(x_1);
lean::inc(x_91);
x_94 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_90, x_91, x_1, x_2);
if (lean::obj_tag(x_94) == 0)
{
obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_19);
x_100 = lean::cnstr_get(x_94, 0);
lean::inc(x_100);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_102 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 x_102 = x_94;
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
return x_103;
}
else
{
obj* x_104; obj* x_107; uint8 x_110; obj* x_111; obj* x_112; 
x_104 = lean::cnstr_get(x_94, 0);
lean::inc(x_104);
lean::dec(x_94);
x_107 = lean::cnstr_get(x_104, 1);
lean::inc(x_107);
lean::dec(x_104);
x_110 = 0;
x_111 = lean::box(x_110);
if (lean::is_scalar(x_19)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_19;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_107);
x_11 = x_112;
goto lbl_12;
}
}
else
{
obj* x_113; obj* x_116; obj* x_119; obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_136; uint8 x_137; obj* x_139; obj* x_140; obj* x_141; obj* x_143; obj* x_145; obj* x_147; obj* x_150; obj* x_151; obj* x_153; obj* x_155; obj* x_157; obj* x_159; obj* x_161; obj* x_164; uint8 x_165; obj* x_166; obj* x_167; 
x_113 = lean::cnstr_get(x_77, 0);
lean::inc(x_113);
lean::dec(x_77);
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
lean::dec(x_113);
x_119 = lean::cnstr_get(x_2, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_2, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_2, 2);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_2, 3);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_71, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_71, 1);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_116, 0);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_116, 1);
lean::inc(x_133);
lean::dec(x_116);
x_136 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_136, 0, x_131);
lean::cnstr_set(x_136, 1, x_133);
x_137 = lean::unbox(x_15);
lean::dec(x_15);
lean::cnstr_set_scalar(x_136, sizeof(void*)*2, x_137);
x_139 = x_136;
x_140 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(x_73, x_70, x_139);
x_141 = lean::cnstr_get(x_71, 3);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_71, 4);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_71, 5);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_71, 6);
lean::inc(x_147);
lean::dec(x_71);
x_150 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_150, 0, x_127);
lean::cnstr_set(x_150, 1, x_129);
lean::cnstr_set(x_150, 2, x_140);
lean::cnstr_set(x_150, 3, x_141);
lean::cnstr_set(x_150, 4, x_143);
lean::cnstr_set(x_150, 5, x_145);
lean::cnstr_set(x_150, 6, x_147);
x_151 = lean::cnstr_get(x_2, 5);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_2, 6);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_2, 7);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_2, 8);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_2, 9);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_2, 10);
lean::inc(x_161);
lean::dec(x_2);
x_164 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_164, 0, x_119);
lean::cnstr_set(x_164, 1, x_121);
lean::cnstr_set(x_164, 2, x_123);
lean::cnstr_set(x_164, 3, x_125);
lean::cnstr_set(x_164, 4, x_150);
lean::cnstr_set(x_164, 5, x_151);
lean::cnstr_set(x_164, 6, x_153);
lean::cnstr_set(x_164, 7, x_155);
lean::cnstr_set(x_164, 8, x_157);
lean::cnstr_set(x_164, 9, x_159);
lean::cnstr_set(x_164, 10, x_161);
x_165 = 0;
x_166 = lean::box(x_165);
if (lean::is_scalar(x_19)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_19;
}
lean::cnstr_set(x_167, 0, x_166);
lean::cnstr_set(x_167, 1, x_164);
x_11 = x_167;
goto lbl_12;
}
}
}
}
}
obj* _init_l_lean_elaborator_variables_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("variables.elaborate: unexpected input");
return x_0;
}
}
obj* _init_l_lean_elaborator_variables_elaborate___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("variables");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
}
}
obj* l_lean_elaborator_variables_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
x_3 = l_lean_parser_command_variables_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::inc(x_0);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; obj* x_16; 
lean::dec(x_8);
x_12 = l_lean_elaborator_variables_elaborate___closed__1;
lean::inc(x_1);
lean::inc(x_12);
lean::inc(x_0);
x_16 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_12, x_1, x_2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_1);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_21 = x_16;
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
obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_32; 
x_23 = lean::cnstr_get(x_16, 0);
lean::inc(x_23);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_25 = x_16;
}
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
lean::dec(x_23);
lean::inc(x_1);
x_32 = l_lean_elaborator_simple__binders__to__pexpr(x_26, x_1, x_28);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; obj* x_38; 
lean::dec(x_1);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
lean::dec(x_32);
if (lean::is_scalar(x_25)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_25;
 lean::cnstr_set_tag(x_25, 0);
}
lean::cnstr_set(x_38, 0, x_35);
return x_38;
}
else
{
obj* x_40; obj* x_43; obj* x_45; obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_25);
x_40 = lean::cnstr_get(x_32, 0);
lean::inc(x_40);
lean::dec(x_32);
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
x_48 = l_lean_elaborator_variables_elaborate___closed__2;
lean::inc(x_48);
x_50 = lean_expr_mk_mdata(x_48, x_43);
x_51 = l_lean_elaborator_old__elab__command(x_0, x_50, x_1, x_45);
return x_51;
}
}
}
else
{
obj* x_52; obj* x_56; 
x_52 = lean::cnstr_get(x_8, 0);
lean::inc(x_52);
lean::dec(x_8);
lean::inc(x_1);
x_56 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_52, x_1, x_2);
if (lean::obj_tag(x_56) == 0)
{
obj* x_59; obj* x_61; obj* x_62; 
lean::dec(x_1);
lean::dec(x_0);
x_59 = lean::cnstr_get(x_56, 0);
lean::inc(x_59);
if (lean::is_shared(x_56)) {
 lean::dec(x_56);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_56, 0);
 x_61 = x_56;
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
obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_72; 
x_63 = lean::cnstr_get(x_56, 0);
lean::inc(x_63);
if (lean::is_shared(x_56)) {
 lean::dec(x_56);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_56, 0);
 x_65 = x_56;
}
x_66 = lean::cnstr_get(x_63, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_63, 1);
lean::inc(x_68);
lean::dec(x_63);
lean::inc(x_1);
x_72 = l_lean_elaborator_simple__binders__to__pexpr(x_66, x_1, x_68);
if (lean::obj_tag(x_72) == 0)
{
obj* x_75; obj* x_78; 
lean::dec(x_1);
lean::dec(x_0);
x_75 = lean::cnstr_get(x_72, 0);
lean::inc(x_75);
lean::dec(x_72);
if (lean::is_scalar(x_65)) {
 x_78 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_78 = x_65;
 lean::cnstr_set_tag(x_65, 0);
}
lean::cnstr_set(x_78, 0, x_75);
return x_78;
}
else
{
obj* x_80; obj* x_83; obj* x_85; obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_65);
x_80 = lean::cnstr_get(x_72, 0);
lean::inc(x_80);
lean::dec(x_72);
x_83 = lean::cnstr_get(x_80, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_80, 1);
lean::inc(x_85);
lean::dec(x_80);
x_88 = l_lean_elaborator_variables_elaborate___closed__2;
lean::inc(x_88);
x_90 = lean_expr_mk_mdata(x_88, x_83);
x_91 = l_lean_elaborator_old__elab__command(x_0, x_90, x_1, x_85);
return x_91;
}
}
}
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_include_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_elaborator_include_elaborate___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_mangle__ident(x_2);
x_8 = lean::box(0);
x_9 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(x_0, x_7, x_8);
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* l_lean_elaborator_include_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_1);
x_4 = l_lean_parser_command_include_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::apply_1(x_5, x_0);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 3);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 4);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_16, 2);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_16, 3);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_7, 1);
lean::inc(x_26);
lean::dec(x_7);
x_29 = l_list_foldl___main___at_lean_elaborator_include_elaborate___spec__2(x_24, x_26);
x_30 = lean::cnstr_get(x_16, 4);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_16, 5);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_16, 6);
lean::inc(x_34);
lean::dec(x_16);
x_37 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_37, 0, x_18);
lean::cnstr_set(x_37, 1, x_20);
lean::cnstr_set(x_37, 2, x_22);
lean::cnstr_set(x_37, 3, x_29);
lean::cnstr_set(x_37, 4, x_30);
lean::cnstr_set(x_37, 5, x_32);
lean::cnstr_set(x_37, 6, x_34);
x_38 = lean::cnstr_get(x_2, 5);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_2, 6);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_2, 7);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_2, 8);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_2, 9);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_2, 10);
lean::inc(x_48);
lean::dec(x_2);
x_51 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_51, 0, x_8);
lean::cnstr_set(x_51, 1, x_10);
lean::cnstr_set(x_51, 2, x_12);
lean::cnstr_set(x_51, 3, x_14);
lean::cnstr_set(x_51, 4, x_37);
lean::cnstr_set(x_51, 5, x_38);
lean::cnstr_set(x_51, 6, x_40);
lean::cnstr_set(x_51, 7, x_42);
lean::cnstr_set(x_51, 8, x_44);
lean::cnstr_set(x_51, 9, x_46);
lean::cnstr_set(x_51, 10, x_48);
x_52 = lean::box(0);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_51);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
obj* _init_l_lean_elaborator_module_header_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("not implemented: imports");
return x_0;
}
}
obj* l_lean_elaborator_module_header_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; 
x_3 = l_lean_parser_module_header_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::inc(x_0);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_14; obj* x_16; 
lean::dec(x_10);
x_14 = l_lean_elaborator_module_header_elaborate___closed__1;
lean::inc(x_14);
x_16 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_14, x_1, x_2);
return x_16;
}
else
{
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_1);
lean::dec(x_0);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_2);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
else
{
obj* x_24; obj* x_26; 
lean::dec(x_10);
x_24 = l_lean_elaborator_module_header_elaborate___closed__1;
lean::inc(x_24);
x_26 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_24, x_1, x_2);
return x_26;
}
}
}
}
obj* l_lean_elaborator_prec__to__nat___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::mk_nat_obj(0u);
return x_1;
}
else
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_5);
return x_8;
}
}
}
obj* l_lean_elaborator_prec__to__nat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_prec__to__nat___main(x_0);
return x_1;
}
}
obj* _init_l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("register_notation_tokens: unreachable");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_13; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 3);
lean::inc(x_13);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_19; 
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_0);
x_19 = l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1;
lean::inc(x_19);
return x_19;
}
else
{
obj* x_21; obj* x_24; obj* x_26; obj* x_28; obj* x_31; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; 
x_21 = lean::cnstr_get(x_11, 0);
lean::inc(x_21);
lean::dec(x_11);
x_24 = lean::cnstr_get(x_0, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_24, 1);
lean::inc(x_28);
lean::dec(x_24);
x_31 = lean::cnstr_get(x_21, 1);
lean::inc(x_31);
lean::dec(x_21);
x_34 = l_string_trim(x_31);
x_35 = l_lean_elaborator_prec__to__nat___main(x_13);
x_36 = lean::box(0);
lean::inc(x_34);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set(x_38, 1, x_35);
lean::cnstr_set(x_38, 2, x_36);
x_39 = l_lean_parser_trie_insert___rarg(x_28, x_34, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_26);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::cnstr_get(x_0, 1);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_0, 2);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_0, 3);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_0, 4);
lean::inc(x_47);
lean::dec(x_0);
x_50 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_50, 0, x_40);
lean::cnstr_set(x_50, 1, x_41);
lean::cnstr_set(x_50, 2, x_43);
lean::cnstr_set(x_50, 3, x_45);
lean::cnstr_set(x_50, 4, x_47);
x_0 = x_50;
x_1 = x_5;
goto _start;
}
}
}
}
obj* l_lean_elaborator_command__parser__config_register__notation__tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1(x_1, x_2);
return x_5;
}
}
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(obj* x_0) {
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
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
}
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_binder__ident_parser), 5, 0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_binders_parser), 5, 0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("register_notation_parser: unimplemented");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("register_notation_parser: unreachable");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_lean_expander_expand__bracketed__binder___main___closed__4;
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
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
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 1);
lean::inc(x_14);
lean::dec(x_12);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; 
lean::dec(x_3);
x_18 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5;
lean::inc(x_18);
x_8 = x_18;
goto lbl_9;
}
else
{
obj* x_20; obj* x_23; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_20 = lean::cnstr_get(x_14, 0);
lean::inc(x_20);
lean::dec(x_14);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_26 = l_string_trim(x_23);
lean::inc(x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_28, 0, x_26);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1), 8, 3);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_29);
lean::closure_set(x_30, 2, x_28);
x_10 = x_30;
goto lbl_11;
}
lbl_9:
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_7);
lean::dec(x_5);
x_33 = lean::cnstr_get(x_8, 0);
lean::inc(x_33);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_35 = x_8;
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
obj* x_37; obj* x_39; obj* x_40; 
x_37 = lean::cnstr_get(x_8, 0);
lean::inc(x_37);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_39 = x_8;
}
x_40 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(x_5);
if (lean::obj_tag(x_40) == 0)
{
obj* x_43; obj* x_46; 
lean::dec(x_7);
lean::dec(x_37);
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
lean::dec(x_40);
if (lean::is_scalar(x_39)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_39;
 lean::cnstr_set_tag(x_39, 0);
}
lean::cnstr_set(x_46, 0, x_43);
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_51; 
x_47 = lean::cnstr_get(x_40, 0);
lean::inc(x_47);
lean::dec(x_40);
if (lean::is_scalar(x_7)) {
 x_50 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_50 = x_7;
}
lean::cnstr_set(x_50, 0, x_37);
lean::cnstr_set(x_50, 1, x_47);
if (lean::is_scalar(x_39)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_39;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
}
}
lbl_11:
{
obj* x_52; obj* x_54; 
x_54 = lean::cnstr_get(x_3, 1);
lean::inc(x_54);
lean::dec(x_3);
if (lean::obj_tag(x_54) == 0)
{
obj* x_57; 
x_57 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_57);
x_52 = x_57;
goto lbl_53;
}
else
{
obj* x_59; obj* x_61; 
x_59 = lean::cnstr_get(x_54, 0);
lean::inc(x_59);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_61 = x_54;
}
switch (lean::obj_tag(x_59)) {
case 0:
{
obj* x_64; 
lean::dec(x_59);
lean::dec(x_61);
x_64 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
lean::inc(x_64);
x_52 = x_64;
goto lbl_53;
}
case 1:
{
obj* x_68; 
lean::dec(x_59);
lean::dec(x_61);
x_68 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2;
lean::inc(x_68);
x_52 = x_68;
goto lbl_53;
}
default:
{
obj* x_70; obj* x_73; 
x_70 = lean::cnstr_get(x_59, 0);
lean::inc(x_70);
lean::dec(x_59);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_77; 
lean::dec(x_61);
x_77 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3;
lean::inc(x_77);
x_52 = x_77;
goto lbl_53;
}
else
{
obj* x_79; obj* x_82; 
x_79 = lean::cnstr_get(x_73, 0);
lean::inc(x_79);
lean::dec(x_73);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
switch (lean::obj_tag(x_82)) {
case 0:
{
obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
lean::dec(x_82);
x_88 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_85);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_89, 0, x_88);
if (lean::is_scalar(x_61)) {
 x_90 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_90 = x_61;
}
lean::cnstr_set(x_90, 0, x_89);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
x_52 = x_91;
goto lbl_53;
}
case 2:
{
obj* x_92; obj* x_95; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_92 = lean::cnstr_get(x_82, 0);
lean::inc(x_92);
lean::dec(x_82);
x_95 = lean::cnstr_get(x_92, 2);
lean::inc(x_95);
lean::dec(x_92);
x_98 = l_lean_elaborator_prec__to__nat___main(x_95);
x_99 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_99, 0, x_98);
if (lean::is_scalar(x_61)) {
 x_100 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_100 = x_61;
}
lean::cnstr_set(x_100, 0, x_99);
x_101 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
x_52 = x_101;
goto lbl_53;
}
default:
{
obj* x_104; 
lean::dec(x_82);
lean::dec(x_61);
x_104 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
lean::inc(x_104);
x_52 = x_104;
goto lbl_53;
}
}
}
}
}
}
lbl_53:
{
if (lean::obj_tag(x_52) == 0)
{
obj* x_107; obj* x_109; obj* x_110; 
lean::dec(x_10);
x_107 = lean::cnstr_get(x_52, 0);
lean::inc(x_107);
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 x_109 = x_52;
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
x_8 = x_110;
goto lbl_9;
}
else
{
obj* x_111; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_111 = lean::cnstr_get(x_52, 0);
lean::inc(x_111);
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_113 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 x_113 = x_52;
}
x_114 = l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(x_111);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_10);
lean::cnstr_set(x_115, 1, x_114);
if (lean::is_scalar(x_113)) {
 x_116 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_116 = x_113;
}
lean::cnstr_set(x_116, 0, x_115);
x_8 = x_116;
goto lbl_9;
}
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(obj* x_0) {
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
x_7 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(x_4);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
}
obj* l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; 
lean::dec(x_1);
x_8 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(obj* x_0) {
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4), 7, 1);
lean::closure_set(x_7, 0, x_2);
x_8 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(x_4);
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
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(obj* x_0) {
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4), 7, 1);
lean::closure_set(x_7, 0, x_2);
x_8 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(x_4);
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
obj* _init_l_lean_elaborator_command__parser__config_register__notation__parser___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_get__leading), 6, 0);
return x_0;
}
}
obj* l_lean_elaborator_command__parser__config_register__notation__parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::inc(x_5);
x_8 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_16 = x_8;
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
x_18 = lean::cnstr_get(x_8, 0);
lean::inc(x_18);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_20 = x_8;
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_29; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_18);
lean::dec(x_20);
x_29 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5;
lean::inc(x_29);
return x_29;
}
else
{
obj* x_31; obj* x_34; obj* x_37; 
x_31 = lean::cnstr_get(x_5, 0);
lean::inc(x_31);
lean::dec(x_5);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_46; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_18);
lean::dec(x_20);
x_46 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5;
lean::inc(x_46);
return x_46;
}
else
{
obj* x_48; obj* x_51; obj* x_54; 
x_48 = lean::cnstr_get(x_37, 0);
lean::inc(x_48);
lean::dec(x_37);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
x_54 = l_string_trim(x_51);
x_21 = x_54;
goto lbl_22;
}
}
lbl_22:
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(x_18);
x_56 = l_list_join___main___rarg(x_55);
x_57 = lean::cnstr_get(x_1, 0);
lean::inc(x_57);
lean::dec(x_1);
if (lean::obj_tag(x_57) == 0)
{
obj* x_60; 
x_60 = lean::cnstr_get(x_3, 0);
lean::inc(x_60);
lean::dec(x_3);
if (lean::obj_tag(x_60) == 0)
{
obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_75; obj* x_78; obj* x_79; 
x_63 = lean::cnstr_get(x_2, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_2, 1);
lean::inc(x_65);
x_67 = lean::box(0);
x_68 = lean_name_mk_string(x_67, x_21);
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1), 7, 2);
lean::closure_set(x_69, 0, x_0);
lean::closure_set(x_69, 1, x_56);
x_70 = l_lean_parser_token__map_insert___rarg(x_65, x_68, x_69);
x_71 = lean::cnstr_get(x_2, 2);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_2, 3);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_2, 4);
lean::inc(x_75);
lean::dec(x_2);
x_78 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_78, 0, x_63);
lean::cnstr_set(x_78, 1, x_70);
lean::cnstr_set(x_78, 2, x_71);
lean::cnstr_set(x_78, 3, x_73);
lean::cnstr_set(x_78, 4, x_75);
if (lean::is_scalar(x_20)) {
 x_79 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_79 = x_20;
}
lean::cnstr_set(x_79, 0, x_78);
return x_79;
}
else
{
obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_97; obj* x_100; obj* x_101; 
lean::dec(x_60);
x_81 = lean::cnstr_get(x_2, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_2, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_2, 2);
lean::inc(x_85);
x_87 = lean::box(0);
x_88 = lean_name_mk_string(x_87, x_21);
x_89 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(x_56);
x_90 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
lean::inc(x_90);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set(x_92, 1, x_89);
x_93 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3), 8, 2);
lean::closure_set(x_93, 0, x_0);
lean::closure_set(x_93, 1, x_92);
x_94 = l_lean_parser_token__map_insert___rarg(x_85, x_88, x_93);
x_95 = lean::cnstr_get(x_2, 3);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_2, 4);
lean::inc(x_97);
lean::dec(x_2);
x_100 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_100, 0, x_81);
lean::cnstr_set(x_100, 1, x_83);
lean::cnstr_set(x_100, 2, x_94);
lean::cnstr_set(x_100, 3, x_95);
lean::cnstr_set(x_100, 4, x_97);
if (lean::is_scalar(x_20)) {
 x_101 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_101 = x_20;
}
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
}
else
{
obj* x_103; 
lean::dec(x_57);
x_103 = lean::cnstr_get(x_3, 0);
lean::inc(x_103);
lean::dec(x_3);
if (lean::obj_tag(x_103) == 0)
{
obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_121; obj* x_122; 
x_106 = lean::cnstr_get(x_2, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_2, 1);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_2, 2);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_2, 3);
lean::inc(x_112);
x_114 = lean::box(0);
x_115 = lean_name_mk_string(x_114, x_21);
x_116 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1), 7, 2);
lean::closure_set(x_116, 0, x_0);
lean::closure_set(x_116, 1, x_56);
x_117 = l_lean_parser_token__map_insert___rarg(x_112, x_115, x_116);
x_118 = lean::cnstr_get(x_2, 4);
lean::inc(x_118);
lean::dec(x_2);
x_121 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_121, 0, x_106);
lean::cnstr_set(x_121, 1, x_108);
lean::cnstr_set(x_121, 2, x_110);
lean::cnstr_set(x_121, 3, x_117);
lean::cnstr_set(x_121, 4, x_118);
if (lean::is_scalar(x_20)) {
 x_122 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_122 = x_20;
}
lean::cnstr_set(x_122, 0, x_121);
return x_122;
}
else
{
obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
lean::dec(x_103);
x_124 = lean::cnstr_get(x_2, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_2, 1);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_2, 2);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_2, 3);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_2, 4);
lean::inc(x_132);
lean::dec(x_2);
x_135 = lean::box(0);
x_136 = lean_name_mk_string(x_135, x_21);
x_137 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(x_56);
x_138 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
lean::inc(x_138);
x_140 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_140, 0, x_138);
lean::cnstr_set(x_140, 1, x_137);
x_141 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3), 8, 2);
lean::closure_set(x_141, 0, x_0);
lean::closure_set(x_141, 1, x_140);
x_142 = l_lean_parser_token__map_insert___rarg(x_132, x_136, x_141);
x_143 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_143, 0, x_124);
lean::cnstr_set(x_143, 1, x_126);
lean::cnstr_set(x_143, 2, x_128);
lean::cnstr_set(x_143, 3, x_130);
lean::cnstr_set(x_143, 4, x_142);
if (lean::is_scalar(x_20)) {
 x_144 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_144 = x_20;
}
lean::cnstr_set(x_144, 0, x_143);
return x_144;
}
}
}
}
}
}
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_7, 2);
lean::inc(x_12);
x_14 = l_lean_elaborator_command__parser__config_register__notation__tokens(x_12, x_0);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_23; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_17 = x_14;
}
x_18 = l_lean_parser_command_reserve__notation_has__view;
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
x_21 = lean::apply_1(x_19, x_7);
lean::inc(x_2);
x_23 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_21, x_15, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; obj* x_29; 
lean::dec(x_9);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
lean::dec(x_23);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_26);
return x_29;
}
else
{
obj* x_31; obj* x_34; obj* x_36; 
lean::dec(x_17);
x_31 = lean::cnstr_get(x_23, 0);
lean::inc(x_31);
lean::dec(x_23);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::dec(x_31);
x_0 = x_34;
x_1 = x_9;
x_3 = x_36;
goto _start;
}
}
else
{
obj* x_41; 
lean::dec(x_7);
x_41 = lean::cnstr_get(x_14, 0);
lean::inc(x_41);
lean::dec(x_14);
x_0 = x_41;
x_1 = x_9;
goto _start;
}
}
}
}
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_16; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 2);
lean::inc(x_14);
x_16 = l_lean_elaborator_command__parser__config_register__notation__tokens(x_14, x_0);
if (lean::obj_tag(x_16) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_26; 
lean::dec(x_7);
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_20 = x_16;
}
x_21 = l_lean_parser_command_notation_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_12);
lean::inc(x_2);
x_26 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_24, x_18, x_2, x_3);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_32; 
lean::dec(x_9);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
lean::dec(x_26);
if (lean::is_scalar(x_20)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_20;
}
lean::cnstr_set(x_32, 0, x_29);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_39; 
lean::dec(x_20);
x_34 = lean::cnstr_get(x_26, 0);
lean::inc(x_34);
lean::dec(x_26);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_0 = x_37;
x_1 = x_9;
x_3 = x_39;
goto _start;
}
}
else
{
obj* x_43; obj* x_45; obj* x_46; obj* x_50; 
x_43 = lean::cnstr_get(x_16, 0);
lean::inc(x_43);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_45 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_45 = x_16;
}
x_46 = lean::cnstr_get(x_7, 0);
lean::inc(x_46);
lean::dec(x_7);
lean::inc(x_12);
x_50 = l_lean_elaborator_command__parser__config_register__notation__parser(x_46, x_12, x_43);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_54; obj* x_55; obj* x_57; obj* x_59; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
lean::dec(x_50);
x_54 = l_lean_parser_command_notation_has__view;
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
x_57 = lean::apply_1(x_55, x_12);
lean::inc(x_2);
x_59 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_57, x_51, x_2, x_3);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_65; 
lean::dec(x_9);
lean::dec(x_2);
x_62 = lean::cnstr_get(x_59, 0);
lean::inc(x_62);
lean::dec(x_59);
if (lean::is_scalar(x_45)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_45;
 lean::cnstr_set_tag(x_45, 0);
}
lean::cnstr_set(x_65, 0, x_62);
return x_65;
}
else
{
obj* x_67; obj* x_70; obj* x_72; 
lean::dec(x_45);
x_67 = lean::cnstr_get(x_59, 0);
lean::inc(x_67);
lean::dec(x_59);
x_70 = lean::cnstr_get(x_67, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_67, 1);
lean::inc(x_72);
lean::dec(x_67);
x_0 = x_70;
x_1 = x_9;
x_3 = x_72;
goto _start;
}
}
else
{
obj* x_78; 
lean::dec(x_12);
lean::dec(x_45);
x_78 = lean::cnstr_get(x_50, 0);
lean::inc(x_78);
lean::dec(x_50);
x_0 = x_78;
x_1 = x_9;
goto _start;
}
}
}
}
}
obj* l_lean_elaborator_update__parser__config(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_6);
x_11 = l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(x_4, x_6, x_0, x_1);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_22 = x_11;
}
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 x_27 = x_20;
}
x_28 = lean::cnstr_get(x_1, 1);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_1, 4);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
lean::inc(x_28);
x_35 = l_list_append___rarg(x_28, x_32);
x_36 = l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(x_23, x_35, x_0, x_25);
if (lean::obj_tag(x_36) == 0)
{
obj* x_43; obj* x_46; 
lean::dec(x_27);
lean::dec(x_28);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_30);
x_43 = lean::cnstr_get(x_36, 0);
lean::inc(x_43);
lean::dec(x_36);
if (lean::is_scalar(x_22)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_22;
 lean::cnstr_set_tag(x_22, 0);
}
lean::cnstr_set(x_46, 0, x_43);
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_47 = lean::cnstr_get(x_36, 0);
lean::inc(x_47);
lean::dec(x_36);
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
lean::dec(x_47);
x_53 = lean::cnstr_get(x_1, 2);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_1, 3);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_1, 5);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_2, 1);
lean::inc(x_59);
lean::dec(x_2);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_50);
lean::cnstr_set(x_62, 1, x_59);
x_63 = lean::cnstr_get(x_1, 7);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_1, 8);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_1, 9);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_1, 10);
lean::inc(x_69);
lean::dec(x_1);
x_72 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_72, 0, x_6);
lean::cnstr_set(x_72, 1, x_28);
lean::cnstr_set(x_72, 2, x_53);
lean::cnstr_set(x_72, 3, x_55);
lean::cnstr_set(x_72, 4, x_30);
lean::cnstr_set(x_72, 5, x_57);
lean::cnstr_set(x_72, 6, x_62);
lean::cnstr_set(x_72, 7, x_63);
lean::cnstr_set(x_72, 8, x_65);
lean::cnstr_set(x_72, 9, x_67);
lean::cnstr_set(x_72, 10, x_69);
x_73 = lean::box(0);
if (lean::is_scalar(x_27)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_27;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_72);
if (lean::is_scalar(x_22)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_22;
}
lean::cnstr_set(x_75, 0, x_74);
return x_75;
}
}
}
}
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_2 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_2 = x_1;
}
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 4);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 6);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 7);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 8);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 9);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 10);
lean::inc(x_21);
lean::dec(x_0);
x_24 = l_lean_message__log_empty;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_26, 0, x_3);
lean::cnstr_set(x_26, 1, x_5);
lean::cnstr_set(x_26, 2, x_7);
lean::cnstr_set(x_26, 3, x_9);
lean::cnstr_set(x_26, 4, x_11);
lean::cnstr_set(x_26, 5, x_24);
lean::cnstr_set(x_26, 6, x_13);
lean::cnstr_set(x_26, 7, x_15);
lean::cnstr_set(x_26, 8, x_17);
lean::cnstr_set(x_26, 9, x_19);
lean::cnstr_set(x_26, 10, x_21);
x_27 = lean::box(0);
if (lean::is_scalar(x_2)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_2;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_30, 0, x_29);
return x_30;
}
}
obj* _init_l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pure___rarg), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
lean::inc(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__3), 2, 1);
lean::closure_set(x_7, 0, x_1);
x_8 = l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1;
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg___lambda__1), 2, 1);
lean::closure_set(x_11, 0, x_3);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___rarg___lambda__1), 2, 1);
lean::closure_set(x_14, 0, x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_15);
return x_16;
}
}
obj* _init_l_lean_elaborator_yield__to__outside___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___rarg___lambda__2), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_elaborator_yield__to__outside___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; 
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_lean_elaborator_yield__to__outside___rarg___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_5);
return x_7;
}
}
obj* l_lean_elaborator_yield__to__outside(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___rarg), 1, 0);
return x_4;
}
}
obj* _init_l_lean_elaborator_postprocess__notation__spec___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::mk_string(":");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = l_lean_parser_max__prec;
lean::inc(x_5);
x_7 = l_lean_parser_number_view_of__nat(x_5);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* l_lean_elaborator_postprocess__notation__spec(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
return x_0;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_9 = x_3;
}
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_14 = x_5;
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_10, 2);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_10, 3);
lean::inc(x_21);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 lean::cnstr_release(x_10, 3);
 x_23 = x_10;
}
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_0);
x_25 = l_lean_elaborator_postprocess__notation__spec___closed__1;
lean::inc(x_25);
if (lean::is_scalar(x_23)) {
 x_27 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_27 = x_23;
}
lean::cnstr_set(x_27, 0, x_15);
lean::cnstr_set(x_27, 1, x_17);
lean::cnstr_set(x_27, 2, x_19);
lean::cnstr_set(x_27, 3, x_25);
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_12);
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
else
{
lean::dec(x_15);
lean::dec(x_17);
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_12);
lean::dec(x_14);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_23);
return x_0;
}
}
}
else
{
lean::dec(x_1);
lean::dec(x_3);
return x_0;
}
}
}
obj* l_lean_elaborator_reserve__notation_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_40; obj* x_41; 
x_3 = l_lean_parser_command_reserve__notation_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
lean::dec(x_6);
x_14 = l_lean_elaborator_postprocess__notation__spec(x_11);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_9);
lean::cnstr_set(x_15, 2, x_14);
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::cnstr_get(x_2, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_2, 2);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 3);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 4);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_2, 5);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_2, 6);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_2, 7);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_2, 8);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_2, 9);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_2, 10);
lean::inc(x_37);
lean::dec(x_2);
x_40 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_40, 0, x_18);
lean::cnstr_set(x_40, 1, x_19);
lean::cnstr_set(x_40, 2, x_21);
lean::cnstr_set(x_40, 3, x_23);
lean::cnstr_set(x_40, 4, x_25);
lean::cnstr_set(x_40, 5, x_27);
lean::cnstr_set(x_40, 6, x_29);
lean::cnstr_set(x_40, 7, x_31);
lean::cnstr_set(x_40, 8, x_33);
lean::cnstr_set(x_40, 9, x_35);
lean::cnstr_set(x_40, 10, x_37);
x_41 = l_lean_elaborator_update__parser__config(x_1, x_40);
return x_41;
}
}
uint8 l_lean_elaborator_match__precedence___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_4; 
lean::dec(x_1);
x_4 = 1;
return x_4;
}
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
uint8 x_9; 
lean::dec(x_5);
x_9 = 0;
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_20; uint8 x_21; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_5, 1);
lean::inc(x_13);
lean::dec(x_5);
x_16 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_13);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
lean::dec(x_10);
x_20 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_17);
x_21 = lean::nat_dec_eq(x_16, x_20);
lean::dec(x_20);
lean::dec(x_16);
if (x_21 == 0)
{
uint8 x_24; 
x_24 = 0;
return x_24;
}
else
{
uint8 x_25; 
x_25 = 1;
return x_25;
}
}
}
}
}
obj* l_lean_elaborator_match__precedence___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_elaborator_match__precedence___main(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_elaborator_match__precedence(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_lean_elaborator_match__precedence___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_match__precedence___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_elaborator_match__precedence(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___lambda__1), 1, 0);
return x_0;
}
}
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_lean_parser_syntax_reprint__lst___main___closed__1;
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_19; 
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
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 3);
lean::inc(x_19);
lean::dec(x_15);
if (lean::obj_tag(x_17) == 0)
{
obj* x_27; 
lean::dec(x_19);
lean::dec(x_7);
lean::dec(x_10);
lean::dec(x_5);
lean::dec(x_12);
x_27 = lean::box(0);
return x_27;
}
else
{
obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; 
x_28 = lean::cnstr_get(x_17, 0);
lean::inc(x_28);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_30 = x_17;
}
x_31 = lean::cnstr_get(x_12, 0);
lean::inc(x_31);
x_37 = lean::cnstr_get(x_31, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_31, 3);
lean::inc(x_39);
if (lean::obj_tag(x_37) == 0)
{
obj* x_48; 
lean::dec(x_19);
lean::dec(x_10);
lean::dec(x_28);
lean::dec(x_30);
lean::dec(x_12);
lean::dec(x_39);
lean::dec(x_31);
x_48 = lean::box(0);
x_8 = x_48;
goto lbl_9;
}
else
{
obj* x_49; obj* x_52; obj* x_55; obj* x_56; obj* x_59; uint8 x_60; 
x_49 = lean::cnstr_get(x_37, 0);
lean::inc(x_49);
lean::dec(x_37);
x_52 = lean::cnstr_get(x_28, 1);
lean::inc(x_52);
lean::dec(x_28);
x_55 = l_string_trim(x_52);
x_56 = lean::cnstr_get(x_49, 1);
lean::inc(x_56);
lean::dec(x_49);
x_59 = l_string_trim(x_56);
x_60 = lean::string_dec_eq(x_55, x_59);
lean::dec(x_59);
lean::dec(x_55);
if (x_60 == 0)
{
obj* x_69; 
lean::dec(x_19);
lean::dec(x_10);
lean::dec(x_30);
lean::dec(x_12);
lean::dec(x_39);
lean::dec(x_31);
x_69 = lean::box(0);
x_8 = x_69;
goto lbl_9;
}
else
{
uint8 x_70; 
x_70 = l_lean_elaborator_match__precedence___main(x_19, x_39);
if (x_70 == 0)
{
obj* x_75; 
lean::dec(x_10);
lean::dec(x_30);
lean::dec(x_12);
lean::dec(x_31);
x_75 = lean::box(0);
x_8 = x_75;
goto lbl_9;
}
else
{
obj* x_76; 
x_76 = lean::box(0);
x_35 = x_76;
goto lbl_36;
}
}
}
lbl_34:
{
if (lean::obj_tag(x_33) == 0)
{
obj* x_79; 
lean::dec(x_30);
lean::dec(x_31);
x_79 = lean::box(0);
x_8 = x_79;
goto lbl_9;
}
else
{
obj* x_80; obj* x_83; obj* x_84; 
x_80 = lean::cnstr_get(x_33, 0);
lean::inc(x_80);
lean::dec(x_33);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_31);
lean::cnstr_set(x_83, 1, x_80);
if (lean::is_scalar(x_30)) {
 x_84 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_84 = x_30;
}
lean::cnstr_set(x_84, 0, x_83);
x_8 = x_84;
goto lbl_9;
}
}
lbl_36:
{
obj* x_86; 
lean::dec(x_35);
x_86 = lean::cnstr_get(x_10, 1);
lean::inc(x_86);
lean::dec(x_10);
if (lean::obj_tag(x_86) == 0)
{
obj* x_89; 
x_89 = lean::cnstr_get(x_12, 1);
lean::inc(x_89);
lean::dec(x_12);
if (lean::obj_tag(x_89) == 0)
{
obj* x_92; 
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_89);
x_33 = x_92;
goto lbl_34;
}
else
{
obj* x_94; 
lean::dec(x_89);
x_94 = lean::box(0);
x_33 = x_94;
goto lbl_34;
}
}
else
{
obj* x_95; obj* x_97; 
x_95 = lean::cnstr_get(x_86, 0);
lean::inc(x_95);
if (lean::is_shared(x_86)) {
 lean::dec(x_86);
 x_97 = lean::box(0);
} else {
 lean::cnstr_release(x_86, 0);
 x_97 = x_86;
}
switch (lean::obj_tag(x_95)) {
case 0:
{
obj* x_98; obj* x_101; 
x_98 = lean::cnstr_get(x_95, 0);
lean::inc(x_98);
lean::dec(x_95);
x_101 = lean::cnstr_get(x_12, 1);
lean::inc(x_101);
lean::dec(x_12);
if (lean::obj_tag(x_101) == 0)
{
obj* x_106; 
lean::dec(x_97);
lean::dec(x_98);
x_106 = lean::box(0);
x_33 = x_106;
goto lbl_34;
}
else
{
obj* x_107; 
x_107 = lean::cnstr_get(x_101, 0);
lean::inc(x_107);
switch (lean::obj_tag(x_107)) {
case 0:
{
obj* x_109; obj* x_112; obj* x_115; uint8 x_118; 
x_109 = lean::cnstr_get(x_107, 0);
lean::inc(x_109);
lean::dec(x_107);
x_112 = lean::cnstr_get(x_98, 1);
lean::inc(x_112);
lean::dec(x_98);
x_115 = lean::cnstr_get(x_109, 1);
lean::inc(x_115);
lean::dec(x_109);
x_118 = l_lean_elaborator_match__precedence___main(x_112, x_115);
if (x_118 == 0)
{
obj* x_121; 
lean::dec(x_97);
lean::dec(x_101);
x_121 = lean::box(0);
x_33 = x_121;
goto lbl_34;
}
else
{
obj* x_122; 
if (lean::is_scalar(x_97)) {
 x_122 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_122 = x_97;
}
lean::cnstr_set(x_122, 0, x_101);
x_33 = x_122;
goto lbl_34;
}
}
default:
{
obj* x_127; 
lean::dec(x_97);
lean::dec(x_101);
lean::dec(x_98);
lean::dec(x_107);
x_127 = lean::box(0);
x_33 = x_127;
goto lbl_34;
}
}
}
}
case 1:
{
obj* x_128; obj* x_131; 
x_128 = lean::cnstr_get(x_95, 0);
lean::inc(x_128);
lean::dec(x_95);
x_131 = lean::cnstr_get(x_12, 1);
lean::inc(x_131);
lean::dec(x_12);
if (lean::obj_tag(x_131) == 0)
{
obj* x_136; 
lean::dec(x_97);
lean::dec(x_128);
x_136 = lean::box(0);
x_33 = x_136;
goto lbl_34;
}
else
{
obj* x_137; 
x_137 = lean::cnstr_get(x_131, 0);
lean::inc(x_137);
switch (lean::obj_tag(x_137)) {
case 1:
{
obj* x_139; obj* x_142; obj* x_145; uint8 x_148; 
x_139 = lean::cnstr_get(x_137, 0);
lean::inc(x_139);
lean::dec(x_137);
x_142 = lean::cnstr_get(x_128, 1);
lean::inc(x_142);
lean::dec(x_128);
x_145 = lean::cnstr_get(x_139, 1);
lean::inc(x_145);
lean::dec(x_139);
x_148 = l_lean_elaborator_match__precedence___main(x_142, x_145);
if (x_148 == 0)
{
obj* x_151; 
lean::dec(x_97);
lean::dec(x_131);
x_151 = lean::box(0);
x_33 = x_151;
goto lbl_34;
}
else
{
obj* x_152; 
if (lean::is_scalar(x_97)) {
 x_152 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_152 = x_97;
}
lean::cnstr_set(x_152, 0, x_131);
x_33 = x_152;
goto lbl_34;
}
}
default:
{
obj* x_157; 
lean::dec(x_97);
lean::dec(x_131);
lean::dec(x_128);
lean::dec(x_137);
x_157 = lean::box(0);
x_33 = x_157;
goto lbl_34;
}
}
}
}
default:
{
obj* x_158; obj* x_160; obj* x_161; obj* x_163; 
x_158 = lean::cnstr_get(x_95, 0);
lean::inc(x_158);
if (lean::is_shared(x_95)) {
 lean::dec(x_95);
 x_160 = lean::box(0);
} else {
 lean::cnstr_release(x_95, 0);
 x_160 = x_95;
}
x_163 = lean::cnstr_get(x_12, 1);
lean::inc(x_163);
lean::dec(x_12);
if (lean::obj_tag(x_163) == 0)
{
obj* x_169; 
lean::dec(x_97);
lean::dec(x_158);
lean::dec(x_160);
x_169 = lean::box(0);
x_33 = x_169;
goto lbl_34;
}
else
{
obj* x_170; obj* x_172; 
x_170 = lean::cnstr_get(x_163, 0);
lean::inc(x_170);
if (lean::is_shared(x_163)) {
 lean::dec(x_163);
 x_172 = lean::box(0);
} else {
 lean::cnstr_release(x_163, 0);
 x_172 = x_163;
}
switch (lean::obj_tag(x_170)) {
case 2:
{
obj* x_173; obj* x_176; obj* x_178; obj* x_181; 
x_173 = lean::cnstr_get(x_170, 0);
lean::inc(x_173);
lean::dec(x_170);
x_176 = lean::cnstr_get(x_158, 1);
lean::inc(x_176);
x_178 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1;
lean::inc(x_176);
lean::inc(x_178);
x_181 = l_option_map___rarg(x_178, x_176);
if (lean::obj_tag(x_181) == 0)
{
obj* x_183; obj* x_188; 
lean::dec(x_176);
x_183 = lean::cnstr_get(x_173, 1);
lean::inc(x_183);
lean::dec(x_173);
lean::inc(x_183);
lean::inc(x_178);
x_188 = l_option_map___rarg(x_178, x_183);
if (lean::obj_tag(x_188) == 0)
{
obj* x_191; 
lean::dec(x_183);
lean::dec(x_172);
x_191 = lean::box(0);
x_161 = x_191;
goto lbl_162;
}
else
{
obj* x_192; 
x_192 = lean::cnstr_get(x_188, 0);
lean::inc(x_192);
lean::dec(x_188);
switch (lean::obj_tag(x_192)) {
case 0:
{
obj* x_196; 
lean::dec(x_192);
if (lean::is_scalar(x_172)) {
 x_196 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_196 = x_172;
}
lean::cnstr_set(x_196, 0, x_183);
x_161 = x_196;
goto lbl_162;
}
default:
{
obj* x_200; 
lean::dec(x_192);
lean::dec(x_183);
lean::dec(x_172);
x_200 = lean::box(0);
x_161 = x_200;
goto lbl_162;
}
}
}
}
else
{
obj* x_201; 
x_201 = lean::cnstr_get(x_181, 0);
lean::inc(x_201);
lean::dec(x_181);
switch (lean::obj_tag(x_201)) {
case 0:
{
obj* x_204; obj* x_207; obj* x_211; 
x_204 = lean::cnstr_get(x_201, 0);
lean::inc(x_204);
lean::dec(x_201);
x_207 = lean::cnstr_get(x_173, 1);
lean::inc(x_207);
lean::dec(x_173);
lean::inc(x_178);
x_211 = l_option_map___rarg(x_178, x_207);
if (lean::obj_tag(x_211) == 0)
{
obj* x_215; 
lean::dec(x_204);
lean::dec(x_176);
lean::dec(x_172);
x_215 = lean::box(0);
x_161 = x_215;
goto lbl_162;
}
else
{
obj* x_216; 
x_216 = lean::cnstr_get(x_211, 0);
lean::inc(x_216);
lean::dec(x_211);
switch (lean::obj_tag(x_216)) {
case 0:
{
obj* x_219; obj* x_222; obj* x_223; uint8 x_224; 
x_219 = lean::cnstr_get(x_216, 0);
lean::inc(x_219);
lean::dec(x_216);
x_222 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_204);
x_223 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_219);
x_224 = lean::nat_dec_eq(x_222, x_223);
lean::dec(x_223);
lean::dec(x_222);
if (x_224 == 0)
{
obj* x_229; 
lean::dec(x_176);
lean::dec(x_172);
x_229 = lean::box(0);
x_161 = x_229;
goto lbl_162;
}
else
{
obj* x_230; 
if (lean::is_scalar(x_172)) {
 x_230 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_230 = x_172;
}
lean::cnstr_set(x_230, 0, x_176);
x_161 = x_230;
goto lbl_162;
}
}
default:
{
obj* x_235; 
lean::dec(x_204);
lean::dec(x_216);
lean::dec(x_176);
lean::dec(x_172);
x_235 = lean::box(0);
x_161 = x_235;
goto lbl_162;
}
}
}
}
default:
{
obj* x_240; 
lean::dec(x_201);
lean::dec(x_176);
lean::dec(x_173);
lean::dec(x_172);
x_240 = lean::box(0);
x_161 = x_240;
goto lbl_162;
}
}
}
}
default:
{
obj* x_246; 
lean::dec(x_97);
lean::dec(x_170);
lean::dec(x_172);
lean::dec(x_158);
lean::dec(x_160);
x_246 = lean::box(0);
x_33 = x_246;
goto lbl_34;
}
}
}
lbl_162:
{
if (lean::obj_tag(x_161) == 0)
{
obj* x_250; 
lean::dec(x_97);
lean::dec(x_158);
lean::dec(x_160);
x_250 = lean::box(0);
x_33 = x_250;
goto lbl_34;
}
else
{
obj* x_251; obj* x_253; obj* x_254; obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
x_251 = lean::cnstr_get(x_161, 0);
lean::inc(x_251);
if (lean::is_shared(x_161)) {
 lean::dec(x_161);
 x_253 = lean::box(0);
} else {
 lean::cnstr_release(x_161, 0);
 x_253 = x_161;
}
x_254 = lean::cnstr_get(x_158, 0);
lean::inc(x_254);
lean::dec(x_158);
x_257 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_257, 0, x_254);
lean::cnstr_set(x_257, 1, x_251);
if (lean::is_scalar(x_160)) {
 x_258 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_258 = x_160;
}
lean::cnstr_set(x_258, 0, x_257);
if (lean::is_scalar(x_97)) {
 x_259 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_259 = x_97;
}
lean::cnstr_set(x_259, 0, x_258);
if (lean::is_scalar(x_253)) {
 x_260 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_260 = x_253;
}
lean::cnstr_set(x_260, 0, x_259);
x_33 = x_260;
goto lbl_34;
}
}
}
}
}
}
}
lbl_9:
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_263; 
lean::dec(x_7);
lean::dec(x_5);
x_263 = lean::box(0);
return x_263;
}
else
{
obj* x_264; obj* x_266; obj* x_267; 
x_264 = lean::cnstr_get(x_8, 0);
lean::inc(x_264);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_266 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_266 = x_8;
}
x_267 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(x_5);
if (lean::obj_tag(x_267) == 0)
{
obj* x_271; 
lean::dec(x_7);
lean::dec(x_266);
lean::dec(x_264);
x_271 = lean::box(0);
return x_271;
}
else
{
obj* x_272; obj* x_275; obj* x_276; 
x_272 = lean::cnstr_get(x_267, 0);
lean::inc(x_272);
lean::dec(x_267);
if (lean::is_scalar(x_7)) {
 x_275 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_275 = x_7;
}
lean::cnstr_set(x_275, 0, x_264);
lean::cnstr_set(x_275, 1, x_272);
if (lean::is_scalar(x_266)) {
 x_276 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_276 = x_266;
}
lean::cnstr_set(x_276, 0, x_275);
return x_276;
}
}
}
}
}
}
obj* _init_l_lean_elaborator_match__spec___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg___lambda__1), 2, 0);
return x_0;
}
}
obj* l_lean_elaborator_match__spec(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; uint8 x_7; obj* x_8; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::inc(x_2);
x_7 = l_option_is__some___main___rarg(x_2);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = l_option_is__some___main___rarg(x_8);
if (x_7 == 0)
{
if (x_10 == 0)
{
obj* x_11; 
x_11 = lean::box(0);
x_4 = x_11;
goto lbl_5;
}
else
{
obj* x_15; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_15 = lean::box(0);
return x_15;
}
}
else
{
if (x_10 == 0)
{
obj* x_19; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_19 = lean::box(0);
return x_19;
}
else
{
obj* x_20; 
x_20 = lean::box(0);
x_4 = x_20;
goto lbl_5;
}
}
lbl_5:
{
obj* x_22; obj* x_25; obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_4);
x_22 = lean::cnstr_get(x_0, 1);
lean::inc(x_22);
lean::dec(x_0);
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
lean::dec(x_1);
x_28 = l_lean_elaborator_match__spec___closed__1;
lean::inc(x_28);
x_30 = l_list_zip__with___main___rarg(x_28, x_22, x_25);
x_31 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_2);
x_33 = lean::box(0);
return x_33;
}
else
{
obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 x_36 = x_31;
}
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_2);
lean::cnstr_set(x_37, 1, x_34);
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
}
}
}
obj* l_lean_elaborator_notation_elaborate__aux___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 2);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_lean_elaborator_match__spec(x_2, x_5);
return x_8;
}
}
obj* _init_l_lean_elaborator_notation_elaborate__aux___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid notation, matches multiple reserved notations");
return x_0;
}
}
obj* l_lean_elaborator_notation_elaborate__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_notation_elaborate__aux___lambda__1), 2, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = l_list_filter__map___main___rarg(x_4, x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_1);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 2);
lean::inc(x_13);
x_15 = l_lean_elaborator_postprocess__notation__spec(x_13);
x_16 = lean::cnstr_get(x_0, 3);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 4);
lean::inc(x_18);
lean::dec(x_0);
x_21 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_11);
lean::cnstr_set(x_21, 2, x_15);
lean::cnstr_set(x_21, 3, x_16);
lean::cnstr_set(x_21, 4, x_18);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
else
{
obj* x_24; obj* x_26; 
x_24 = lean::cnstr_get(x_7, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_7, 1);
lean::inc(x_26);
lean::dec(x_7);
if (lean::obj_tag(x_26) == 0)
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_1);
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 3);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 4);
lean::inc(x_36);
lean::dec(x_0);
x_39 = l_lean_elaborator_postprocess__notation__spec(x_24);
x_40 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_40, 0, x_30);
lean::cnstr_set(x_40, 1, x_32);
lean::cnstr_set(x_40, 2, x_39);
lean::cnstr_set(x_40, 3, x_34);
lean::cnstr_set(x_40, 4, x_36);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_2);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
else
{
obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_51; 
lean::dec(x_24);
lean::dec(x_26);
x_45 = l_lean_parser_command_notation_has__view;
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
x_48 = lean::apply_1(x_46, x_0);
x_49 = l_lean_elaborator_notation_elaborate__aux___closed__1;
lean::inc(x_49);
x_51 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_48, x_49, x_1, x_2);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
if (lean::is_shared(x_51)) {
 lean::dec(x_51);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_51, 0);
 x_54 = x_51;
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
obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_76; obj* x_77; obj* x_78; 
x_56 = lean::cnstr_get(x_51, 0);
lean::inc(x_56);
if (lean::is_shared(x_51)) {
 lean::dec(x_51);
 x_58 = lean::box(0);
} else {
 lean::cnstr_release(x_51, 0);
 x_58 = x_51;
}
x_59 = lean::cnstr_get(x_56, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_56, 1);
lean::inc(x_61);
if (lean::is_shared(x_56)) {
 lean::dec(x_56);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_63 = x_56;
}
x_64 = lean::cnstr_get(x_59, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_59, 1);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_59, 2);
lean::inc(x_68);
x_70 = l_lean_elaborator_postprocess__notation__spec(x_68);
x_71 = lean::cnstr_get(x_59, 3);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_59, 4);
lean::inc(x_73);
lean::dec(x_59);
x_76 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_76, 0, x_64);
lean::cnstr_set(x_76, 1, x_66);
lean::cnstr_set(x_76, 2, x_70);
lean::cnstr_set(x_76, 3, x_71);
lean::cnstr_set(x_76, 4, x_73);
if (lean::is_scalar(x_63)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_63;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_61);
if (lean::is_scalar(x_58)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_58;
}
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
}
}
}
}
obj* _init_l_lean_elaborator_mk__notation__kind___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_notation");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_mk__notation__kind___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_5, x_7);
lean::dec(x_7);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 4);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 5);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 6);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 7);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 8);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_0, 9);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_0, 10);
lean::inc(x_24);
lean::dec(x_0);
x_27 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_27, 0, x_1);
lean::cnstr_set(x_27, 1, x_3);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_10);
lean::cnstr_set(x_27, 4, x_12);
lean::cnstr_set(x_27, 5, x_14);
lean::cnstr_set(x_27, 6, x_16);
lean::cnstr_set(x_27, 7, x_18);
lean::cnstr_set(x_27, 8, x_20);
lean::cnstr_set(x_27, 9, x_22);
lean::cnstr_set(x_27, 10, x_24);
x_28 = l_lean_elaborator_mk__notation__kind___rarg___closed__1;
lean::inc(x_28);
x_30 = lean_name_mk_numeral(x_28, x_5);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_27);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
}
obj* l_lean_elaborator_mk__notation__kind(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_mk__notation__kind___rarg), 1, 0);
return x_2;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_elaborator_register__notation__macro(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = l_lean_elaborator_mk__notation__kind___rarg(x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_0);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_8 = x_4;
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_54; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_12 = x_4;
}
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_17 = x_10;
}
lean::inc(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_13);
lean::cnstr_set(x_19, 1, x_0);
lean::inc(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mk__notation__transformer), 3, 1);
lean::closure_set(x_21, 0, x_19);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_15, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_15, 2);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_15, 3);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_15, 4);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_15, 5);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_15, 6);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_15, 7);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_36, 1);
lean::inc(x_40);
lean::dec(x_36);
x_43 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_40, x_13, x_21);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_38);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::cnstr_get(x_15, 8);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_15, 9);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_15, 10);
lean::inc(x_49);
lean::dec(x_15);
x_52 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_52, 0, x_22);
lean::cnstr_set(x_52, 1, x_24);
lean::cnstr_set(x_52, 2, x_26);
lean::cnstr_set(x_52, 3, x_28);
lean::cnstr_set(x_52, 4, x_30);
lean::cnstr_set(x_52, 5, x_32);
lean::cnstr_set(x_52, 6, x_34);
lean::cnstr_set(x_52, 7, x_44);
lean::cnstr_set(x_52, 8, x_45);
lean::cnstr_set(x_52, 9, x_47);
lean::cnstr_set(x_52, 10, x_49);
if (lean::is_scalar(x_17)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_17;
}
lean::cnstr_set(x_53, 0, x_19);
lean::cnstr_set(x_53, 1, x_52);
if (lean::is_scalar(x_12)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_12;
}
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
}
uint8 l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
obj* x_2; obj* x_4; uint8 x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_4);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
if (lean::obj_tag(x_8) == 0)
{
return x_7;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
switch (lean::obj_tag(x_11)) {
case 2:
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
if (lean::obj_tag(x_17) == 0)
{
return x_7;
}
else
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
switch (lean::obj_tag(x_23)) {
case 3:
{
uint8 x_27; 
lean::dec(x_23);
x_27 = 1;
return x_27;
}
default:
{
lean::dec(x_23);
return x_7;
}
}
}
}
default:
{
lean::dec(x_11);
return x_7;
}
}
}
}
}
}
obj* _init_l_lean_elaborator_notation_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_notation_elaborate___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ignoring notation using 'fold' action");
return x_0;
}
}
obj* l_lean_elaborator_notation_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; uint8 x_14; 
x_3 = l_lean_parser_command_notation_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_9 = lean::cnstr_get(x_6, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_14 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_11);
if (x_14 == 0)
{
obj* x_15; 
x_15 = lean::box(0);
x_7 = x_15;
goto lbl_8;
}
else
{
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_34; uint8 x_35; obj* x_36; obj* x_37; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_6);
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_2, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_2, 2);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 3);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 4);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
lean::dec(x_1);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
lean::dec(x_27);
x_33 = lean::box(0);
x_34 = l_lean_elaborator_notation_elaborate___closed__1;
x_35 = 1;
x_36 = l_string_join___closed__1;
x_37 = l_lean_elaborator_notation_elaborate___closed__2;
lean::inc(x_37);
lean::inc(x_36);
lean::inc(x_33);
lean::inc(x_34);
x_42 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_42, 0, x_30);
lean::cnstr_set(x_42, 1, x_34);
lean::cnstr_set(x_42, 2, x_33);
lean::cnstr_set(x_42, 3, x_36);
lean::cnstr_set(x_42, 4, x_37);
lean::cnstr_set_scalar(x_42, sizeof(void*)*5, x_35);
x_43 = x_42;
x_44 = lean::cnstr_get(x_2, 5);
lean::inc(x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_44);
x_47 = lean::cnstr_get(x_2, 6);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_2, 7);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_2, 8);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_2, 9);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_2, 10);
lean::inc(x_55);
lean::dec(x_2);
x_58 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_58, 0, x_17);
lean::cnstr_set(x_58, 1, x_19);
lean::cnstr_set(x_58, 2, x_21);
lean::cnstr_set(x_58, 3, x_23);
lean::cnstr_set(x_58, 4, x_25);
lean::cnstr_set(x_58, 5, x_46);
lean::cnstr_set(x_58, 6, x_47);
lean::cnstr_set(x_58, 7, x_49);
lean::cnstr_set(x_58, 8, x_51);
lean::cnstr_set(x_58, 9, x_53);
lean::cnstr_set(x_58, 10, x_55);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_33);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
lbl_8:
{
obj* x_63; 
lean::dec(x_7);
lean::inc(x_1);
x_63 = l_lean_elaborator_notation_elaborate__aux(x_6, x_1, x_2);
if (lean::obj_tag(x_63) == 0)
{
obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_1);
x_65 = lean::cnstr_get(x_63, 0);
lean::inc(x_65);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_67 = x_63;
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_65);
return x_68;
}
else
{
obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_79; 
x_69 = lean::cnstr_get(x_63, 0);
lean::inc(x_69);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_71 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_71 = x_63;
}
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
lean::inc(x_1);
lean::inc(x_72);
x_79 = l_lean_elaborator_register__notation__macro(x_72, x_1, x_74);
if (lean::obj_tag(x_79) == 0)
{
obj* x_82; obj* x_85; 
lean::dec(x_1);
lean::dec(x_72);
x_82 = lean::cnstr_get(x_79, 0);
lean::inc(x_82);
lean::dec(x_79);
if (lean::is_scalar(x_71)) {
 x_85 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_85 = x_71;
 lean::cnstr_set_tag(x_71, 0);
}
lean::cnstr_set(x_85, 0, x_82);
return x_85;
}
else
{
obj* x_87; obj* x_90; obj* x_92; obj* x_95; 
lean::dec(x_71);
x_87 = lean::cnstr_get(x_79, 0);
lean::inc(x_87);
lean::dec(x_79);
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_87, 1);
lean::inc(x_92);
lean::dec(x_87);
x_95 = lean::cnstr_get(x_72, 0);
lean::inc(x_95);
lean::dec(x_72);
if (lean::obj_tag(x_95) == 0)
{
obj* x_98; obj* x_100; obj* x_102; obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_122; obj* x_123; 
x_98 = lean::cnstr_get(x_92, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_92, 1);
lean::inc(x_100);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_90);
lean::cnstr_set(x_102, 1, x_100);
x_103 = lean::cnstr_get(x_92, 2);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_92, 3);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_92, 4);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_92, 5);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_92, 6);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_92, 7);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_92, 8);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_92, 9);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_92, 10);
lean::inc(x_119);
lean::dec(x_92);
x_122 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_122, 0, x_98);
lean::cnstr_set(x_122, 1, x_102);
lean::cnstr_set(x_122, 2, x_103);
lean::cnstr_set(x_122, 3, x_105);
lean::cnstr_set(x_122, 4, x_107);
lean::cnstr_set(x_122, 5, x_109);
lean::cnstr_set(x_122, 6, x_111);
lean::cnstr_set(x_122, 7, x_113);
lean::cnstr_set(x_122, 8, x_115);
lean::cnstr_set(x_122, 9, x_117);
lean::cnstr_set(x_122, 10, x_119);
x_123 = l_lean_elaborator_update__parser__config(x_1, x_122);
return x_123;
}
else
{
obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_140; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_151; obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_160; obj* x_162; obj* x_165; obj* x_166; 
lean::dec(x_95);
x_125 = lean::cnstr_get(x_92, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_92, 1);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_92, 2);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_92, 3);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_92, 4);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_133, 0);
lean::inc(x_135);
x_137 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_137, 0, x_90);
lean::cnstr_set(x_137, 1, x_135);
x_138 = lean::cnstr_get(x_133, 1);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_133, 2);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_133, 3);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_133, 4);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_133, 5);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_133, 6);
lean::inc(x_148);
lean::dec(x_133);
x_151 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_151, 0, x_137);
lean::cnstr_set(x_151, 1, x_138);
lean::cnstr_set(x_151, 2, x_140);
lean::cnstr_set(x_151, 3, x_142);
lean::cnstr_set(x_151, 4, x_144);
lean::cnstr_set(x_151, 5, x_146);
lean::cnstr_set(x_151, 6, x_148);
x_152 = lean::cnstr_get(x_92, 5);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_92, 6);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_92, 7);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_92, 8);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_92, 9);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_92, 10);
lean::inc(x_162);
lean::dec(x_92);
x_165 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_165, 0, x_125);
lean::cnstr_set(x_165, 1, x_127);
lean::cnstr_set(x_165, 2, x_129);
lean::cnstr_set(x_165, 3, x_131);
lean::cnstr_set(x_165, 4, x_151);
lean::cnstr_set(x_165, 5, x_152);
lean::cnstr_set(x_165, 6, x_154);
lean::cnstr_set(x_165, 7, x_156);
lean::cnstr_set(x_165, 8, x_158);
lean::cnstr_set(x_165, 9, x_160);
lean::cnstr_set(x_165, 10, x_162);
x_166 = l_lean_elaborator_update__parser__config(x_1, x_165);
return x_166;
}
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_universe_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("a universe named '");
return x_0;
}
}
obj* _init_l_lean_elaborator_universe_elaborate___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("' has already been declared in this scope");
return x_0;
}
}
obj* l_lean_elaborator_universe_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_14; obj* x_18; 
x_3 = l_lean_parser_command_universe_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::inc(x_0);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = l_lean_elaborator_mangle__ident(x_8);
x_12 = lean::cnstr_get(x_2, 4);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 1);
lean::inc(x_14);
lean::inc(x_11);
lean::inc(x_14);
x_18 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_14, x_11);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_1);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 2);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_2, 3);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_12, 0);
lean::inc(x_29);
lean::inc(x_11);
x_32 = level_mk_param(x_11);
x_33 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_14, x_11, x_32);
x_34 = lean::cnstr_get(x_12, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_12, 3);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_12, 4);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_12, 5);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_12, 6);
lean::inc(x_42);
lean::dec(x_12);
x_45 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_45, 0, x_29);
lean::cnstr_set(x_45, 1, x_33);
lean::cnstr_set(x_45, 2, x_34);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set(x_45, 4, x_38);
lean::cnstr_set(x_45, 5, x_40);
lean::cnstr_set(x_45, 6, x_42);
x_46 = lean::cnstr_get(x_2, 5);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_2, 6);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_2, 7);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_2, 8);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_2, 9);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_2, 10);
lean::inc(x_56);
lean::dec(x_2);
x_59 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_59, 0, x_21);
lean::cnstr_set(x_59, 1, x_23);
lean::cnstr_set(x_59, 2, x_25);
lean::cnstr_set(x_59, 3, x_27);
lean::cnstr_set(x_59, 4, x_45);
lean::cnstr_set(x_59, 5, x_46);
lean::cnstr_set(x_59, 6, x_48);
lean::cnstr_set(x_59, 7, x_50);
lean::cnstr_set(x_59, 8, x_52);
lean::cnstr_set(x_59, 9, x_54);
lean::cnstr_set(x_59, 10, x_56);
x_60 = lean::box(0);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_59);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_61);
return x_62;
}
else
{
obj* x_66; obj* x_68; obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_18);
x_66 = l_lean_name_to__string___closed__1;
lean::inc(x_66);
x_68 = l_lean_name_to__string__with__sep___main(x_66, x_11);
x_69 = l_lean_elaborator_universe_elaborate___closed__1;
lean::inc(x_69);
x_71 = lean::string_append(x_69, x_68);
lean::dec(x_68);
x_73 = l_lean_elaborator_universe_elaborate___closed__2;
x_74 = lean::string_append(x_71, x_73);
x_75 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_74, x_1, x_2);
return x_75;
}
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown identifier '");
return x_0;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid 'attribute' command, identifier is ambiguous");
return x_0;
}
}
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
x_12 = lean::cnstr_get(x_7, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_16; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; 
lean::inc(x_7);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_7);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
lean::dec(x_7);
x_19 = l_lean_name_to__string___closed__1;
lean::inc(x_19);
x_21 = l_lean_name_to__string__with__sep___main(x_19, x_16);
x_22 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1;
lean::inc(x_22);
x_24 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_26 = l_char_has__repr___closed__1;
x_27 = lean::string_append(x_24, x_26);
lean::inc(x_1);
x_29 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_15, x_27, x_1, x_2);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
if (lean::is_shared(x_29)) {
 lean::dec(x_29);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_29, 0);
 x_35 = x_29;
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
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; 
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
if (lean::is_shared(x_29)) {
 lean::dec(x_29);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_29, 0);
 x_39 = x_29;
}
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
if (lean::is_shared(x_37)) {
 lean::dec(x_37);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 x_44 = x_37;
}
x_45 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_9, x_1, x_42);
if (lean::obj_tag(x_45) == 0)
{
obj* x_49; obj* x_52; 
lean::dec(x_11);
lean::dec(x_40);
lean::dec(x_44);
x_49 = lean::cnstr_get(x_45, 0);
lean::inc(x_49);
lean::dec(x_45);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_39;
 lean::cnstr_set_tag(x_39, 0);
}
lean::cnstr_set(x_52, 0, x_49);
return x_52;
}
else
{
obj* x_53; obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_63; 
x_53 = lean::cnstr_get(x_45, 0);
lean::inc(x_53);
lean::dec(x_45);
x_56 = lean::cnstr_get(x_53, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_53, 1);
lean::inc(x_58);
lean::dec(x_53);
if (lean::is_scalar(x_11)) {
 x_61 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_61 = x_11;
}
lean::cnstr_set(x_61, 0, x_40);
lean::cnstr_set(x_61, 1, x_56);
if (lean::is_scalar(x_44)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_44;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_58);
if (lean::is_scalar(x_39)) {
 x_63 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_63 = x_39;
}
lean::cnstr_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
obj* x_64; obj* x_66; 
x_64 = lean::cnstr_get(x_12, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_12, 1);
lean::inc(x_66);
lean::dec(x_12);
if (lean::obj_tag(x_66) == 0)
{
obj* x_70; 
lean::dec(x_7);
x_70 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_9, x_1, x_2);
if (lean::obj_tag(x_70) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_11);
lean::dec(x_64);
x_73 = lean::cnstr_get(x_70, 0);
lean::inc(x_73);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_75 = x_70;
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
return x_76;
}
else
{
obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_77 = lean::cnstr_get(x_70, 0);
lean::inc(x_77);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_79 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_79 = x_70;
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
}
x_85 = lean::box(0);
x_86 = lean_expr_mk_const(x_64, x_85);
if (lean::is_scalar(x_11)) {
 x_87 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_87 = x_11;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_80);
if (lean::is_scalar(x_84)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_84;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_82);
if (lean::is_scalar(x_79)) {
 x_89 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_89 = x_79;
}
lean::cnstr_set(x_89, 0, x_88);
return x_89;
}
}
else
{
obj* x_92; obj* x_93; obj* x_96; 
lean::dec(x_64);
lean::dec(x_66);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_7);
x_93 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
lean::inc(x_1);
lean::inc(x_93);
x_96 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_92, x_93, x_1, x_2);
if (lean::obj_tag(x_96) == 0)
{
obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_100 = lean::cnstr_get(x_96, 0);
lean::inc(x_100);
if (lean::is_shared(x_96)) {
 lean::dec(x_96);
 x_102 = lean::box(0);
} else {
 lean::cnstr_release(x_96, 0);
 x_102 = x_96;
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
return x_103;
}
else
{
obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_112; 
x_104 = lean::cnstr_get(x_96, 0);
lean::inc(x_104);
if (lean::is_shared(x_96)) {
 lean::dec(x_96);
 x_106 = lean::box(0);
} else {
 lean::cnstr_release(x_96, 0);
 x_106 = x_96;
}
x_107 = lean::cnstr_get(x_104, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_104, 1);
lean::inc(x_109);
if (lean::is_shared(x_104)) {
 lean::dec(x_104);
 x_111 = lean::box(0);
} else {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_111 = x_104;
}
x_112 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_9, x_1, x_109);
if (lean::obj_tag(x_112) == 0)
{
obj* x_116; obj* x_119; 
lean::dec(x_11);
lean::dec(x_111);
lean::dec(x_107);
x_116 = lean::cnstr_get(x_112, 0);
lean::inc(x_116);
lean::dec(x_112);
if (lean::is_scalar(x_106)) {
 x_119 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_119 = x_106;
 lean::cnstr_set_tag(x_106, 0);
}
lean::cnstr_set(x_119, 0, x_116);
return x_119;
}
else
{
obj* x_120; obj* x_123; obj* x_125; obj* x_128; obj* x_129; obj* x_130; 
x_120 = lean::cnstr_get(x_112, 0);
lean::inc(x_120);
lean::dec(x_112);
x_123 = lean::cnstr_get(x_120, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_120, 1);
lean::inc(x_125);
lean::dec(x_120);
if (lean::is_scalar(x_11)) {
 x_128 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_128 = x_11;
}
lean::cnstr_set(x_128, 0, x_107);
lean::cnstr_set(x_128, 1, x_123);
if (lean::is_scalar(x_111)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_111;
}
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_125);
if (lean::is_scalar(x_106)) {
 x_130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_130 = x_106;
}
lean::cnstr_set(x_130, 0, x_129);
return x_130;
}
}
}
}
}
}
}
obj* _init_l_lean_elaborator_attribute_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("attribute");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
}
}
obj* _init_l_lean_elaborator_attribute_elaborate___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("local");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_attribute_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_11; 
x_3 = l_lean_parser_command_attribute_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::inc(x_0);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
lean::inc(x_1);
x_11 = l_lean_elaborator_attrs__to__pexpr(x_8, x_1, x_2);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
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
obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_30; 
x_19 = lean::cnstr_get(x_11, 0);
lean::inc(x_19);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_21 = x_11;
}
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::cnstr_get(x_7, 5);
lean::inc(x_27);
lean::inc(x_1);
x_30 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_27, x_1, x_24);
if (lean::obj_tag(x_30) == 0)
{
obj* x_35; obj* x_38; 
lean::dec(x_7);
lean::dec(x_22);
lean::dec(x_1);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_30, 0);
lean::inc(x_35);
lean::dec(x_30);
if (lean::is_scalar(x_21)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_21;
 lean::cnstr_set_tag(x_21, 0);
}
lean::cnstr_set(x_38, 0, x_35);
return x_38;
}
else
{
obj* x_40; obj* x_43; obj* x_45; obj* x_48; uint8 x_51; obj* x_52; obj* x_53; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_21);
x_40 = lean::cnstr_get(x_30, 0);
lean::inc(x_40);
lean::dec(x_30);
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
x_48 = lean::cnstr_get(x_7, 0);
lean::inc(x_48);
lean::dec(x_7);
x_51 = l_option_is__some___main___rarg(x_48);
x_52 = l_lean_elaborator_attribute_elaborate___closed__1;
x_53 = l_lean_elaborator_attribute_elaborate___closed__2;
lean::inc(x_53);
lean::inc(x_52);
x_56 = l_lean_kvmap_set__bool(x_52, x_53, x_51);
x_57 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_57);
x_59 = l_lean_expr_mk__capp(x_57, x_43);
x_60 = lean_expr_mk_app(x_22, x_59);
x_61 = lean_expr_mk_mdata(x_56, x_60);
x_62 = l_lean_elaborator_old__elab__command(x_0, x_61, x_1, x_45);
return x_62;
}
}
}
}
obj* _init_l_lean_elaborator_check_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("#check");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
}
}
obj* l_lean_elaborator_check_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_12; 
x_3 = l_lean_parser_command_check_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::inc(x_0);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
lean::inc(x_1);
x_12 = l_lean_elaborator_to__pexpr___main(x_8, x_1, x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_1);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_17 = x_12;
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
obj* x_19; obj* x_22; obj* x_24; obj* x_27; obj* x_29; obj* x_30; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = l_lean_elaborator_check_elaborate___closed__1;
lean::inc(x_27);
x_29 = lean_expr_mk_mdata(x_27, x_22);
x_30 = l_lean_elaborator_old__elab__command(x_0, x_29, x_1, x_24);
return x_30;
}
}
}
obj* l_lean_elaborator_open_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_1);
x_4 = l_lean_parser_command_open_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::apply_1(x_5, x_0);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 3);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 4);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_16, 2);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_16, 3);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_16, 4);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_16, 5);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_7, 1);
lean::inc(x_30);
lean::dec(x_7);
x_33 = l_list_append___rarg(x_28, x_30);
x_34 = lean::cnstr_get(x_16, 6);
lean::inc(x_34);
lean::dec(x_16);
x_37 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_37, 0, x_18);
lean::cnstr_set(x_37, 1, x_20);
lean::cnstr_set(x_37, 2, x_22);
lean::cnstr_set(x_37, 3, x_24);
lean::cnstr_set(x_37, 4, x_26);
lean::cnstr_set(x_37, 5, x_33);
lean::cnstr_set(x_37, 6, x_34);
x_38 = lean::cnstr_get(x_2, 5);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_2, 6);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_2, 7);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_2, 8);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_2, 9);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_2, 10);
lean::inc(x_48);
lean::dec(x_2);
x_51 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_51, 0, x_8);
lean::cnstr_set(x_51, 1, x_10);
lean::cnstr_set(x_51, 2, x_12);
lean::cnstr_set(x_51, 3, x_14);
lean::cnstr_set(x_51, 4, x_37);
lean::cnstr_set(x_51, 5, x_38);
lean::cnstr_set(x_51, 6, x_40);
lean::cnstr_set(x_51, 7, x_42);
lean::cnstr_set(x_51, 8, x_44);
lean::cnstr_set(x_51, 9, x_46);
lean::cnstr_set(x_51, 10, x_48);
x_52 = lean::box(0);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_51);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
obj* l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(obj* x_0, obj* x_1) {
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
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_4);
x_11 = l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(x_0, x_6);
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
obj* l_lean_elaborator_export_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = l_lean_elaborator_get__namespace___rarg(x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_0);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_8 = x_4;
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_12 = x_4;
}
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_17 = x_10;
}
x_18 = l_lean_parser_command_export_has__view;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::apply_1(x_19, x_0);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_15, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_15, 2);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_15, 3);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_21, 1);
lean::inc(x_30);
lean::dec(x_21);
x_33 = l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(x_13, x_30);
x_34 = l_list_append___rarg(x_28, x_33);
x_35 = lean::cnstr_get(x_15, 4);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_15, 5);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_15, 6);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_15, 7);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_15, 8);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_15, 9);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_15, 10);
lean::inc(x_47);
lean::dec(x_15);
x_50 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_50, 0, x_22);
lean::cnstr_set(x_50, 1, x_24);
lean::cnstr_set(x_50, 2, x_26);
lean::cnstr_set(x_50, 3, x_34);
lean::cnstr_set(x_50, 4, x_35);
lean::cnstr_set(x_50, 5, x_37);
lean::cnstr_set(x_50, 6, x_39);
lean::cnstr_set(x_50, 7, x_41);
lean::cnstr_set(x_50, 8, x_43);
lean::cnstr_set(x_50, 9, x_45);
lean::cnstr_set(x_50, 10, x_47);
x_51 = lean::box(0);
if (lean::is_scalar(x_17)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_17;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_50);
if (lean::is_scalar(x_12)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_12;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
}
obj* _init_l_lean_elaborator_init__quot_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("init_quot");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
x_8 = l_lean_elaborator_dummy;
lean::inc(x_8);
x_10 = lean_expr_mk_mdata(x_7, x_8);
return x_10;
}
}
obj* l_lean_elaborator_init__quot_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_elaborator_init__quot_elaborate___closed__1;
lean::inc(x_3);
x_5 = l_lean_elaborator_old__elab__command(x_0, x_3, x_1, x_2);
return x_5;
}
}
obj* l_lean_elaborator_set__option_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_17; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_51; 
lean::dec(x_1);
x_4 = l_lean_parser_command_set__option_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::apply_1(x_5, x_0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 2);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_2, 4);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 6);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_7, 2);
lean::inc(x_17);
lean::dec(x_7);
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_2, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_2, 2);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_2, 3);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_13, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_13, 1);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_13, 2);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_13, 3);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_13, 4);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_13, 5);
lean::inc(x_38);
lean::dec(x_13);
x_41 = lean::cnstr_get(x_2, 5);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_2, 6);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_2, 7);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_2, 8);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_2, 9);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_2, 10);
lean::inc(x_51);
lean::dec(x_2);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_54; 
x_54 = lean::cnstr_get(x_17, 0);
lean::inc(x_54);
lean::dec(x_17);
if (lean::obj_tag(x_54) == 0)
{
uint8 x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_54);
x_58 = 1;
x_59 = l_lean_kvmap_set__bool(x_15, x_10, x_58);
x_60 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_60, 0, x_28);
lean::cnstr_set(x_60, 1, x_30);
lean::cnstr_set(x_60, 2, x_32);
lean::cnstr_set(x_60, 3, x_34);
lean::cnstr_set(x_60, 4, x_36);
lean::cnstr_set(x_60, 5, x_38);
lean::cnstr_set(x_60, 6, x_59);
x_61 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_61, 0, x_20);
lean::cnstr_set(x_61, 1, x_22);
lean::cnstr_set(x_61, 2, x_24);
lean::cnstr_set(x_61, 3, x_26);
lean::cnstr_set(x_61, 4, x_60);
lean::cnstr_set(x_61, 5, x_41);
lean::cnstr_set(x_61, 6, x_43);
lean::cnstr_set(x_61, 7, x_45);
lean::cnstr_set(x_61, 8, x_47);
lean::cnstr_set(x_61, 9, x_49);
lean::cnstr_set(x_61, 10, x_51);
x_62 = lean::box(0);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_61);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_63);
return x_64;
}
else
{
uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_54);
x_66 = 0;
x_67 = l_lean_kvmap_set__bool(x_15, x_10, x_66);
x_68 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_68, 0, x_28);
lean::cnstr_set(x_68, 1, x_30);
lean::cnstr_set(x_68, 2, x_32);
lean::cnstr_set(x_68, 3, x_34);
lean::cnstr_set(x_68, 4, x_36);
lean::cnstr_set(x_68, 5, x_38);
lean::cnstr_set(x_68, 6, x_67);
x_69 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_69, 0, x_20);
lean::cnstr_set(x_69, 1, x_22);
lean::cnstr_set(x_69, 2, x_24);
lean::cnstr_set(x_69, 3, x_26);
lean::cnstr_set(x_69, 4, x_68);
lean::cnstr_set(x_69, 5, x_41);
lean::cnstr_set(x_69, 6, x_43);
lean::cnstr_set(x_69, 7, x_45);
lean::cnstr_set(x_69, 8, x_47);
lean::cnstr_set(x_69, 9, x_49);
lean::cnstr_set(x_69, 10, x_51);
x_70 = lean::box(0);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_69);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
return x_72;
}
}
case 1:
{
obj* x_73; obj* x_76; 
x_73 = lean::cnstr_get(x_17, 0);
lean::inc(x_73);
lean::dec(x_17);
x_76 = l_lean_parser_string__lit_view_value(x_73);
if (lean::obj_tag(x_76) == 0)
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_10);
x_78 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_78, 0, x_28);
lean::cnstr_set(x_78, 1, x_30);
lean::cnstr_set(x_78, 2, x_32);
lean::cnstr_set(x_78, 3, x_34);
lean::cnstr_set(x_78, 4, x_36);
lean::cnstr_set(x_78, 5, x_38);
lean::cnstr_set(x_78, 6, x_15);
x_79 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_79, 0, x_20);
lean::cnstr_set(x_79, 1, x_22);
lean::cnstr_set(x_79, 2, x_24);
lean::cnstr_set(x_79, 3, x_26);
lean::cnstr_set(x_79, 4, x_78);
lean::cnstr_set(x_79, 5, x_41);
lean::cnstr_set(x_79, 6, x_43);
lean::cnstr_set(x_79, 7, x_45);
lean::cnstr_set(x_79, 8, x_47);
lean::cnstr_set(x_79, 9, x_49);
lean::cnstr_set(x_79, 10, x_51);
x_80 = lean::box(0);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_79);
x_82 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
return x_82;
}
else
{
obj* x_83; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_83 = lean::cnstr_get(x_76, 0);
lean::inc(x_83);
lean::dec(x_76);
x_86 = l_lean_kvmap_set__string(x_15, x_10, x_83);
x_87 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_87, 0, x_28);
lean::cnstr_set(x_87, 1, x_30);
lean::cnstr_set(x_87, 2, x_32);
lean::cnstr_set(x_87, 3, x_34);
lean::cnstr_set(x_87, 4, x_36);
lean::cnstr_set(x_87, 5, x_38);
lean::cnstr_set(x_87, 6, x_86);
x_88 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_88, 0, x_20);
lean::cnstr_set(x_88, 1, x_22);
lean::cnstr_set(x_88, 2, x_24);
lean::cnstr_set(x_88, 3, x_26);
lean::cnstr_set(x_88, 4, x_87);
lean::cnstr_set(x_88, 5, x_41);
lean::cnstr_set(x_88, 6, x_43);
lean::cnstr_set(x_88, 7, x_45);
lean::cnstr_set(x_88, 8, x_47);
lean::cnstr_set(x_88, 9, x_49);
lean::cnstr_set(x_88, 10, x_51);
x_89 = lean::box(0);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_88);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
}
default:
{
obj* x_92; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_92 = lean::cnstr_get(x_17, 0);
lean::inc(x_92);
lean::dec(x_17);
x_95 = l_lean_parser_number_view_to__nat___main(x_92);
x_96 = l_lean_kvmap_set__nat(x_15, x_10, x_95);
x_97 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_97, 0, x_28);
lean::cnstr_set(x_97, 1, x_30);
lean::cnstr_set(x_97, 2, x_32);
lean::cnstr_set(x_97, 3, x_34);
lean::cnstr_set(x_97, 4, x_36);
lean::cnstr_set(x_97, 5, x_38);
lean::cnstr_set(x_97, 6, x_96);
x_98 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_98, 0, x_20);
lean::cnstr_set(x_98, 1, x_22);
lean::cnstr_set(x_98, 2, x_24);
lean::cnstr_set(x_98, 3, x_26);
lean::cnstr_set(x_98, 4, x_97);
lean::cnstr_set(x_98, 5, x_41);
lean::cnstr_set(x_98, 6, x_43);
lean::cnstr_set(x_98, 7, x_45);
lean::cnstr_set(x_98, 8, x_47);
lean::cnstr_set(x_98, 9, x_49);
lean::cnstr_set(x_98, 10, x_51);
x_99 = lean::box(0);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_98);
x_101 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
}
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_syntax_get__pos(x_0);
x_17 = lean::mk_nat_obj(0u);
x_18 = l_option_get__or__else___main___rarg(x_16, x_17);
x_19 = l_lean_file__map_to__position(x_13, x_18);
x_20 = lean::box(0);
x_21 = 2;
x_22 = l_string_join___closed__1;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_24, 0, x_11);
lean::cnstr_set(x_24, 1, x_19);
lean::cnstr_set(x_24, 2, x_20);
lean::cnstr_set(x_24, 3, x_22);
lean::cnstr_set(x_24, 4, x_1);
lean::cnstr_set_scalar(x_24, sizeof(void*)*5, x_21);
x_25 = x_24;
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_27, 0, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg___lambda__1), 2, 1);
lean::closure_set(x_28, 0, x_5);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_29, 0, x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_30, 0, x_27);
lean::closure_set(x_30, 1, x_29);
return x_30;
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(x_0, x_1, x_2, x_4);
return x_7;
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_command_elaborate), 3, 0);
return x_0;
}
}
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_15);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_with__current__command___rarg), 6, 5);
lean::closure_set(x_19, 0, x_10);
lean::closure_set(x_19, 1, x_15);
lean::closure_set(x_19, 2, x_1);
lean::closure_set(x_19, 3, x_2);
lean::closure_set(x_19, 4, x_3);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___lambda__1), 4, 3);
lean::closure_set(x_20, 0, x_12);
lean::closure_set(x_20, 1, x_1);
lean::closure_set(x_20, 2, x_2);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_21, 0, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_22, 0, x_19);
lean::closure_set(x_22, 1, x_21);
return x_22;
}
}
}
obj* _init_l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("no_kind.elaborate: unreachable");
return x_0;
}
}
obj* l_lean_elaborator_no__kind_elaborate___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_11; 
x_9 = l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1;
lean::inc(x_9);
x_11 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_0, x_9, x_1, x_2, x_6);
return x_11;
}
else
{
obj* x_13; obj* x_16; obj* x_19; 
lean::dec(x_0);
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(x_16, x_1, x_2, x_6);
return x_19;
}
}
}
obj* l_lean_elaborator_no__kind_elaborate___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_7 = x_2;
}
lean::inc(x_3);
x_9 = l_lean_parser_syntax_as__node___main(x_3);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_5);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_no__kind_elaborate___lambda__1), 4, 3);
lean::closure_set(x_13, 0, x_3);
lean::closure_set(x_13, 1, x_0);
lean::closure_set(x_13, 2, x_1);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_15, 0, x_12);
lean::closure_set(x_15, 1, x_14);
return x_15;
}
}
obj* l_lean_elaborator_no__kind_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_no__kind_elaborate___lambda__2), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__2(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = l_lean_elaborator_commands_elaborate___main(x_0, x_1, x_2, x_3, x_5);
return x_8;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__3(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = l_lean_elaborator_yield__to__outside___rarg(x_5);
x_9 = lean::box(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__2___boxed), 5, 4);
lean::closure_set(x_10, 0, x_9);
lean::closure_set(x_10, 1, x_1);
lean::closure_set(x_10, 2, x_2);
lean::closure_set(x_10, 3, x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_11);
return x_12;
}
}
obj* _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__1), 1, 0);
return x_0;
}
}
obj* _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2() {
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
obj* _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("module");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("eoi");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid end of input, expected 'end'");
return x_0;
}
}
obj* _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid 'end', there is no open scope to end");
return x_0;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__4(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; 
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
lean::inc(x_5);
x_11 = l_lean_parser_syntax_as__node___main(x_5);
x_12 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1;
lean::inc(x_12);
x_14 = l_option_map___rarg(x_12, x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_5);
lean::dec(x_9);
x_17 = lean::box(0);
lean::inc(x_1);
lean::inc(x_0);
x_20 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_17, x_0, x_1, x_7);
x_21 = lean::box(x_2);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 5, 4);
lean::closure_set(x_22, 0, x_21);
lean::closure_set(x_22, 1, x_3);
lean::closure_set(x_22, 2, x_0);
lean::closure_set(x_22, 3, x_1);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_23, 0, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_28; uint8 x_29; 
x_25 = lean::cnstr_get(x_14, 0);
lean::inc(x_25);
lean::dec(x_14);
x_28 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2;
x_29 = lean_name_dec_eq(x_25, x_28);
if (x_29 == 0)
{
obj* x_30; uint8 x_31; 
x_30 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3;
x_31 = lean_name_dec_eq(x_25, x_30);
lean::dec(x_25);
if (x_31 == 0)
{
obj* x_35; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_5);
lean::dec(x_9);
x_35 = lean::box(0);
lean::inc(x_1);
lean::inc(x_0);
x_38 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_35, x_0, x_1, x_7);
x_39 = lean::box(x_2);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 5, 4);
lean::closure_set(x_40, 0, x_39);
lean::closure_set(x_40, 1, x_3);
lean::closure_set(x_40, 2, x_0);
lean::closure_set(x_40, 3, x_1);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_41, 0, x_40);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_42, 0, x_38);
lean::closure_set(x_42, 1, x_41);
return x_42;
}
else
{
lean::dec(x_3);
if (x_2 == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_47 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_9;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_7);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_50, 0, x_49);
return x_50;
}
else
{
obj* x_52; obj* x_54; 
lean::dec(x_9);
x_52 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4;
lean::inc(x_52);
x_54 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_5, x_52, x_0, x_1, x_7);
return x_54;
}
}
}
else
{
lean::dec(x_3);
lean::dec(x_25);
if (x_2 == 0)
{
obj* x_58; obj* x_60; 
lean::dec(x_9);
x_58 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5;
lean::inc(x_58);
x_60 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_5, x_58, x_0, x_1, x_7);
return x_60;
}
else
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_64 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_9;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_7);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_67, 0, x_66);
return x_67;
}
}
}
}
}
obj* _init_l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("commands.elaborate: out of fuel");
return x_0;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1;
lean::inc(x_8);
x_10 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_3, x_8, x_0, x_1, x_5);
return x_10;
}
}
obj* l_lean_elaborator_commands_elaborate___main(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_1, x_8);
lean::dec(x_8);
lean::dec(x_1);
x_12 = l_lean_elaborator_current__command___rarg(x_4);
x_13 = lean::box(x_0);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__4___boxed), 5, 4);
lean::closure_set(x_14, 0, x_2);
lean::closure_set(x_14, 1, x_3);
lean::closure_set(x_14, 2, x_13);
lean::closure_set(x_14, 3, x_9);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_16, 0, x_12);
lean::closure_set(x_16, 1, x_15);
return x_16;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
x_18 = l_lean_elaborator_current__command___rarg(x_4);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__5), 3, 2);
lean::closure_set(x_19, 0, x_2);
lean::closure_set(x_19, 1, x_3);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_21, 0, x_18);
lean::closure_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate___main___lambda__2(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate___main___lambda__3(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = l_lean_elaborator_commands_elaborate___main___lambda__4(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate___main(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_elaborator_commands_elaborate___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_lean_elaborator_commands_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_elaborator_end__scope___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_6 = x_1;
}
x_7 = lean::apply_1(x_0, x_2);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_10, 0, x_9);
return x_10;
}
}
obj* _init_l_lean_elaborator_end__scope___lambda__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid end of ");
return x_0;
}
}
obj* _init_l_lean_elaborator_end__scope___lambda__2___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", expected name '");
return x_0;
}
}
obj* l_lean_elaborator_end__scope___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; 
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
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
x_14 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_14);
x_16 = l_option_map___rarg(x_14, x_12);
if (lean::obj_tag(x_16) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_21 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_7);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_9);
x_26 = lean::box(0);
x_10 = x_26;
goto lbl_11;
}
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_16, 0);
lean::inc(x_27);
lean::dec(x_16);
if (lean::obj_tag(x_1) == 0)
{
obj* x_32; 
lean::dec(x_9);
lean::dec(x_27);
x_32 = lean::box(0);
x_10 = x_32;
goto lbl_11;
}
else
{
obj* x_33; uint8 x_35; 
x_33 = lean::cnstr_get(x_1, 0);
lean::inc(x_33);
x_35 = lean_name_dec_eq(x_27, x_33);
lean::dec(x_33);
lean::dec(x_27);
if (x_35 == 0)
{
obj* x_39; 
lean::dec(x_9);
x_39 = lean::box(0);
x_10 = x_39;
goto lbl_11;
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_45 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_9;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_7);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_48, 0, x_47);
return x_48;
}
}
}
lbl_11:
{
obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_10);
x_50 = l_lean_parser_command_end_has__view;
x_51 = lean::cnstr_get(x_50, 1);
lean::inc(x_51);
x_53 = lean::apply_1(x_51, x_5);
x_54 = l_lean_elaborator_end__scope___lambda__2___closed__1;
lean::inc(x_54);
x_56 = lean::string_append(x_54, x_0);
lean::dec(x_0);
x_58 = l_lean_elaborator_end__scope___lambda__2___closed__2;
x_59 = lean::string_append(x_56, x_58);
x_60 = lean::box(0);
x_61 = l_option_get__or__else___main___rarg(x_1, x_60);
x_62 = l_lean_name_to__string___closed__1;
lean::inc(x_62);
x_64 = l_lean_name_to__string__with__sep___main(x_62, x_61);
x_65 = lean::string_append(x_59, x_64);
lean::dec(x_64);
x_67 = l_char_has__repr___closed__1;
x_68 = lean::string_append(x_65, x_67);
x_69 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_53, x_68, x_2, x_3, x_7);
return x_69;
}
}
}
obj* _init_l_lean_elaborator_end__scope___lambda__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_end_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__1), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_elaborator_end__scope___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = l_lean_elaborator_current__command___rarg(x_5);
x_9 = l_lean_elaborator_end__scope___lambda__3___closed__1;
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__2), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_2);
lean::closure_set(x_12, 3, x_3);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
}
obj* l_lean_elaborator_end__scope(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_3);
x_6 = l_lean_elaborator_update__parser__config(x_3, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__3), 5, 4);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_1);
lean::closure_set(x_8, 2, x_2);
lean::closure_set(x_8, 3, x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_4(x_0, x_4, x_1, x_2, x_6);
return x_9;
}
}
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_3);
lean::inc(x_2);
x_7 = lean::apply_3(x_0, x_2, x_3, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 1;
x_6 = lean::mk_nat_obj(1000u);
x_7 = l_lean_elaborator_commands_elaborate___main(x_5, x_6, x_1, x_2, x_3);
return x_7;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_5 = x_0;
}
x_6 = lean::cnstr_get(x_1, 4);
lean::inc(x_6);
lean::dec(x_1);
if (lean::is_scalar(x_5)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_5;
}
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_3);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_4 = x_1;
}
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 3);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 5);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 6);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_2, 7);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_2, 8);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_2, 9);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 10);
lean::inc(x_23);
lean::dec(x_2);
x_26 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_7);
lean::cnstr_set(x_26, 2, x_9);
lean::cnstr_set(x_26, 3, x_11);
lean::cnstr_set(x_26, 4, x_0);
lean::cnstr_set(x_26, 5, x_13);
lean::cnstr_set(x_26, 6, x_15);
lean::cnstr_set(x_26, 7, x_17);
lean::cnstr_set(x_26, 8, x_19);
lean::cnstr_set(x_26, 9, x_21);
lean::cnstr_set(x_26, 10, x_23);
x_27 = lean::box(0);
if (lean::is_scalar(x_4)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_4;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_30, 0, x_29);
return x_30;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside), 2, 0);
return x_0;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1;
lean::inc(x_9);
x_11 = l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg(x_9, x_0, x_1, x_2, x_6);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3), 2, 1);
lean::closure_set(x_12, 0, x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__2), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1), 4, 0);
return x_0;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_7);
x_10 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2;
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4), 4, 3);
lean::closure_set(x_12, 0, x_10);
lean::closure_set(x_12, 1, x_0);
lean::closure_set(x_12, 2, x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_9);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
}
obj* _init_l_lean_elaborator_section_elaborate___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("section");
return x_0;
}
}
obj* l_lean_elaborator_section_elaborate___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_15; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_10);
x_12 = l_option_map___rarg(x_10, x_7);
x_13 = l_lean_elaborator_section_elaborate___lambda__1___closed__1;
lean::inc(x_13);
x_15 = l_lean_elaborator_end__scope(x_13, x_12, x_1, x_2, x_4);
return x_15;
}
}
obj* l_lean_elaborator_section_elaborate___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_10 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2(x_0, x_1, x_5);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_section_elaborate___lambda__1), 4, 3);
lean::closure_set(x_11, 0, x_3);
lean::closure_set(x_11, 1, x_0);
lean::closure_set(x_11, 2, x_1);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_12);
return x_13;
}
}
obj* _init_l_lean_elaborator_section_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_section_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__1), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_elaborator_section_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = l_lean_elaborator_section_elaborate___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_section_elaborate___lambda__2), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_1);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
x_6 = 1;
x_7 = lean::mk_nat_obj(1000u);
x_8 = l_lean_elaborator_commands_elaborate___main(x_6, x_7, x_0, x_1, x_3);
return x_8;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_8 = x_3;
}
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 2);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_6, 3);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_6, 4);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_17, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_17, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_17, 3);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
lean::dec(x_0);
x_30 = lean::cnstr_get(x_27, 2);
lean::inc(x_30);
lean::dec(x_27);
x_33 = l_lean_name_append___main(x_4, x_30);
x_34 = lean::cnstr_get(x_17, 4);
lean::inc(x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_34);
x_37 = lean::cnstr_get(x_17, 5);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_17, 6);
lean::inc(x_39);
lean::dec(x_17);
x_42 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_42, 0, x_19);
lean::cnstr_set(x_42, 1, x_21);
lean::cnstr_set(x_42, 2, x_23);
lean::cnstr_set(x_42, 3, x_25);
lean::cnstr_set(x_42, 4, x_36);
lean::cnstr_set(x_42, 5, x_37);
lean::cnstr_set(x_42, 6, x_39);
x_43 = lean::cnstr_get(x_6, 5);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_6, 6);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_6, 7);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_6, 8);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_6, 9);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_6, 10);
lean::inc(x_53);
lean::dec(x_6);
x_56 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_56, 0, x_9);
lean::cnstr_set(x_56, 1, x_11);
lean::cnstr_set(x_56, 2, x_13);
lean::cnstr_set(x_56, 3, x_15);
lean::cnstr_set(x_56, 4, x_42);
lean::cnstr_set(x_56, 5, x_43);
lean::cnstr_set(x_56, 6, x_45);
lean::cnstr_set(x_56, 7, x_47);
lean::cnstr_set(x_56, 8, x_49);
lean::cnstr_set(x_56, 9, x_51);
lean::cnstr_set(x_56, 10, x_53);
x_57 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_8;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_56);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_60, 0, x_59);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__1), 3, 2);
lean::closure_set(x_61, 0, x_1);
lean::closure_set(x_61, 1, x_2);
x_62 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_62, 0, x_61);
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_63, 0, x_60);
lean::closure_set(x_63, 1, x_62);
return x_63;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_6 = l_lean_elaborator_get__namespace___rarg(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2), 4, 3);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1;
lean::inc(x_9);
x_11 = l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg(x_9, x_0, x_1, x_2, x_6);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3), 2, 1);
lean::closure_set(x_12, 0, x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__3), 5, 1);
lean::closure_set(x_4, 0, x_0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__4), 4, 3);
lean::closure_set(x_12, 0, x_4);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_2);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
}
obj* _init_l_lean_elaborator_namespace_elaborate___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("namespace");
return x_0;
}
}
obj* l_lean_elaborator_namespace_elaborate___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_13; obj* x_14; obj* x_16; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 2);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
x_14 = l_lean_elaborator_namespace_elaborate___lambda__1___closed__1;
lean::inc(x_14);
x_16 = l_lean_elaborator_end__scope(x_14, x_13, x_1, x_2, x_4);
return x_16;
}
}
obj* l_lean_elaborator_namespace_elaborate___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_3);
x_11 = l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1(x_3, x_0, x_1, x_5);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_namespace_elaborate___lambda__1), 4, 3);
lean::closure_set(x_12, 0, x_3);
lean::closure_set(x_12, 1, x_0);
lean::closure_set(x_12, 2, x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
}
obj* _init_l_lean_elaborator_namespace_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_namespace_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__1), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_elaborator_namespace_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = l_lean_elaborator_namespace_elaborate___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_namespace_elaborate___lambda__2), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_1);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(obj* x_0, obj* x_1, obj* x_2) {
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
x_26 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_10, x_1, x_2);
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
x_28 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_4, x_1, x_2);
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
x_55 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_36, x_1, x_2);
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
x_62 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_30, x_1, x_2);
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
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__5(obj* x_0, obj* x_1) {
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
x_12 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(x_0, x_7, x_9);
x_0 = x_12;
x_1 = x_4;
goto _start;
}
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_module_header_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_notation_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__3), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_reserve__notation_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__5), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_universe_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__7), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__9(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_variables_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__9), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_include_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__13(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__13), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__15(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_attribute_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__15), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__17(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_open_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__17), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__19(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_export_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__19), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__21(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_check_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__21), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__23(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_init__quot_elaborate___closed__1;
lean::inc(x_7);
x_9 = l_lean_elaborator_old__elab__command(x_2, x_7, x_0, x_4);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_10, 0, x_9);
return x_10;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__23), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_set__option_elaborate(x_2, x_0, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_4 = l_lean_elaborator_current__command___rarg(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* _init_l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_0 = l_lean_parser_module_header;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2), 3, 0);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_lean_parser_command_notation;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4), 3, 0);
lean::inc(x_4);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_lean_parser_command_reserve__notation;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6), 3, 0);
lean::inc(x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_lean_parser_command_universe;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8), 3, 0);
lean::inc(x_12);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
x_16 = l_lean_parser_no__kind;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_no__kind_elaborate), 3, 0);
lean::inc(x_16);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_17);
x_20 = l_lean_parser_command_section;
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_section_elaborate), 3, 0);
lean::inc(x_20);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_21);
x_24 = l_lean_parser_command_namespace;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_namespace_elaborate), 3, 0);
lean::inc(x_24);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_25);
x_28 = l_lean_parser_command_variables;
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10), 3, 0);
lean::inc(x_28);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_29);
x_32 = l_lean_parser_command_include;
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12), 3, 0);
lean::inc(x_32);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_33);
x_36 = l_lean_parser_command_declaration;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14), 3, 0);
lean::inc(x_36);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_37);
x_40 = l_lean_parser_command_attribute;
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16), 3, 0);
lean::inc(x_40);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_41);
x_44 = l_lean_parser_command_open;
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18), 3, 0);
lean::inc(x_44);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_45);
x_48 = l_lean_parser_command_export;
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20), 3, 0);
lean::inc(x_48);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_49);
x_52 = l_lean_parser_command_check;
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22), 3, 0);
lean::inc(x_52);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_53);
x_56 = l_lean_parser_command_init__quot;
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24), 3, 0);
lean::inc(x_56);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_57);
x_60 = l_lean_parser_command_set__option;
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26), 3, 0);
lean::inc(x_60);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_61);
x_64 = lean::box(0);
lean::inc(x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_63);
lean::cnstr_set(x_66, 1, x_64);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_59);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_55);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_51);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_47);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_43);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_39);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_35);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_31);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_27);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_23);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_19);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_15);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_11);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_7);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_3);
lean::cnstr_set(x_81, 1, x_80);
x_82 = l_list_foldl___main___at_lean_elaborator_elaborators___spec__5(x_64, x_81);
return x_82;
}
}
obj* _init_l_lean_elaborator_elaborators() {
_start:
{
obj* x_0; 
x_0 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1;
lean::inc(x_0);
return x_0;
}
}
uint8 l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
lean::dec(x_0);
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_6; uint8 x_9; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean_name_dec_eq(x_0, x_4);
lean::dec(x_4);
if (x_9 == 0)
{
uint8 x_11; 
x_11 = l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(x_0, x_6);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8 x_16; 
lean::dec(x_6);
lean::dec(x_0);
x_16 = 1;
return x_16;
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 0;
x_4 = lean::box(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_13; uint8 x_16; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::cnstr_get(x_10, 2);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean_name_dec_eq(x_13, x_0);
lean::dec(x_13);
if (x_16 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
uint8 x_21; obj* x_22; 
lean::dec(x_7);
lean::dec(x_0);
x_21 = 1;
x_22 = lean::box(x_21);
return x_22;
}
}
}
}
uint8 l_lean_elaborator_is__open__namespace___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::box(0);
x_3 = lean_name_dec_eq(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_8; uint8 x_11; 
x_5 = lean::cnstr_get(x_0, 4);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 4);
lean::inc(x_8);
lean::inc(x_1);
x_11 = l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(x_1, x_8);
if (x_11 == 0)
{
obj* x_12; obj* x_15; uint8 x_16; 
x_12 = lean::cnstr_get(x_5, 5);
lean::inc(x_12);
lean::dec(x_5);
x_15 = l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(x_1, x_12);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
uint8 x_18; 
x_18 = 0;
return x_18;
}
else
{
uint8 x_19; 
x_19 = 1;
return x_19;
}
}
else
{
uint8 x_22; 
lean::dec(x_1);
lean::dec(x_5);
x_22 = 1;
return x_22;
}
}
else
{
uint8 x_25; 
lean::dec(x_1);
lean::dec(x_0);
x_25 = 1;
return x_25;
}
}
}
obj* l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_lean_elaborator_is__open__namespace___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_elaborator_is__open__namespace___main(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_elaborator_is__open__namespace(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_lean_elaborator_is__open__namespace___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_is__open__namespace___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_elaborator_is__open__namespace(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 0;
x_4 = lean::box(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean_name_dec_eq(x_0, x_10);
lean::dec(x_10);
if (x_13 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
uint8 x_18; obj* x_19; 
lean::dec(x_7);
lean::dec(x_0);
x_18 = 1;
x_19 = lean::box(x_18);
return x_19;
}
}
}
}
obj* l_lean_elaborator_match__open__spec(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_4, 2);
lean::inc(x_7);
lean::dec(x_4);
x_10 = l_lean_name_append___main(x_7, x_0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; uint8 x_20; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_14 = x_2;
}
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_15, 2);
lean::inc(x_17);
lean::dec(x_15);
x_20 = lean_name_dec_eq(x_0, x_17);
lean::dec(x_17);
if (x_20 == 0)
{
obj* x_22; obj* x_26; uint8 x_27; 
x_22 = lean::cnstr_get(x_12, 2);
lean::inc(x_22);
lean::dec(x_12);
lean::inc(x_0);
x_26 = l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(x_0, x_22);
x_27 = lean::unbox(x_26);
lean::dec(x_26);
if (x_27 == 0)
{
obj* x_32; 
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_0);
x_32 = lean::box(0);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_39; obj* x_40; 
x_33 = lean::cnstr_get(x_1, 0);
lean::inc(x_33);
lean::dec(x_1);
x_36 = lean::cnstr_get(x_33, 2);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_lean_name_append___main(x_36, x_0);
if (lean::is_scalar(x_14)) {
 x_40 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_40 = x_14;
}
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
}
else
{
obj* x_42; obj* x_45; obj* x_48; obj* x_49; 
lean::dec(x_12);
x_42 = lean::cnstr_get(x_1, 0);
lean::inc(x_42);
lean::dec(x_1);
x_45 = lean::cnstr_get(x_42, 2);
lean::inc(x_45);
lean::dec(x_42);
x_48 = l_lean_name_append___main(x_45, x_0);
if (lean::is_scalar(x_14)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_14;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
}
}
}
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_14; uint8 x_15; 
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
x_10 = lean::cnstr_get(x_1, 8);
lean::inc(x_10);
lean::inc(x_0);
lean::inc(x_5);
x_14 = l_lean_name_append___main(x_5, x_0);
x_15 = lean_environment_contains(x_10, x_14);
if (x_15 == 0)
{
lean::dec(x_9);
lean::dec(x_5);
x_2 = x_7;
goto _start;
}
else
{
obj* x_19; obj* x_20; 
x_19 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; uint8 x_11; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
x_8 = lean::cnstr_get(x_0, 8);
lean::inc(x_8);
lean::inc(x_3);
x_11 = lean_environment_contains(x_8, x_3);
if (x_11 == 0)
{
lean::dec(x_7);
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
x_15 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; uint8 x_11; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::inc(x_0);
x_11 = l_lean_elaborator_is__open__namespace___main(x_0, x_8);
if (x_11 == 0)
{
lean::dec(x_7);
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
x_15 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; uint8 x_11; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
x_8 = lean::cnstr_get(x_0, 8);
lean::inc(x_8);
lean::inc(x_3);
x_11 = lean_environment_contains(x_8, x_3);
if (x_11 == 0)
{
lean::dec(x_7);
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
x_15 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_lean_elaborator_resolve__context___main___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = l_lean_elaborator_match__open__spec(x_0, x_2);
return x_5;
}
}
obj* _init_l_lean_elaborator_resolve__context___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_root_");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_resolve__context___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 4);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_4, 2);
lean::inc(x_6);
lean::inc(x_0);
x_9 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_6, x_0);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_14; 
x_10 = lean::cnstr_get(x_4, 4);
lean::inc(x_10);
lean::inc(x_2);
lean::inc(x_0);
x_14 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(x_0, x_2, x_10);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_19; obj* x_20; uint8 x_23; obj* x_25; obj* x_26; obj* x_29; obj* x_31; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_39; 
x_15 = l_lean_elaborator_resolve__context___main___closed__1;
x_16 = lean::box(0);
lean::inc(x_15);
lean::inc(x_0);
x_19 = l_lean_name_replace__prefix___main(x_0, x_15, x_16);
x_20 = lean::cnstr_get(x_2, 8);
lean::inc(x_20);
lean::inc(x_19);
x_23 = lean_environment_contains(x_20, x_19);
lean::inc(x_0);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_match__open__spec), 2, 1);
lean::closure_set(x_25, 0, x_0);
x_26 = lean::cnstr_get(x_4, 5);
lean::inc(x_26);
lean::dec(x_4);
x_29 = l_list_filter__map___main___rarg(x_25, x_26);
lean::inc(x_2);
x_31 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(x_2, x_29);
x_32 = lean::cnstr_get(x_2, 3);
lean::inc(x_32);
lean::inc(x_2);
x_35 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(x_2, x_32);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_resolve__context___main___lambda__1), 2, 1);
lean::closure_set(x_36, 0, x_0);
x_37 = l_list_filter__map___main___rarg(x_36, x_35);
lean::inc(x_2);
x_39 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(x_2, x_37);
if (x_23 == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_19);
x_41 = l_list_append___rarg(x_14, x_31);
x_42 = l_list_append___rarg(x_41, x_39);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_2);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
return x_44;
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_19);
lean::cnstr_set(x_45, 1, x_14);
x_46 = l_list_append___rarg(x_45, x_31);
x_47 = l_list_append___rarg(x_46, x_39);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_2);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
}
else
{
obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_4);
x_51 = lean::cnstr_get(x_14, 0);
lean::inc(x_51);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_53 = x_14;
}
x_54 = l_lean_name_append___main(x_51, x_0);
x_55 = lean::box(0);
if (lean::is_scalar(x_53)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_53;
}
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_2);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
}
else
{
obj* x_61; obj* x_64; obj* x_66; obj* x_67; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_4);
lean::dec(x_0);
x_61 = lean::cnstr_get(x_9, 0);
lean::inc(x_61);
lean::dec(x_9);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
if (lean::is_shared(x_61)) {
 lean::dec(x_61);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_66 = x_61;
}
x_67 = lean::cnstr_get(x_64, 0);
lean::inc(x_67);
lean::dec(x_64);
x_70 = lean::box(0);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_67);
lean::cnstr_set(x_71, 1, x_70);
if (lean::is_scalar(x_66)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_66;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_2);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
}
}
obj* l_lean_elaborator_resolve__context(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_resolve__context___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
}
lean::inc(x_1);
x_13 = l_lean_elaborator_preresolve___main(x_7, x_1, x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
}
x_29 = l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_36; 
lean::dec(x_11);
lean::dec(x_24);
lean::dec(x_28);
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
lean::dec(x_29);
if (lean::is_scalar(x_23)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_23;
 lean::cnstr_set_tag(x_23, 0);
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
if (lean::is_scalar(x_11)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_11;
}
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_28)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_28;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_23)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_23;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_lean_elaborator_preresolve___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_5 = x_0;
}
lean::inc(x_3);
x_7 = l_lean_elaborator_mangle__ident(x_3);
x_8 = l_lean_elaborator_resolve__context___main(x_7, x_1, x_2);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_5);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_13 = x_8;
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
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_17 = x_8;
}
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_22 = x_15;
}
x_23 = lean::cnstr_get(x_3, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_3, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_3, 2);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_3, 3);
lean::inc(x_29);
x_31 = l_list_append___rarg(x_18, x_29);
x_32 = lean::cnstr_get(x_3, 4);
lean::inc(x_32);
lean::dec(x_3);
x_35 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_35, 0, x_23);
lean::cnstr_set(x_35, 1, x_25);
lean::cnstr_set(x_35, 2, x_27);
lean::cnstr_set(x_35, 3, x_31);
lean::cnstr_set(x_35, 4, x_32);
if (lean::is_scalar(x_5)) {
 x_36 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_36 = x_5;
}
lean::cnstr_set(x_36, 0, x_35);
if (lean::is_scalar(x_22)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_22;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_20);
if (lean::is_scalar(x_17)) {
 x_38 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_38 = x_17;
}
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
}
case 2:
{
obj* x_39; obj* x_41; obj* x_42; obj* x_44; 
x_39 = lean::cnstr_get(x_0, 0);
lean::inc(x_39);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_41 = x_0;
}
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
x_44 = l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(x_42, x_1, x_2);
if (lean::obj_tag(x_44) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_39);
lean::dec(x_41);
x_47 = lean::cnstr_get(x_44, 0);
lean::inc(x_47);
if (lean::is_shared(x_44)) {
 lean::dec(x_44);
 x_49 = lean::box(0);
} else {
 lean::cnstr_release(x_44, 0);
 x_49 = x_44;
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
obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_51 = lean::cnstr_get(x_44, 0);
lean::inc(x_51);
if (lean::is_shared(x_44)) {
 lean::dec(x_44);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_44, 0);
 x_53 = x_44;
}
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
if (lean::is_shared(x_51)) {
 lean::dec(x_51);
 x_58 = lean::box(0);
} else {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_58 = x_51;
}
x_59 = lean::cnstr_get(x_39, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_39, 2);
lean::inc(x_61);
lean::dec(x_39);
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_59);
lean::cnstr_set(x_64, 1, x_54);
lean::cnstr_set(x_64, 2, x_61);
if (lean::is_scalar(x_41)) {
 x_65 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_65 = x_41;
}
lean::cnstr_set(x_65, 0, x_64);
if (lean::is_scalar(x_58)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_58;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_56);
if (lean::is_scalar(x_53)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_53;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
default:
{
obj* x_69; obj* x_70; 
lean::dec(x_1);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_0);
lean::cnstr_set(x_69, 1, x_2);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
}
}
obj* l_lean_elaborator_preresolve(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_preresolve___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _init_l_lean_elaborator_max__recursion() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(100u);
return x_0;
}
}
obj* _init_l_lean_elaborator_max__commands() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(10000u);
return x_0;
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set(x_3, 2, x_1);
return x_3;
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set(x_3, 2, x_1);
return x_3;
}
}
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg), 4, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_run___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_run___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l___private_init_lean_parser_rec_1__run__aux___main___rarg(x_0, x_1, x_2, x_3);
x_7 = lean::apply_2(x_6, x_4, x_5);
return x_7;
}
}
obj* l_lean_parser_rec__t_run___at_lean_elaborator_run___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_run___spec__6), 6, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_2);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::apply_3(x_0, x_6, x_4, x_5);
return x_7;
}
}
obj* _init_l_lean_elaborator_run___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string("foo");
x_5 = 2;
x_6 = lean::mk_string("");
x_7 = lean::mk_string("elaborator.run: out of fuel");
x_8 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 3, x_6);
lean::cnstr_set(x_8, 4, x_7);
lean::cnstr_set_scalar(x_8, sizeof(void*)*5, x_5);
x_9 = x_8;
return x_9;
}
}
obj* l_lean_elaborator_run___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 3);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 4);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 5);
lean::inc(x_15);
x_17 = l_lean_elaborator_run___lambda__1___closed__1;
lean::inc(x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_15);
x_20 = lean::cnstr_get(x_2, 6);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_2, 7);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_2, 8);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_2, 9);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_2, 10);
lean::inc(x_28);
lean::dec(x_2);
x_31 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_7);
lean::cnstr_set(x_31, 2, x_9);
lean::cnstr_set(x_31, 3, x_11);
lean::cnstr_set(x_31, 4, x_13);
lean::cnstr_set(x_31, 5, x_19);
lean::cnstr_set(x_31, 6, x_20);
lean::cnstr_set(x_31, 7, x_22);
lean::cnstr_set(x_31, 8, x_24);
lean::cnstr_set(x_31, 9, x_26);
lean::cnstr_set(x_31, 10, x_28);
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_31);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_35, 0, x_34);
return x_35;
}
}
obj* _init_l_lean_elaborator_run___lambda__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown command: ");
return x_0;
}
}
obj* l_lean_elaborator_run___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_10 = l_lean_name_to__string___closed__1;
lean::inc(x_10);
x_12 = l_lean_name_to__string__with__sep___main(x_10, x_0);
x_13 = l_lean_elaborator_run___lambda__2___closed__1;
lean::inc(x_13);
x_15 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_17 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_1, x_15, x_2, x_3, x_7);
return x_17;
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_1);
lean::dec(x_0);
x_20 = lean::cnstr_get(x_5, 0);
lean::inc(x_20);
lean::dec(x_5);
x_23 = lean::apply_3(x_20, x_2, x_3, x_7);
return x_23;
}
}
}
obj* l_lean_elaborator_run___lambda__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
}
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 4);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 5);
lean::inc(x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::cnstr_get(x_0, 6);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 7);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_0, 8);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_0, 9);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_0, 10);
lean::inc(x_26);
lean::dec(x_0);
x_29 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_29, 0, x_5);
lean::cnstr_set(x_29, 1, x_7);
lean::cnstr_set(x_29, 2, x_9);
lean::cnstr_set(x_29, 3, x_11);
lean::cnstr_set(x_29, 4, x_13);
lean::cnstr_set(x_29, 5, x_17);
lean::cnstr_set(x_29, 6, x_18);
lean::cnstr_set(x_29, 7, x_20);
lean::cnstr_set(x_29, 8, x_22);
lean::cnstr_set(x_29, 9, x_24);
lean::cnstr_set(x_29, 10, x_26);
x_30 = lean::box(0);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_29);
if (lean::is_scalar(x_4)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_4;
 lean::cnstr_set_tag(x_4, 1);
}
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_33, 0, x_32);
return x_33;
}
else
{
obj* x_35; 
lean::dec(x_0);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_35, 0, x_1);
return x_35;
}
}
}
obj* _init_l_lean_elaborator_run___lambda__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("not a command: ");
return x_0;
}
}
obj* l_lean_elaborator_run___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::inc(x_0);
x_6 = l_lean_parser_syntax_to__format___main(x_0);
x_7 = lean::mk_nat_obj(80u);
x_8 = l_lean_format_pretty(x_6, x_7);
x_9 = l_lean_elaborator_run___lambda__4___closed__1;
lean::inc(x_9);
x_11 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_13 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_0, x_11, x_2, x_3, x_4);
return x_13;
}
else
{
obj* x_14; obj* x_17; obj* x_20; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_elaborator_elaborators;
lean::inc(x_17);
lean::inc(x_20);
x_23 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_20, x_17);
lean::inc(x_4);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_4);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_27, 0, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__2), 5, 4);
lean::closure_set(x_28, 0, x_17);
lean::closure_set(x_28, 1, x_0);
lean::closure_set(x_28, 2, x_2);
lean::closure_set(x_28, 3, x_3);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_29, 0, x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_30, 0, x_27);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__3), 2, 1);
lean::closure_set(x_31, 0, x_4);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_31);
return x_32;
}
}
}
obj* l_lean_elaborator_run___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_0);
x_10 = l_lean_parser_syntax_as__node___main(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg), 4, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__4), 5, 1);
lean::closure_set(x_12, 0, x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_with__current__command___rarg), 6, 5);
lean::closure_set(x_14, 0, x_4);
lean::closure_set(x_14, 1, x_13);
lean::closure_set(x_14, 2, x_1);
lean::closure_set(x_14, 3, x_2);
lean::closure_set(x_14, 4, x_6);
return x_14;
}
}
obj* l_lean_elaborator_run___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_0);
lean::inc(x_3);
x_10 = l_lean_elaborator_preresolve___main(x_3, x_0, x_5);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__5), 4, 3);
lean::closure_set(x_12, 0, x_3);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
}
obj* l_lean_elaborator_run___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_5 = l_lean_elaborator_current__command___rarg(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__6), 3, 2);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_5);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_elaborator_run___lambda__8(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_4; obj* x_6; obj* x_7; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_lean_message__log_empty;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_11; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_11, 5);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_17, 0, x_14);
return x_17;
}
}
}
obj* _init_l_lean_elaborator_run___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_17; 
x_0 = lean::box(0);
x_1 = lean::mk_string("trace");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("as_messages");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = l_lean_options_mk;
x_7 = 1;
lean::inc(x_6);
x_9 = l_lean_kvmap_set__bool(x_6, x_5, x_7);
x_10 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1;
x_11 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2;
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_17 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_10);
lean::cnstr_set(x_17, 2, x_11);
lean::cnstr_set(x_17, 3, x_0);
lean::cnstr_set(x_17, 4, x_0);
lean::cnstr_set(x_17, 5, x_0);
lean::cnstr_set(x_17, 6, x_9);
return x_17;
}
}
obj* _init_l_lean_elaborator_run___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean_environment_mk_empty(x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_run___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint32 x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_ngen");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("fixme");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = 0;
x_6 = lean::alloc_cnstr(0, 1, 4);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set_scalar(x_6, sizeof(void*)*1, x_5);
x_7 = x_6;
return x_7;
}
}
obj* _init_l_lean_elaborator_run___closed__4() {
_start:
{
uint8 x_0; obj* x_1; obj* x_2; obj* x_4; 
x_0 = 0;
x_1 = l_lean_elaborator_max__commands;
x_2 = lean::box(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___boxed), 5, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_1);
return x_4;
}
}
obj* _init_l_lean_elaborator_run___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__1), 3, 0);
return x_0;
}
}
obj* _init_l_lean_elaborator_run___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__7), 4, 0);
return x_0;
}
}
obj* _init_l_lean_elaborator_run___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__8), 1, 0);
return x_0;
}
}
obj* l_lean_elaborator_run(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_30; obj* x_31; obj* x_33; 
x_1 = lean::box(0);
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = l_lean_expander_builtin__transformers;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_lean_elaborator_run___closed__1;
x_11 = l_lean_message__log_empty;
x_12 = l_lean_elaborator_run___closed__2;
x_13 = l_lean_elaborator_run___closed__3;
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_1);
lean::inc(x_1);
x_21 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_1);
lean::cnstr_set(x_21, 2, x_9);
lean::cnstr_set(x_21, 3, x_1);
lean::cnstr_set(x_21, 4, x_10);
lean::cnstr_set(x_21, 5, x_11);
lean::cnstr_set(x_21, 6, x_2);
lean::cnstr_set(x_21, 7, x_8);
lean::cnstr_set(x_21, 8, x_12);
lean::cnstr_set(x_21, 9, x_13);
lean::cnstr_set(x_21, 10, x_9);
x_22 = l_lean_elaborator_run___closed__4;
x_23 = l_lean_elaborator_run___closed__5;
x_24 = l_lean_elaborator_run___closed__6;
x_25 = l_lean_elaborator_max__recursion;
lean::inc(x_25);
lean::inc(x_24);
lean::inc(x_23);
lean::inc(x_22);
x_30 = l_lean_parser_rec__t_run___at_lean_elaborator_run___spec__5(x_22, x_23, x_24, x_25, x_0, x_21);
x_31 = l_lean_elaborator_run___closed__7;
lean::inc(x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_33, 0, x_30);
lean::closure_set(x_33, 1, x_31);
return x_33;
}
}
void initialize_init_lean_parser_module();
void initialize_init_lean_expander();
void initialize_init_lean_expr();
void initialize_init_lean_options();
static bool _G_initialized = false;
void initialize_init_lean_elaborator() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_module();
 initialize_init_lean_expander();
 initialize_init_lean_expr();
 initialize_init_lean_options();
 l_lean_elaborator_ordered__rbmap_empty___closed__1 = _init_l_lean_elaborator_ordered__rbmap_empty___closed__1();
 l_lean_elaborator_elaborator__t = _init_l_lean_elaborator_elaborator__t();
 l_lean_elaborator_elaborator__m = _init_l_lean_elaborator_elaborator__m();
 l_lean_elaborator_elaborator = _init_l_lean_elaborator_elaborator();
 l_lean_elaborator_coelaborator__m = _init_l_lean_elaborator_coelaborator__m();
 l_lean_elaborator_coelaborator = _init_l_lean_elaborator_coelaborator();
 l_lean_elaborator_elaborator__t___at_lean_elaborator_command_elaborate___spec__2 = _init_l_lean_elaborator_elaborator__t___at_lean_elaborator_command_elaborate___spec__2();
 l_lean_elaborator_coelaborator__m_monad__coroutine = _init_l_lean_elaborator_coelaborator__m_monad__coroutine();
 l_lean_elaborator_current__command___rarg___closed__1 = _init_l_lean_elaborator_current__command___rarg___closed__1();
 l_lean_elaborator_level__get__app__args___main___closed__1 = _init_l_lean_elaborator_level__get__app__args___main___closed__1();
 l_lean_elaborator_to__level___main___closed__1 = _init_l_lean_elaborator_to__level___main___closed__1();
 l_lean_elaborator_to__level___main___closed__2 = _init_l_lean_elaborator_to__level___main___closed__2();
 l_lean_elaborator_to__level___main___closed__3 = _init_l_lean_elaborator_to__level___main___closed__3();
 l_lean_elaborator_to__level___main___closed__4 = _init_l_lean_elaborator_to__level___main___closed__4();
 l_lean_elaborator_expr_mk__annotation___closed__1 = _init_l_lean_elaborator_expr_mk__annotation___closed__1();
 l_lean_elaborator_dummy = _init_l_lean_elaborator_dummy();
 l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1 = _init_l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1();
 l_lean_elaborator_mk__eqns___closed__1 = _init_l_lean_elaborator_mk__eqns___closed__1();
 l_lean_elaborator_mk__eqns___closed__2 = _init_l_lean_elaborator_mk__eqns___closed__2();
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1();
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1();
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2();
 l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1 = _init_l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1();
 l_lean_elaborator_to__pexpr___main___closed__1 = _init_l_lean_elaborator_to__pexpr___main___closed__1();
 l_lean_elaborator_to__pexpr___main___closed__2 = _init_l_lean_elaborator_to__pexpr___main___closed__2();
 l_lean_elaborator_to__pexpr___main___closed__3 = _init_l_lean_elaborator_to__pexpr___main___closed__3();
 l_lean_elaborator_to__pexpr___main___closed__4 = _init_l_lean_elaborator_to__pexpr___main___closed__4();
 l_lean_elaborator_to__pexpr___main___closed__5 = _init_l_lean_elaborator_to__pexpr___main___closed__5();
 l_lean_elaborator_to__pexpr___main___closed__6 = _init_l_lean_elaborator_to__pexpr___main___closed__6();
 l_lean_elaborator_to__pexpr___main___closed__7 = _init_l_lean_elaborator_to__pexpr___main___closed__7();
 l_lean_elaborator_to__pexpr___main___closed__8 = _init_l_lean_elaborator_to__pexpr___main___closed__8();
 l_lean_elaborator_to__pexpr___main___closed__9 = _init_l_lean_elaborator_to__pexpr___main___closed__9();
 l_lean_elaborator_to__pexpr___main___closed__10 = _init_l_lean_elaborator_to__pexpr___main___closed__10();
 l_lean_elaborator_to__pexpr___main___closed__11 = _init_l_lean_elaborator_to__pexpr___main___closed__11();
 l_lean_elaborator_to__pexpr___main___closed__12 = _init_l_lean_elaborator_to__pexpr___main___closed__12();
 l_lean_elaborator_to__pexpr___main___closed__13 = _init_l_lean_elaborator_to__pexpr___main___closed__13();
 l_lean_elaborator_to__pexpr___main___closed__14 = _init_l_lean_elaborator_to__pexpr___main___closed__14();
 l_lean_elaborator_to__pexpr___main___closed__15 = _init_l_lean_elaborator_to__pexpr___main___closed__15();
 l_lean_elaborator_to__pexpr___main___closed__16 = _init_l_lean_elaborator_to__pexpr___main___closed__16();
 l_lean_elaborator_to__pexpr___main___closed__17 = _init_l_lean_elaborator_to__pexpr___main___closed__17();
 l_lean_elaborator_to__pexpr___main___closed__18 = _init_l_lean_elaborator_to__pexpr___main___closed__18();
 l_lean_elaborator_to__pexpr___main___closed__19 = _init_l_lean_elaborator_to__pexpr___main___closed__19();
 l_lean_elaborator_to__pexpr___main___closed__20 = _init_l_lean_elaborator_to__pexpr___main___closed__20();
 l_lean_elaborator_to__pexpr___main___closed__21 = _init_l_lean_elaborator_to__pexpr___main___closed__21();
 l_lean_elaborator_to__pexpr___main___closed__22 = _init_l_lean_elaborator_to__pexpr___main___closed__22();
 l_lean_elaborator_to__pexpr___main___closed__23 = _init_l_lean_elaborator_to__pexpr___main___closed__23();
 l_lean_elaborator_to__pexpr___main___closed__24 = _init_l_lean_elaborator_to__pexpr___main___closed__24();
 l_lean_elaborator_to__pexpr___main___closed__25 = _init_l_lean_elaborator_to__pexpr___main___closed__25();
 l_lean_elaborator_to__pexpr___main___closed__26 = _init_l_lean_elaborator_to__pexpr___main___closed__26();
 l_lean_elaborator_to__pexpr___main___closed__27 = _init_l_lean_elaborator_to__pexpr___main___closed__27();
 l_lean_elaborator_to__pexpr___main___closed__28 = _init_l_lean_elaborator_to__pexpr___main___closed__28();
 l_lean_elaborator_to__pexpr___main___closed__29 = _init_l_lean_elaborator_to__pexpr___main___closed__29();
 l_lean_elaborator_to__pexpr___main___closed__30 = _init_l_lean_elaborator_to__pexpr___main___closed__30();
 l_lean_elaborator_to__pexpr___main___closed__31 = _init_l_lean_elaborator_to__pexpr___main___closed__31();
 l_lean_elaborator_to__pexpr___main___closed__32 = _init_l_lean_elaborator_to__pexpr___main___closed__32();
 l_lean_elaborator_to__pexpr___main___closed__33 = _init_l_lean_elaborator_to__pexpr___main___closed__33();
 l_lean_elaborator_to__pexpr___main___closed__34 = _init_l_lean_elaborator_to__pexpr___main___closed__34();
 l_lean_elaborator_to__pexpr___main___closed__35 = _init_l_lean_elaborator_to__pexpr___main___closed__35();
 l_lean_elaborator_to__pexpr___main___closed__36 = _init_l_lean_elaborator_to__pexpr___main___closed__36();
 l_lean_elaborator_to__pexpr___main___closed__37 = _init_l_lean_elaborator_to__pexpr___main___closed__37();
 l_lean_elaborator_to__pexpr___main___closed__38 = _init_l_lean_elaborator_to__pexpr___main___closed__38();
 l_lean_elaborator_to__pexpr___main___closed__39 = _init_l_lean_elaborator_to__pexpr___main___closed__39();
 l_lean_elaborator_to__pexpr___main___closed__40 = _init_l_lean_elaborator_to__pexpr___main___closed__40();
 l_lean_elaborator_to__pexpr___main___closed__41 = _init_l_lean_elaborator_to__pexpr___main___closed__41();
 l_lean_elaborator_to__pexpr___main___closed__42 = _init_l_lean_elaborator_to__pexpr___main___closed__42();
 l_lean_elaborator_to__pexpr___main___closed__43 = _init_l_lean_elaborator_to__pexpr___main___closed__43();
 l_lean_elaborator_to__pexpr___main___closed__44 = _init_l_lean_elaborator_to__pexpr___main___closed__44();
 l_lean_elaborator_to__pexpr___main___closed__45 = _init_l_lean_elaborator_to__pexpr___main___closed__45();
 l_lean_elaborator_to__pexpr___main___closed__46 = _init_l_lean_elaborator_to__pexpr___main___closed__46();
 l_lean_elaborator_to__pexpr___main___closed__47 = _init_l_lean_elaborator_to__pexpr___main___closed__47();
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6();
 l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1 = _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1();
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13();
 l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1 = _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1();
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__1 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__1();
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__2 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__2();
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__3 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__3();
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__4 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__4();
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__5 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__5();
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__6 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__6();
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__7 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__7();
 l_lean_elaborator_locally___rarg___closed__1 = _init_l_lean_elaborator_locally___rarg___closed__1();
 l_lean_elaborator_elab__def__like___closed__1 = _init_l_lean_elaborator_elab__def__like___closed__1();
 l_lean_elaborator_elab__def__like___closed__2 = _init_l_lean_elaborator_elab__def__like___closed__2();
 l_lean_elaborator_infer__mod__to__pexpr___closed__1 = _init_l_lean_elaborator_infer__mod__to__pexpr___closed__1();
 l_lean_elaborator_infer__mod__to__pexpr___closed__2 = _init_l_lean_elaborator_infer__mod__to__pexpr___closed__2();
 l_lean_elaborator_infer__mod__to__pexpr___closed__3 = _init_l_lean_elaborator_infer__mod__to__pexpr___closed__3();
 l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1();
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1();
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2();
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3();
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4();
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5();
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6();
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7();
 l_lean_elaborator_variables_elaborate___closed__1 = _init_l_lean_elaborator_variables_elaborate___closed__1();
 l_lean_elaborator_variables_elaborate___closed__2 = _init_l_lean_elaborator_variables_elaborate___closed__2();
 l_lean_elaborator_module_header_elaborate___closed__1 = _init_l_lean_elaborator_module_header_elaborate___closed__1();
 l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1 = _init_l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1();
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1();
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2();
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3();
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4();
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5();
 l_lean_elaborator_command__parser__config_register__notation__parser___closed__1 = _init_l_lean_elaborator_command__parser__config_register__notation__parser___closed__1();
 l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1 = _init_l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1();
 l_lean_elaborator_yield__to__outside___rarg___closed__1 = _init_l_lean_elaborator_yield__to__outside___rarg___closed__1();
 l_lean_elaborator_postprocess__notation__spec___closed__1 = _init_l_lean_elaborator_postprocess__notation__spec___closed__1();
 l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1();
 l_lean_elaborator_match__spec___closed__1 = _init_l_lean_elaborator_match__spec___closed__1();
 l_lean_elaborator_notation_elaborate__aux___closed__1 = _init_l_lean_elaborator_notation_elaborate__aux___closed__1();
 l_lean_elaborator_mk__notation__kind___rarg___closed__1 = _init_l_lean_elaborator_mk__notation__kind___rarg___closed__1();
 l_lean_elaborator_notation_elaborate___closed__1 = _init_l_lean_elaborator_notation_elaborate___closed__1();
 l_lean_elaborator_notation_elaborate___closed__2 = _init_l_lean_elaborator_notation_elaborate___closed__2();
 l_lean_elaborator_universe_elaborate___closed__1 = _init_l_lean_elaborator_universe_elaborate___closed__1();
 l_lean_elaborator_universe_elaborate___closed__2 = _init_l_lean_elaborator_universe_elaborate___closed__2();
 l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1();
 l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2 = _init_l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2();
 l_lean_elaborator_attribute_elaborate___closed__1 = _init_l_lean_elaborator_attribute_elaborate___closed__1();
 l_lean_elaborator_attribute_elaborate___closed__2 = _init_l_lean_elaborator_attribute_elaborate___closed__2();
 l_lean_elaborator_check_elaborate___closed__1 = _init_l_lean_elaborator_check_elaborate___closed__1();
 l_lean_elaborator_init__quot_elaborate___closed__1 = _init_l_lean_elaborator_init__quot_elaborate___closed__1();
 l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1 = _init_l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1();
 l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1 = _init_l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1();
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1();
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2();
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3();
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4();
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5();
 l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1 = _init_l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1();
 l_lean_elaborator_end__scope___lambda__2___closed__1 = _init_l_lean_elaborator_end__scope___lambda__2___closed__1();
 l_lean_elaborator_end__scope___lambda__2___closed__2 = _init_l_lean_elaborator_end__scope___lambda__2___closed__2();
 l_lean_elaborator_end__scope___lambda__3___closed__1 = _init_l_lean_elaborator_end__scope___lambda__3___closed__1();
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1();
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1();
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2();
 l_lean_elaborator_section_elaborate___lambda__1___closed__1 = _init_l_lean_elaborator_section_elaborate___lambda__1___closed__1();
 l_lean_elaborator_section_elaborate___closed__1 = _init_l_lean_elaborator_section_elaborate___closed__1();
 l_lean_elaborator_namespace_elaborate___lambda__1___closed__1 = _init_l_lean_elaborator_namespace_elaborate___lambda__1___closed__1();
 l_lean_elaborator_namespace_elaborate___closed__1 = _init_l_lean_elaborator_namespace_elaborate___closed__1();
 l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1 = _init_l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1();
 l_lean_elaborator_elaborators = _init_l_lean_elaborator_elaborators();
 l_lean_elaborator_resolve__context___main___closed__1 = _init_l_lean_elaborator_resolve__context___main___closed__1();
 l_lean_elaborator_max__recursion = _init_l_lean_elaborator_max__recursion();
 l_lean_elaborator_max__commands = _init_l_lean_elaborator_max__commands();
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1();
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2();
 l_lean_elaborator_run___lambda__1___closed__1 = _init_l_lean_elaborator_run___lambda__1___closed__1();
 l_lean_elaborator_run___lambda__2___closed__1 = _init_l_lean_elaborator_run___lambda__2___closed__1();
 l_lean_elaborator_run___lambda__4___closed__1 = _init_l_lean_elaborator_run___lambda__4___closed__1();
 l_lean_elaborator_run___closed__1 = _init_l_lean_elaborator_run___closed__1();
 l_lean_elaborator_run___closed__2 = _init_l_lean_elaborator_run___closed__2();
 l_lean_elaborator_run___closed__3 = _init_l_lean_elaborator_run___closed__3();
 l_lean_elaborator_run___closed__4 = _init_l_lean_elaborator_run___closed__4();
 l_lean_elaborator_run___closed__5 = _init_l_lean_elaborator_run___closed__5();
 l_lean_elaborator_run___closed__6 = _init_l_lean_elaborator_run___closed__6();
 l_lean_elaborator_run___closed__7 = _init_l_lean_elaborator_run___closed__7();
}
