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
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
lean::cnstr_set(x_2, 2, x_1);
return x_2;
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_14 = x_1;
} else {
 lean::dec(x_1);
 x_14 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_43 = x_1;
} else {
 lean::dec(x_1);
 x_43 = lean::box(0);
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
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
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
lean::dec(x_12);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_19);
return x_21;
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_14 = x_1;
} else {
 lean::dec(x_1);
 x_14 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_43 = x_1;
} else {
 lean::dec(x_1);
 x_43 = lean::box(0);
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
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
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
lean::dec(x_12);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_19);
return x_21;
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
return x_0;
}
}
obj* _init_l_lean_elaborator_elaborator__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_elaborator_elaborator() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_elaborator_coelaborator__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_elaborator_coelaborator() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_elaborator_elaborator__t___at_lean_elaborator_command_elaborate___spec__2() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
} else {
 lean::dec(x_1);
 x_5 = lean::box(0);
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
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_46 = x_42;
} else {
 lean::dec(x_42);
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
obj* x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_48 = lean::cnstr_get(x_42, 0);
lean::inc(x_48);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_50 = x_42;
} else {
 lean::dec(x_42);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_55 = x_48;
} else {
 lean::dec(x_48);
 x_55 = lean::box(0);
}
x_56 = lean::cnstr_get(x_51, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_51, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_60 = x_51;
} else {
 lean::dec(x_51);
 x_60 = lean::box(0);
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
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_1, x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_level__add___main(x_0, x_5);
x_8 = level_mk_succ(x_7);
return x_8;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
} else {
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
} else {
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
} else {
 lean::dec(x_21);
 x_28 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
} else {
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
} else {
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
} else {
 lean::dec(x_21);
 x_28 = lean::box(0);
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
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
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
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::dec(x_5);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_19 = x_12;
} else {
 lean::dec(x_12);
 x_19 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Prop");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean_expr_mk_const(x_2, x_0);
return x_3;
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
} else {
 lean::dec(x_1);
 x_8 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_22 = x_16;
} else {
 lean::dec(x_16);
 x_22 = lean::box(0);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_26 = x_16;
} else {
 lean::dec(x_16);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 x_31 = x_24;
} else {
 lean::dec(x_24);
 x_31 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_22 = x_15;
} else {
 lean::dec(x_15);
 x_22 = lean::box(0);
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
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_26 = x_15;
} else {
 lean::dec(x_15);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 x_31 = x_24;
} else {
 lean::dec(x_24);
 x_31 = lean::box(0);
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
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_53 = x_46;
} else {
 lean::dec(x_46);
 x_53 = lean::box(0);
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
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_71 = x_64;
} else {
 lean::dec(x_64);
 x_71 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_22 = x_16;
} else {
 lean::dec(x_16);
 x_22 = lean::box(0);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_26 = x_16;
} else {
 lean::dec(x_16);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 x_31 = x_24;
} else {
 lean::dec(x_24);
 x_31 = lean::box(0);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_21 = x_16;
} else {
 lean::dec(x_16);
 x_21 = lean::box(0);
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
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 x_37 = x_32;
} else {
 lean::dec(x_32);
 x_37 = lean::box(0);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_21 = x_16;
} else {
 lean::dec(x_16);
 x_21 = lean::box(0);
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
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 x_42 = x_37;
} else {
 lean::dec(x_37);
 x_42 = lean::box(0);
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
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 lean::cnstr_release(x_53, 1);
 x_58 = x_53;
} else {
 lean::dec(x_53);
 x_58 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
} else {
 lean::dec(x_23);
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
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_35 = x_23;
} else {
 lean::dec(x_23);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_40 = x_33;
} else {
 lean::dec(x_33);
 x_40 = lean::box(0);
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
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_82 = x_75;
} else {
 lean::dec(x_75);
 x_82 = lean::box(0);
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
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_86 = x_75;
} else {
 lean::dec(x_75);
 x_86 = lean::box(0);
}
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_91 = x_84;
} else {
 lean::dec(x_84);
 x_91 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_29 = x_22;
} else {
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
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_33 = x_22;
} else {
 lean::dec(x_22);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_38 = x_31;
} else {
 lean::dec(x_31);
 x_38 = lean::box(0);
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_75 = x_68;
} else {
 lean::dec(x_68);
 x_75 = lean::box(0);
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_79 = x_68;
} else {
 lean::dec(x_68);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
} else {
 lean::dec(x_77);
 x_84 = lean::box(0);
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
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_115 = x_108;
} else {
 lean::dec(x_108);
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
obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
x_117 = lean::cnstr_get(x_108, 0);
lean::inc(x_117);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_119 = x_108;
} else {
 lean::dec(x_108);
 x_119 = lean::box(0);
}
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_124 = x_117;
} else {
 lean::dec(x_117);
 x_124 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
} else {
 lean::dec(x_23);
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
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_35 = x_23;
} else {
 lean::dec(x_23);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_40 = x_33;
} else {
 lean::dec(x_33);
 x_40 = lean::box(0);
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
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_82 = x_75;
} else {
 lean::dec(x_75);
 x_82 = lean::box(0);
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
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_86 = x_75;
} else {
 lean::dec(x_75);
 x_86 = lean::box(0);
}
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_91 = x_84;
} else {
 lean::dec(x_84);
 x_91 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_29 = x_22;
} else {
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
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_33 = x_22;
} else {
 lean::dec(x_22);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_38 = x_31;
} else {
 lean::dec(x_31);
 x_38 = lean::box(0);
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_75 = x_68;
} else {
 lean::dec(x_68);
 x_75 = lean::box(0);
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_79 = x_68;
} else {
 lean::dec(x_68);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
} else {
 lean::dec(x_77);
 x_84 = lean::box(0);
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
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_115 = x_108;
} else {
 lean::dec(x_108);
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
obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
x_117 = lean::cnstr_get(x_108, 0);
lean::inc(x_117);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_119 = x_108;
} else {
 lean::dec(x_108);
 x_119 = lean::box(0);
}
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_124 = x_117;
} else {
 lean::dec(x_117);
 x_124 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
} else {
 lean::dec(x_23);
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
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_35 = x_23;
} else {
 lean::dec(x_23);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_40 = x_33;
} else {
 lean::dec(x_33);
 x_40 = lean::box(0);
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
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_82 = x_75;
} else {
 lean::dec(x_75);
 x_82 = lean::box(0);
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
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_86 = x_75;
} else {
 lean::dec(x_75);
 x_86 = lean::box(0);
}
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_91 = x_84;
} else {
 lean::dec(x_84);
 x_91 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_29 = x_22;
} else {
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
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_33 = x_22;
} else {
 lean::dec(x_22);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_38 = x_31;
} else {
 lean::dec(x_31);
 x_38 = lean::box(0);
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_75 = x_68;
} else {
 lean::dec(x_68);
 x_75 = lean::box(0);
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_79 = x_68;
} else {
 lean::dec(x_68);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
} else {
 lean::dec(x_77);
 x_84 = lean::box(0);
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
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_115 = x_108;
} else {
 lean::dec(x_108);
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
obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
x_117 = lean::cnstr_get(x_108, 0);
lean::inc(x_117);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_119 = x_108;
} else {
 lean::dec(x_108);
 x_119 = lean::box(0);
}
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_124 = x_117;
} else {
 lean::dec(x_117);
 x_124 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
} else {
 lean::dec(x_23);
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
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_35 = x_23;
} else {
 lean::dec(x_23);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_40 = x_33;
} else {
 lean::dec(x_33);
 x_40 = lean::box(0);
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
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_82 = x_75;
} else {
 lean::dec(x_75);
 x_82 = lean::box(0);
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
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_86 = x_75;
} else {
 lean::dec(x_75);
 x_86 = lean::box(0);
}
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_91 = x_84;
} else {
 lean::dec(x_84);
 x_91 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_29 = x_22;
} else {
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
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_33 = x_22;
} else {
 lean::dec(x_22);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_38 = x_31;
} else {
 lean::dec(x_31);
 x_38 = lean::box(0);
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_75 = x_68;
} else {
 lean::dec(x_68);
 x_75 = lean::box(0);
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_79 = x_68;
} else {
 lean::dec(x_68);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
} else {
 lean::dec(x_77);
 x_84 = lean::box(0);
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
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_115 = x_108;
} else {
 lean::dec(x_108);
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
obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
x_117 = lean::cnstr_get(x_108, 0);
lean::inc(x_117);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_119 = x_108;
} else {
 lean::dec(x_108);
 x_119 = lean::box(0);
}
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_124 = x_117;
} else {
 lean::dec(x_117);
 x_124 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
} else {
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
} else {
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
} else {
 lean::dec(x_21);
 x_28 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
} else {
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
} else {
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
} else {
 lean::dec(x_21);
 x_28 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("annotation");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("preresolved");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = l_lean_kvmap_set__name(x_0, x_2, x_4);
return x_5;
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_73 = x_68;
} else {
 lean::dec(x_68);
 x_73 = lean::box(0);
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_77 = x_68;
} else {
 lean::dec(x_68);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_75, 1);
lean::inc(x_80);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 lean::cnstr_release(x_75, 1);
 x_82 = x_75;
} else {
 lean::dec(x_75);
 x_82 = lean::box(0);
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
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 x_129 = x_125;
} else {
 lean::dec(x_125);
 x_129 = lean::box(0);
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
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 x_133 = x_125;
} else {
 lean::dec(x_125);
 x_133 = lean::box(0);
}
x_134 = lean::cnstr_get(x_131, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_131, 1);
lean::inc(x_136);
if (lean::is_exclusive(x_131)) {
 lean::cnstr_release(x_131, 0);
 lean::cnstr_release(x_131, 1);
 x_138 = x_131;
} else {
 lean::dec(x_131);
 x_138 = lean::box(0);
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
if (lean::is_exclusive(x_209)) {
 lean::cnstr_release(x_209, 0);
 lean::cnstr_release(x_209, 1);
 x_214 = x_209;
} else {
 lean::dec(x_209);
 x_214 = lean::box(0);
}
x_215 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_212);
x_216 = lean::cnstr_get(x_215, 0);
lean::inc(x_216);
x_218 = lean::cnstr_get(x_215, 1);
lean::inc(x_218);
if (lean::is_exclusive(x_215)) {
 lean::cnstr_release(x_215, 0);
 lean::cnstr_release(x_215, 1);
 x_220 = x_215;
} else {
 lean::dec(x_215);
 x_220 = lean::box(0);
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
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 x_233 = x_223;
} else {
 lean::dec(x_223);
 x_233 = lean::box(0);
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
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 x_237 = x_223;
} else {
 lean::dec(x_223);
 x_237 = lean::box(0);
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
obj* x_304; obj* x_306; obj* x_309; obj* x_310; obj* x_312; obj* x_313; obj* x_315; obj* x_316; uint8 x_317; obj* x_319; obj* x_320; obj* x_323; obj* x_325; obj* x_326; obj* x_328; obj* x_329; obj* x_330; obj* x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
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
x_315 = l_lean_kvmap_set__nat(x_309, x_313, x_312);
x_316 = l_lean_elaborator_to__pexpr___main___closed__26;
x_317 = 0;
lean::inc(x_316);
x_319 = l_lean_kvmap_set__bool(x_315, x_316, x_317);
x_320 = lean::cnstr_get(x_206, 1);
lean::inc(x_320);
lean::dec(x_206);
x_323 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_323);
x_325 = l_option_map___rarg(x_323, x_320);
x_326 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_326);
x_328 = l_option_map___rarg(x_326, x_325);
x_329 = l_option_get__or__else___main___rarg(x_328, x_309);
x_330 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_330);
x_332 = l_lean_kvmap_set__name(x_319, x_330, x_329);
x_333 = l_list_append___rarg(x_238, x_304);
x_334 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(x_333);
x_335 = lean_expr_mk_mdata(x_332, x_334);
if (lean::is_scalar(x_214)) {
 x_336 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_336 = x_214;
}
lean::cnstr_set(x_336, 0, x_335);
lean::cnstr_set(x_336, 1, x_306);
x_14 = x_336;
goto lbl_15;
}
}
}
else
{
obj* x_337; obj* x_339; obj* x_341; obj* x_342; 
x_337 = lean::cnstr_get(x_218, 0);
lean::inc(x_337);
x_339 = lean::cnstr_get(x_218, 1);
lean::inc(x_339);
if (lean::is_exclusive(x_218)) {
 lean::cnstr_release(x_218, 0);
 lean::cnstr_release(x_218, 1);
 x_341 = x_218;
} else {
 lean::dec(x_218);
 x_341 = lean::box(0);
}
x_342 = lean::cnstr_get(x_337, 0);
lean::inc(x_342);
lean::dec(x_337);
if (lean::obj_tag(x_342) == 0)
{
obj* x_346; obj* x_347; obj* x_349; obj* x_350; obj* x_353; 
lean::dec(x_339);
x_346 = l_lean_parser_term_struct__inst__item_has__view;
x_347 = lean::cnstr_get(x_346, 1);
lean::inc(x_347);
x_349 = lean::apply_1(x_347, x_342);
x_350 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
lean::inc(x_350);
x_353 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_349, x_350, x_1, x_2);
if (lean::obj_tag(x_353) == 0)
{
obj* x_363; obj* x_365; obj* x_366; 
lean::dec(x_341);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_210);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_363 = lean::cnstr_get(x_353, 0);
lean::inc(x_363);
if (lean::is_exclusive(x_353)) {
 lean::cnstr_release(x_353, 0);
 x_365 = x_353;
} else {
 lean::dec(x_353);
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
obj* x_367; obj* x_369; obj* x_370; obj* x_372; obj* x_377; 
x_367 = lean::cnstr_get(x_353, 0);
lean::inc(x_367);
if (lean::is_exclusive(x_353)) {
 lean::cnstr_release(x_353, 0);
 x_369 = x_353;
} else {
 lean::dec(x_353);
 x_369 = lean::box(0);
}
x_370 = lean::cnstr_get(x_367, 0);
lean::inc(x_370);
x_372 = lean::cnstr_get(x_367, 1);
lean::inc(x_372);
lean::dec(x_367);
lean::inc(x_1);
lean::inc(x_0);
x_377 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_210, x_1, x_372);
if (lean::obj_tag(x_377) == 0)
{
obj* x_387; obj* x_390; 
lean::dec(x_341);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_370);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_387 = lean::cnstr_get(x_377, 0);
lean::inc(x_387);
lean::dec(x_377);
if (lean::is_scalar(x_369)) {
 x_390 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_390 = x_369;
 lean::cnstr_set_tag(x_369, 0);
}
lean::cnstr_set(x_390, 0, x_387);
return x_390;
}
else
{
obj* x_391; obj* x_394; obj* x_396; obj* x_399; obj* x_403; 
x_391 = lean::cnstr_get(x_377, 0);
lean::inc(x_391);
lean::dec(x_377);
x_394 = lean::cnstr_get(x_391, 0);
lean::inc(x_394);
x_396 = lean::cnstr_get(x_391, 1);
lean::inc(x_396);
lean::dec(x_391);
lean::inc(x_1);
lean::inc(x_0);
x_403 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_216, x_1, x_396);
if (lean::obj_tag(x_403) == 0)
{
obj* x_413; obj* x_416; 
lean::dec(x_341);
lean::dec(x_394);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_370);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_214);
x_413 = lean::cnstr_get(x_403, 0);
lean::inc(x_413);
lean::dec(x_403);
if (lean::is_scalar(x_369)) {
 x_416 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_416 = x_369;
 lean::cnstr_set_tag(x_369, 0);
}
lean::cnstr_set(x_416, 0, x_413);
return x_416;
}
else
{
obj* x_417; obj* x_420; obj* x_422; obj* x_425; 
x_417 = lean::cnstr_get(x_403, 0);
lean::inc(x_417);
lean::dec(x_403);
x_420 = lean::cnstr_get(x_417, 0);
lean::inc(x_420);
x_422 = lean::cnstr_get(x_417, 1);
lean::inc(x_422);
lean::dec(x_417);
x_425 = lean::cnstr_get(x_206, 2);
lean::inc(x_425);
if (lean::obj_tag(x_425) == 0)
{
obj* x_429; 
lean::dec(x_341);
lean::dec(x_369);
if (lean::is_scalar(x_220)) {
 x_429 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_429 = x_220;
}
lean::cnstr_set(x_429, 0, x_420);
lean::cnstr_set(x_429, 1, x_422);
x_399 = x_429;
goto lbl_400;
}
else
{
obj* x_430; obj* x_433; obj* x_437; 
x_430 = lean::cnstr_get(x_425, 0);
lean::inc(x_430);
lean::dec(x_425);
x_433 = lean::cnstr_get(x_430, 0);
lean::inc(x_433);
lean::dec(x_430);
lean::inc(x_1);
x_437 = l_lean_elaborator_to__pexpr___main(x_433, x_1, x_422);
if (lean::obj_tag(x_437) == 0)
{
obj* x_448; obj* x_451; 
lean::dec(x_341);
lean::dec(x_394);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_370);
lean::dec(x_206);
lean::dec(x_420);
lean::dec(x_220);
lean::dec(x_214);
x_448 = lean::cnstr_get(x_437, 0);
lean::inc(x_448);
lean::dec(x_437);
if (lean::is_scalar(x_369)) {
 x_451 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_451 = x_369;
 lean::cnstr_set_tag(x_369, 0);
}
lean::cnstr_set(x_451, 0, x_448);
return x_451;
}
else
{
obj* x_453; obj* x_456; obj* x_458; obj* x_461; obj* x_462; obj* x_463; obj* x_464; 
lean::dec(x_369);
x_453 = lean::cnstr_get(x_437, 0);
lean::inc(x_453);
lean::dec(x_437);
x_456 = lean::cnstr_get(x_453, 0);
lean::inc(x_456);
x_458 = lean::cnstr_get(x_453, 1);
lean::inc(x_458);
lean::dec(x_453);
x_461 = lean::box(0);
if (lean::is_scalar(x_341)) {
 x_462 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_462 = x_341;
}
lean::cnstr_set(x_462, 0, x_456);
lean::cnstr_set(x_462, 1, x_461);
x_463 = l_list_append___rarg(x_420, x_462);
if (lean::is_scalar(x_220)) {
 x_464 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_464 = x_220;
}
lean::cnstr_set(x_464, 0, x_463);
lean::cnstr_set(x_464, 1, x_458);
x_399 = x_464;
goto lbl_400;
}
}
}
lbl_400:
{
obj* x_465; obj* x_467; obj* x_470; obj* x_471; obj* x_473; obj* x_474; obj* x_476; obj* x_477; uint8 x_478; obj* x_481; obj* x_482; obj* x_485; obj* x_487; obj* x_488; obj* x_490; obj* x_491; obj* x_492; obj* x_494; obj* x_495; obj* x_496; obj* x_497; obj* x_498; 
x_465 = lean::cnstr_get(x_399, 0);
lean::inc(x_465);
x_467 = lean::cnstr_get(x_399, 1);
lean::inc(x_467);
lean::dec(x_399);
x_470 = lean::box(0);
x_471 = lean::mk_nat_obj(0u);
lean::inc(x_394);
x_473 = l_list_length__aux___main___rarg(x_394, x_471);
x_474 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_474);
x_476 = l_lean_kvmap_set__nat(x_470, x_474, x_473);
x_477 = l_lean_elaborator_to__pexpr___main___closed__26;
x_478 = lean::unbox(x_370);
lean::dec(x_370);
lean::inc(x_477);
x_481 = l_lean_kvmap_set__bool(x_476, x_477, x_478);
x_482 = lean::cnstr_get(x_206, 1);
lean::inc(x_482);
lean::dec(x_206);
x_485 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_485);
x_487 = l_option_map___rarg(x_485, x_482);
x_488 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_488);
x_490 = l_option_map___rarg(x_488, x_487);
x_491 = l_option_get__or__else___main___rarg(x_490, x_470);
x_492 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_492);
x_494 = l_lean_kvmap_set__name(x_481, x_492, x_491);
x_495 = l_list_append___rarg(x_394, x_465);
x_496 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_495);
x_497 = lean_expr_mk_mdata(x_494, x_496);
if (lean::is_scalar(x_214)) {
 x_498 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_498 = x_214;
}
lean::cnstr_set(x_498, 0, x_497);
lean::cnstr_set(x_498, 1, x_467);
x_14 = x_498;
goto lbl_15;
}
}
}
}
else
{
if (lean::obj_tag(x_339) == 0)
{
obj* x_502; 
lean::dec(x_342);
lean::inc(x_1);
lean::inc(x_0);
x_502 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_210, x_1, x_2);
if (lean::obj_tag(x_502) == 0)
{
obj* x_511; obj* x_513; obj* x_514; 
lean::dec(x_341);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_511 = lean::cnstr_get(x_502, 0);
lean::inc(x_511);
if (lean::is_exclusive(x_502)) {
 lean::cnstr_release(x_502, 0);
 x_513 = x_502;
} else {
 lean::dec(x_502);
 x_513 = lean::box(0);
}
if (lean::is_scalar(x_513)) {
 x_514 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_514 = x_513;
}
lean::cnstr_set(x_514, 0, x_511);
return x_514;
}
else
{
obj* x_515; obj* x_517; obj* x_518; obj* x_520; obj* x_523; obj* x_527; 
x_515 = lean::cnstr_get(x_502, 0);
lean::inc(x_515);
if (lean::is_exclusive(x_502)) {
 lean::cnstr_release(x_502, 0);
 x_517 = x_502;
} else {
 lean::dec(x_502);
 x_517 = lean::box(0);
}
x_518 = lean::cnstr_get(x_515, 0);
lean::inc(x_518);
x_520 = lean::cnstr_get(x_515, 1);
lean::inc(x_520);
lean::dec(x_515);
lean::inc(x_1);
lean::inc(x_0);
x_527 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_216, x_1, x_520);
if (lean::obj_tag(x_527) == 0)
{
obj* x_536; obj* x_539; 
lean::dec(x_341);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_214);
lean::dec(x_518);
x_536 = lean::cnstr_get(x_527, 0);
lean::inc(x_536);
lean::dec(x_527);
if (lean::is_scalar(x_517)) {
 x_539 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_539 = x_517;
 lean::cnstr_set_tag(x_517, 0);
}
lean::cnstr_set(x_539, 0, x_536);
return x_539;
}
else
{
obj* x_540; obj* x_543; obj* x_545; obj* x_548; 
x_540 = lean::cnstr_get(x_527, 0);
lean::inc(x_540);
lean::dec(x_527);
x_543 = lean::cnstr_get(x_540, 0);
lean::inc(x_543);
x_545 = lean::cnstr_get(x_540, 1);
lean::inc(x_545);
lean::dec(x_540);
x_548 = lean::cnstr_get(x_206, 2);
lean::inc(x_548);
if (lean::obj_tag(x_548) == 0)
{
obj* x_552; 
lean::dec(x_341);
lean::dec(x_517);
if (lean::is_scalar(x_220)) {
 x_552 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_552 = x_220;
}
lean::cnstr_set(x_552, 0, x_543);
lean::cnstr_set(x_552, 1, x_545);
x_523 = x_552;
goto lbl_524;
}
else
{
obj* x_553; obj* x_556; obj* x_560; 
x_553 = lean::cnstr_get(x_548, 0);
lean::inc(x_553);
lean::dec(x_548);
x_556 = lean::cnstr_get(x_553, 0);
lean::inc(x_556);
lean::dec(x_553);
lean::inc(x_1);
x_560 = l_lean_elaborator_to__pexpr___main(x_556, x_1, x_545);
if (lean::obj_tag(x_560) == 0)
{
obj* x_570; obj* x_573; 
lean::dec(x_341);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_543);
lean::dec(x_220);
lean::dec(x_214);
lean::dec(x_518);
x_570 = lean::cnstr_get(x_560, 0);
lean::inc(x_570);
lean::dec(x_560);
if (lean::is_scalar(x_517)) {
 x_573 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_573 = x_517;
 lean::cnstr_set_tag(x_517, 0);
}
lean::cnstr_set(x_573, 0, x_570);
return x_573;
}
else
{
obj* x_575; obj* x_578; obj* x_580; obj* x_583; obj* x_584; obj* x_585; obj* x_586; 
lean::dec(x_517);
x_575 = lean::cnstr_get(x_560, 0);
lean::inc(x_575);
lean::dec(x_560);
x_578 = lean::cnstr_get(x_575, 0);
lean::inc(x_578);
x_580 = lean::cnstr_get(x_575, 1);
lean::inc(x_580);
lean::dec(x_575);
x_583 = lean::box(0);
if (lean::is_scalar(x_341)) {
 x_584 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_584 = x_341;
}
lean::cnstr_set(x_584, 0, x_578);
lean::cnstr_set(x_584, 1, x_583);
x_585 = l_list_append___rarg(x_543, x_584);
if (lean::is_scalar(x_220)) {
 x_586 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_586 = x_220;
}
lean::cnstr_set(x_586, 0, x_585);
lean::cnstr_set(x_586, 1, x_580);
x_523 = x_586;
goto lbl_524;
}
}
}
lbl_524:
{
obj* x_587; obj* x_589; obj* x_592; obj* x_593; obj* x_595; obj* x_596; obj* x_598; obj* x_599; uint8 x_600; obj* x_602; obj* x_603; obj* x_606; obj* x_608; obj* x_609; obj* x_611; obj* x_612; obj* x_613; obj* x_615; obj* x_616; obj* x_617; obj* x_618; obj* x_619; 
x_587 = lean::cnstr_get(x_523, 0);
lean::inc(x_587);
x_589 = lean::cnstr_get(x_523, 1);
lean::inc(x_589);
lean::dec(x_523);
x_592 = lean::box(0);
x_593 = lean::mk_nat_obj(0u);
lean::inc(x_518);
x_595 = l_list_length__aux___main___rarg(x_518, x_593);
x_596 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_596);
x_598 = l_lean_kvmap_set__nat(x_592, x_596, x_595);
x_599 = l_lean_elaborator_to__pexpr___main___closed__26;
x_600 = 1;
lean::inc(x_599);
x_602 = l_lean_kvmap_set__bool(x_598, x_599, x_600);
x_603 = lean::cnstr_get(x_206, 1);
lean::inc(x_603);
lean::dec(x_206);
x_606 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_606);
x_608 = l_option_map___rarg(x_606, x_603);
x_609 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_609);
x_611 = l_option_map___rarg(x_609, x_608);
x_612 = l_option_get__or__else___main___rarg(x_611, x_592);
x_613 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_613);
x_615 = l_lean_kvmap_set__name(x_602, x_613, x_612);
x_616 = l_list_append___rarg(x_518, x_587);
x_617 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_616);
x_618 = lean_expr_mk_mdata(x_615, x_617);
if (lean::is_scalar(x_214)) {
 x_619 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_619 = x_214;
}
lean::cnstr_set(x_619, 0, x_618);
lean::cnstr_set(x_619, 1, x_589);
x_14 = x_619;
goto lbl_15;
}
}
}
else
{
obj* x_621; obj* x_622; obj* x_624; obj* x_625; obj* x_628; 
lean::dec(x_339);
x_621 = l_lean_parser_term_struct__inst__item_has__view;
x_622 = lean::cnstr_get(x_621, 1);
lean::inc(x_622);
x_624 = lean::apply_1(x_622, x_342);
x_625 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
lean::inc(x_625);
x_628 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_624, x_625, x_1, x_2);
if (lean::obj_tag(x_628) == 0)
{
obj* x_638; obj* x_640; obj* x_641; 
lean::dec(x_341);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_210);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_638 = lean::cnstr_get(x_628, 0);
lean::inc(x_638);
if (lean::is_exclusive(x_628)) {
 lean::cnstr_release(x_628, 0);
 x_640 = x_628;
} else {
 lean::dec(x_628);
 x_640 = lean::box(0);
}
if (lean::is_scalar(x_640)) {
 x_641 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_641 = x_640;
}
lean::cnstr_set(x_641, 0, x_638);
return x_641;
}
else
{
obj* x_642; obj* x_644; obj* x_645; obj* x_647; obj* x_652; 
x_642 = lean::cnstr_get(x_628, 0);
lean::inc(x_642);
if (lean::is_exclusive(x_628)) {
 lean::cnstr_release(x_628, 0);
 x_644 = x_628;
} else {
 lean::dec(x_628);
 x_644 = lean::box(0);
}
x_645 = lean::cnstr_get(x_642, 0);
lean::inc(x_645);
x_647 = lean::cnstr_get(x_642, 1);
lean::inc(x_647);
lean::dec(x_642);
lean::inc(x_1);
lean::inc(x_0);
x_652 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_210, x_1, x_647);
if (lean::obj_tag(x_652) == 0)
{
obj* x_662; obj* x_665; 
lean::dec(x_341);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_645);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_216);
lean::dec(x_214);
x_662 = lean::cnstr_get(x_652, 0);
lean::inc(x_662);
lean::dec(x_652);
if (lean::is_scalar(x_644)) {
 x_665 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_665 = x_644;
 lean::cnstr_set_tag(x_644, 0);
}
lean::cnstr_set(x_665, 0, x_662);
return x_665;
}
else
{
obj* x_666; obj* x_669; obj* x_671; obj* x_674; obj* x_678; 
x_666 = lean::cnstr_get(x_652, 0);
lean::inc(x_666);
lean::dec(x_652);
x_669 = lean::cnstr_get(x_666, 0);
lean::inc(x_669);
x_671 = lean::cnstr_get(x_666, 1);
lean::inc(x_671);
lean::dec(x_666);
lean::inc(x_1);
lean::inc(x_0);
x_678 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_216, x_1, x_671);
if (lean::obj_tag(x_678) == 0)
{
obj* x_688; obj* x_691; 
lean::dec(x_341);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_645);
lean::dec(x_669);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_214);
x_688 = lean::cnstr_get(x_678, 0);
lean::inc(x_688);
lean::dec(x_678);
if (lean::is_scalar(x_644)) {
 x_691 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_691 = x_644;
 lean::cnstr_set_tag(x_644, 0);
}
lean::cnstr_set(x_691, 0, x_688);
return x_691;
}
else
{
obj* x_692; obj* x_695; obj* x_697; obj* x_700; 
x_692 = lean::cnstr_get(x_678, 0);
lean::inc(x_692);
lean::dec(x_678);
x_695 = lean::cnstr_get(x_692, 0);
lean::inc(x_695);
x_697 = lean::cnstr_get(x_692, 1);
lean::inc(x_697);
lean::dec(x_692);
x_700 = lean::cnstr_get(x_206, 2);
lean::inc(x_700);
if (lean::obj_tag(x_700) == 0)
{
obj* x_704; 
lean::dec(x_341);
lean::dec(x_644);
if (lean::is_scalar(x_220)) {
 x_704 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_704 = x_220;
}
lean::cnstr_set(x_704, 0, x_695);
lean::cnstr_set(x_704, 1, x_697);
x_674 = x_704;
goto lbl_675;
}
else
{
obj* x_705; obj* x_708; obj* x_712; 
x_705 = lean::cnstr_get(x_700, 0);
lean::inc(x_705);
lean::dec(x_700);
x_708 = lean::cnstr_get(x_705, 0);
lean::inc(x_708);
lean::dec(x_705);
lean::inc(x_1);
x_712 = l_lean_elaborator_to__pexpr___main(x_708, x_1, x_697);
if (lean::obj_tag(x_712) == 0)
{
obj* x_723; obj* x_726; 
lean::dec(x_341);
lean::dec(x_7);
lean::dec(x_695);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_645);
lean::dec(x_669);
lean::dec(x_206);
lean::dec(x_220);
lean::dec(x_214);
x_723 = lean::cnstr_get(x_712, 0);
lean::inc(x_723);
lean::dec(x_712);
if (lean::is_scalar(x_644)) {
 x_726 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_726 = x_644;
 lean::cnstr_set_tag(x_644, 0);
}
lean::cnstr_set(x_726, 0, x_723);
return x_726;
}
else
{
obj* x_728; obj* x_731; obj* x_733; obj* x_736; obj* x_737; obj* x_738; obj* x_739; 
lean::dec(x_644);
x_728 = lean::cnstr_get(x_712, 0);
lean::inc(x_728);
lean::dec(x_712);
x_731 = lean::cnstr_get(x_728, 0);
lean::inc(x_731);
x_733 = lean::cnstr_get(x_728, 1);
lean::inc(x_733);
lean::dec(x_728);
x_736 = lean::box(0);
if (lean::is_scalar(x_341)) {
 x_737 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_737 = x_341;
}
lean::cnstr_set(x_737, 0, x_731);
lean::cnstr_set(x_737, 1, x_736);
x_738 = l_list_append___rarg(x_695, x_737);
if (lean::is_scalar(x_220)) {
 x_739 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_739 = x_220;
}
lean::cnstr_set(x_739, 0, x_738);
lean::cnstr_set(x_739, 1, x_733);
x_674 = x_739;
goto lbl_675;
}
}
}
lbl_675:
{
obj* x_740; obj* x_742; obj* x_745; obj* x_746; obj* x_748; obj* x_749; obj* x_751; obj* x_752; uint8 x_753; obj* x_756; obj* x_757; obj* x_760; obj* x_762; obj* x_763; obj* x_765; obj* x_766; obj* x_767; obj* x_769; obj* x_770; obj* x_771; obj* x_772; obj* x_773; 
x_740 = lean::cnstr_get(x_674, 0);
lean::inc(x_740);
x_742 = lean::cnstr_get(x_674, 1);
lean::inc(x_742);
lean::dec(x_674);
x_745 = lean::box(0);
x_746 = lean::mk_nat_obj(0u);
lean::inc(x_669);
x_748 = l_list_length__aux___main___rarg(x_669, x_746);
x_749 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_749);
x_751 = l_lean_kvmap_set__nat(x_745, x_749, x_748);
x_752 = l_lean_elaborator_to__pexpr___main___closed__26;
x_753 = lean::unbox(x_645);
lean::dec(x_645);
lean::inc(x_752);
x_756 = l_lean_kvmap_set__bool(x_751, x_752, x_753);
x_757 = lean::cnstr_get(x_206, 1);
lean::inc(x_757);
lean::dec(x_206);
x_760 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_760);
x_762 = l_option_map___rarg(x_760, x_757);
x_763 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_763);
x_765 = l_option_map___rarg(x_763, x_762);
x_766 = l_option_get__or__else___main___rarg(x_765, x_745);
x_767 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_767);
x_769 = l_lean_kvmap_set__name(x_756, x_767, x_766);
x_770 = l_list_append___rarg(x_669, x_740);
x_771 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_770);
x_772 = lean_expr_mk_mdata(x_769, x_771);
if (lean::is_scalar(x_214)) {
 x_773 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_773 = x_214;
}
lean::cnstr_set(x_773, 0, x_772);
lean::cnstr_set(x_773, 1, x_742);
x_14 = x_773;
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
obj* x_776; 
lean::inc(x_1);
lean::inc(x_9);
x_776 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_9, x_1, x_2);
if (lean::obj_tag(x_776) == 0)
{
obj* x_781; obj* x_783; obj* x_784; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_781 = lean::cnstr_get(x_776, 0);
lean::inc(x_781);
if (lean::is_exclusive(x_776)) {
 lean::cnstr_release(x_776, 0);
 x_783 = x_776;
} else {
 lean::dec(x_776);
 x_783 = lean::box(0);
}
if (lean::is_scalar(x_783)) {
 x_784 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_784 = x_783;
}
lean::cnstr_set(x_784, 0, x_781);
return x_784;
}
else
{
obj* x_785; obj* x_788; obj* x_790; obj* x_792; obj* x_793; obj* x_794; 
x_785 = lean::cnstr_get(x_776, 0);
lean::inc(x_785);
lean::dec(x_776);
x_788 = lean::cnstr_get(x_785, 0);
lean::inc(x_788);
x_790 = lean::cnstr_get(x_785, 1);
lean::inc(x_790);
if (lean::is_exclusive(x_785)) {
 lean::cnstr_release(x_785, 0);
 lean::cnstr_release(x_785, 1);
 x_792 = x_785;
} else {
 lean::dec(x_785);
 x_792 = lean::box(0);
}
x_793 = l_list_reverse___rarg(x_788);
if (lean::is_scalar(x_792)) {
 x_794 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_794 = x_792;
}
lean::cnstr_set(x_794, 0, x_793);
lean::cnstr_set(x_794, 1, x_790);
x_16 = x_794;
goto lbl_17;
}
}
}
else
{
obj* x_797; obj* x_798; obj* x_801; obj* x_802; obj* x_803; obj* x_805; obj* x_806; obj* x_807; 
lean::dec(x_9);
lean::dec(x_7);
x_797 = l_lean_parser_string__lit_has__view;
x_798 = lean::cnstr_get(x_797, 0);
lean::inc(x_798);
lean::inc(x_0);
x_801 = lean::apply_1(x_798, x_0);
x_802 = l_lean_parser_string__lit_view_value(x_801);
x_803 = l_lean_elaborator_to__pexpr___main___closed__31;
lean::inc(x_803);
x_805 = l_option_get__or__else___main___rarg(x_802, x_803);
x_806 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_806, 0, x_805);
x_807 = lean_expr_mk_lit(x_806);
if (x_21 == 0)
{
obj* x_808; 
x_808 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_808) == 0)
{
obj* x_810; obj* x_811; 
lean::dec(x_1);
x_810 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_810, 0, x_807);
lean::cnstr_set(x_810, 1, x_2);
x_811 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_811, 0, x_810);
return x_811;
}
else
{
obj* x_812; obj* x_815; obj* x_818; obj* x_821; obj* x_822; obj* x_823; obj* x_825; obj* x_827; obj* x_828; obj* x_831; obj* x_833; obj* x_834; obj* x_835; obj* x_836; 
x_812 = lean::cnstr_get(x_808, 0);
lean::inc(x_812);
lean::dec(x_808);
x_815 = lean::cnstr_get(x_1, 0);
lean::inc(x_815);
lean::dec(x_1);
x_818 = lean::cnstr_get(x_815, 2);
lean::inc(x_818);
lean::dec(x_815);
x_821 = l_lean_file__map_to__position(x_818, x_812);
x_822 = lean::box(0);
x_823 = lean::cnstr_get(x_821, 1);
lean::inc(x_823);
x_825 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_825);
x_827 = l_lean_kvmap_set__nat(x_822, x_825, x_823);
x_828 = lean::cnstr_get(x_821, 0);
lean::inc(x_828);
lean::dec(x_821);
x_831 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_831);
x_833 = l_lean_kvmap_set__nat(x_827, x_831, x_828);
x_834 = lean_expr_mk_mdata(x_833, x_807);
x_835 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_835, 0, x_834);
lean::cnstr_set(x_835, 1, x_2);
x_836 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_836, 0, x_835);
return x_836;
}
}
else
{
obj* x_839; obj* x_840; 
lean::dec(x_1);
lean::dec(x_0);
x_839 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_839, 0, x_807);
lean::cnstr_set(x_839, 1, x_2);
x_840 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_840, 0, x_839);
return x_840;
}
}
}
else
{
obj* x_843; obj* x_844; obj* x_847; obj* x_848; obj* x_849; obj* x_850; 
lean::dec(x_9);
lean::dec(x_7);
x_843 = l_lean_parser_number_has__view;
x_844 = lean::cnstr_get(x_843, 0);
lean::inc(x_844);
lean::inc(x_0);
x_847 = lean::apply_1(x_844, x_0);
x_848 = l_lean_parser_number_view_to__nat___main(x_847);
x_849 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_849, 0, x_848);
x_850 = lean_expr_mk_lit(x_849);
if (x_21 == 0)
{
obj* x_851; 
x_851 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_851) == 0)
{
obj* x_853; obj* x_854; 
lean::dec(x_1);
x_853 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_853, 0, x_850);
lean::cnstr_set(x_853, 1, x_2);
x_854 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_854, 0, x_853);
return x_854;
}
else
{
obj* x_855; obj* x_858; obj* x_861; obj* x_864; obj* x_865; obj* x_866; obj* x_868; obj* x_870; obj* x_871; obj* x_874; obj* x_876; obj* x_877; obj* x_878; obj* x_879; 
x_855 = lean::cnstr_get(x_851, 0);
lean::inc(x_855);
lean::dec(x_851);
x_858 = lean::cnstr_get(x_1, 0);
lean::inc(x_858);
lean::dec(x_1);
x_861 = lean::cnstr_get(x_858, 2);
lean::inc(x_861);
lean::dec(x_858);
x_864 = l_lean_file__map_to__position(x_861, x_855);
x_865 = lean::box(0);
x_866 = lean::cnstr_get(x_864, 1);
lean::inc(x_866);
x_868 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_868);
x_870 = l_lean_kvmap_set__nat(x_865, x_868, x_866);
x_871 = lean::cnstr_get(x_864, 0);
lean::inc(x_871);
lean::dec(x_864);
x_874 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_874);
x_876 = l_lean_kvmap_set__nat(x_870, x_874, x_871);
x_877 = lean_expr_mk_mdata(x_876, x_850);
x_878 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_878, 0, x_877);
lean::cnstr_set(x_878, 1, x_2);
x_879 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_879, 0, x_878);
return x_879;
}
}
else
{
obj* x_882; obj* x_883; 
lean::dec(x_1);
lean::dec(x_0);
x_882 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_882, 0, x_850);
lean::cnstr_set(x_882, 1, x_2);
x_883 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_883, 0, x_882);
return x_883;
}
}
}
else
{
obj* x_885; obj* x_886; obj* x_889; obj* x_890; obj* x_894; 
lean::dec(x_9);
x_885 = l_lean_parser_term_borrowed_has__view;
x_886 = lean::cnstr_get(x_885, 0);
lean::inc(x_886);
lean::inc(x_0);
x_889 = lean::apply_1(x_886, x_0);
x_890 = lean::cnstr_get(x_889, 1);
lean::inc(x_890);
lean::dec(x_889);
lean::inc(x_1);
x_894 = l_lean_elaborator_to__pexpr___main(x_890, x_1, x_2);
if (lean::obj_tag(x_894) == 0)
{
obj* x_898; obj* x_900; obj* x_901; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_898 = lean::cnstr_get(x_894, 0);
lean::inc(x_898);
if (lean::is_exclusive(x_894)) {
 lean::cnstr_release(x_894, 0);
 x_900 = x_894;
} else {
 lean::dec(x_894);
 x_900 = lean::box(0);
}
if (lean::is_scalar(x_900)) {
 x_901 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_901 = x_900;
}
lean::cnstr_set(x_901, 0, x_898);
return x_901;
}
else
{
obj* x_902; obj* x_905; obj* x_907; obj* x_909; obj* x_910; obj* x_912; obj* x_913; 
x_902 = lean::cnstr_get(x_894, 0);
lean::inc(x_902);
lean::dec(x_894);
x_905 = lean::cnstr_get(x_902, 0);
lean::inc(x_905);
x_907 = lean::cnstr_get(x_902, 1);
lean::inc(x_907);
if (lean::is_exclusive(x_902)) {
 lean::cnstr_release(x_902, 0);
 lean::cnstr_release(x_902, 1);
 x_909 = x_902;
} else {
 lean::dec(x_902);
 x_909 = lean::box(0);
}
x_910 = l_lean_elaborator_to__pexpr___main___closed__32;
lean::inc(x_910);
x_912 = l_lean_elaborator_expr_mk__annotation(x_910, x_905);
if (lean::is_scalar(x_909)) {
 x_913 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_913 = x_909;
}
lean::cnstr_set(x_913, 0, x_912);
lean::cnstr_set(x_913, 1, x_907);
x_14 = x_913;
goto lbl_15;
}
}
}
else
{
obj* x_915; obj* x_916; obj* x_919; obj* x_920; obj* x_924; 
lean::dec(x_9);
x_915 = l_lean_parser_term_inaccessible_has__view;
x_916 = lean::cnstr_get(x_915, 0);
lean::inc(x_916);
lean::inc(x_0);
x_919 = lean::apply_1(x_916, x_0);
x_920 = lean::cnstr_get(x_919, 1);
lean::inc(x_920);
lean::dec(x_919);
lean::inc(x_1);
x_924 = l_lean_elaborator_to__pexpr___main(x_920, x_1, x_2);
if (lean::obj_tag(x_924) == 0)
{
obj* x_928; obj* x_930; obj* x_931; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_928 = lean::cnstr_get(x_924, 0);
lean::inc(x_928);
if (lean::is_exclusive(x_924)) {
 lean::cnstr_release(x_924, 0);
 x_930 = x_924;
} else {
 lean::dec(x_924);
 x_930 = lean::box(0);
}
if (lean::is_scalar(x_930)) {
 x_931 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_931 = x_930;
}
lean::cnstr_set(x_931, 0, x_928);
return x_931;
}
else
{
obj* x_932; obj* x_935; obj* x_937; obj* x_939; obj* x_940; obj* x_942; obj* x_943; 
x_932 = lean::cnstr_get(x_924, 0);
lean::inc(x_932);
lean::dec(x_924);
x_935 = lean::cnstr_get(x_932, 0);
lean::inc(x_935);
x_937 = lean::cnstr_get(x_932, 1);
lean::inc(x_937);
if (lean::is_exclusive(x_932)) {
 lean::cnstr_release(x_932, 0);
 lean::cnstr_release(x_932, 1);
 x_939 = x_932;
} else {
 lean::dec(x_932);
 x_939 = lean::box(0);
}
x_940 = l_lean_elaborator_to__pexpr___main___closed__33;
lean::inc(x_940);
x_942 = l_lean_elaborator_expr_mk__annotation(x_940, x_935);
if (lean::is_scalar(x_939)) {
 x_943 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_943 = x_939;
}
lean::cnstr_set(x_943, 0, x_942);
lean::cnstr_set(x_943, 1, x_937);
x_14 = x_943;
goto lbl_15;
}
}
}
else
{
obj* x_945; obj* x_946; obj* x_949; obj* x_950; obj* x_952; obj* x_953; obj* x_955; obj* x_958; 
lean::dec(x_9);
x_945 = l_lean_parser_term_explicit_has__view;
x_946 = lean::cnstr_get(x_945, 0);
lean::inc(x_946);
lean::inc(x_0);
x_949 = lean::apply_1(x_946, x_0);
x_950 = lean::cnstr_get(x_949, 0);
lean::inc(x_950);
x_952 = l_lean_parser_ident__univs_has__view;
x_953 = lean::cnstr_get(x_952, 1);
lean::inc(x_953);
x_955 = lean::cnstr_get(x_949, 1);
lean::inc(x_955);
lean::dec(x_949);
x_958 = lean::apply_1(x_953, x_955);
if (lean::obj_tag(x_950) == 0)
{
obj* x_961; 
lean::dec(x_950);
lean::inc(x_1);
x_961 = l_lean_elaborator_to__pexpr___main(x_958, x_1, x_2);
if (lean::obj_tag(x_961) == 0)
{
obj* x_965; obj* x_967; obj* x_968; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_965 = lean::cnstr_get(x_961, 0);
lean::inc(x_965);
if (lean::is_exclusive(x_961)) {
 lean::cnstr_release(x_961, 0);
 x_967 = x_961;
} else {
 lean::dec(x_961);
 x_967 = lean::box(0);
}
if (lean::is_scalar(x_967)) {
 x_968 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_968 = x_967;
}
lean::cnstr_set(x_968, 0, x_965);
return x_968;
}
else
{
obj* x_969; obj* x_972; obj* x_974; obj* x_976; obj* x_977; obj* x_979; obj* x_980; 
x_969 = lean::cnstr_get(x_961, 0);
lean::inc(x_969);
lean::dec(x_961);
x_972 = lean::cnstr_get(x_969, 0);
lean::inc(x_972);
x_974 = lean::cnstr_get(x_969, 1);
lean::inc(x_974);
if (lean::is_exclusive(x_969)) {
 lean::cnstr_release(x_969, 0);
 lean::cnstr_release(x_969, 1);
 x_976 = x_969;
} else {
 lean::dec(x_969);
 x_976 = lean::box(0);
}
x_977 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
lean::inc(x_977);
x_979 = l_lean_elaborator_expr_mk__annotation(x_977, x_972);
if (lean::is_scalar(x_976)) {
 x_980 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_980 = x_976;
}
lean::cnstr_set(x_980, 0, x_979);
lean::cnstr_set(x_980, 1, x_974);
x_14 = x_980;
goto lbl_15;
}
}
else
{
obj* x_983; 
lean::dec(x_950);
lean::inc(x_1);
x_983 = l_lean_elaborator_to__pexpr___main(x_958, x_1, x_2);
if (lean::obj_tag(x_983) == 0)
{
obj* x_987; obj* x_989; obj* x_990; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_987 = lean::cnstr_get(x_983, 0);
lean::inc(x_987);
if (lean::is_exclusive(x_983)) {
 lean::cnstr_release(x_983, 0);
 x_989 = x_983;
} else {
 lean::dec(x_983);
 x_989 = lean::box(0);
}
if (lean::is_scalar(x_989)) {
 x_990 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_990 = x_989;
}
lean::cnstr_set(x_990, 0, x_987);
return x_990;
}
else
{
obj* x_991; obj* x_994; obj* x_996; obj* x_998; obj* x_999; obj* x_1001; obj* x_1002; 
x_991 = lean::cnstr_get(x_983, 0);
lean::inc(x_991);
lean::dec(x_983);
x_994 = lean::cnstr_get(x_991, 0);
lean::inc(x_994);
x_996 = lean::cnstr_get(x_991, 1);
lean::inc(x_996);
if (lean::is_exclusive(x_991)) {
 lean::cnstr_release(x_991, 0);
 lean::cnstr_release(x_991, 1);
 x_998 = x_991;
} else {
 lean::dec(x_991);
 x_998 = lean::box(0);
}
x_999 = l_lean_elaborator_to__pexpr___main___closed__34;
lean::inc(x_999);
x_1001 = l_lean_elaborator_expr_mk__annotation(x_999, x_994);
if (lean::is_scalar(x_998)) {
 x_1002 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1002 = x_998;
}
lean::cnstr_set(x_1002, 0, x_1001);
lean::cnstr_set(x_1002, 1, x_996);
x_14 = x_1002;
goto lbl_15;
}
}
}
}
else
{
obj* x_1004; obj* x_1005; obj* x_1008; obj* x_1009; obj* x_1011; 
lean::dec(x_9);
x_1004 = l_lean_parser_term_projection_has__view;
x_1005 = lean::cnstr_get(x_1004, 0);
lean::inc(x_1005);
lean::inc(x_0);
x_1008 = lean::apply_1(x_1005, x_0);
x_1009 = lean::cnstr_get(x_1008, 2);
lean::inc(x_1009);
x_1011 = lean::cnstr_get(x_1008, 0);
lean::inc(x_1011);
lean::dec(x_1008);
if (lean::obj_tag(x_1009) == 0)
{
obj* x_1014; obj* x_1018; 
x_1014 = lean::cnstr_get(x_1009, 0);
lean::inc(x_1014);
lean::dec(x_1009);
lean::inc(x_1);
x_1018 = l_lean_elaborator_to__pexpr___main(x_1011, x_1, x_2);
if (lean::obj_tag(x_1018) == 0)
{
obj* x_1023; obj* x_1025; obj* x_1026; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1014);
x_1023 = lean::cnstr_get(x_1018, 0);
lean::inc(x_1023);
if (lean::is_exclusive(x_1018)) {
 lean::cnstr_release(x_1018, 0);
 x_1025 = x_1018;
} else {
 lean::dec(x_1018);
 x_1025 = lean::box(0);
}
if (lean::is_scalar(x_1025)) {
 x_1026 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1026 = x_1025;
}
lean::cnstr_set(x_1026, 0, x_1023);
return x_1026;
}
else
{
obj* x_1027; obj* x_1030; obj* x_1032; obj* x_1034; obj* x_1035; obj* x_1038; obj* x_1039; obj* x_1040; obj* x_1042; obj* x_1043; obj* x_1044; 
x_1027 = lean::cnstr_get(x_1018, 0);
lean::inc(x_1027);
lean::dec(x_1018);
x_1030 = lean::cnstr_get(x_1027, 0);
lean::inc(x_1030);
x_1032 = lean::cnstr_get(x_1027, 1);
lean::inc(x_1032);
if (lean::is_exclusive(x_1027)) {
 lean::cnstr_release(x_1027, 0);
 lean::cnstr_release(x_1027, 1);
 x_1034 = x_1027;
} else {
 lean::dec(x_1027);
 x_1034 = lean::box(0);
}
x_1035 = lean::cnstr_get(x_1014, 2);
lean::inc(x_1035);
lean::dec(x_1014);
x_1038 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1038, 0, x_1035);
x_1039 = lean::box(0);
x_1040 = l_lean_elaborator_to__pexpr___main___closed__35;
lean::inc(x_1040);
x_1042 = l_lean_kvmap_insert__core___main(x_1039, x_1040, x_1038);
x_1043 = lean_expr_mk_mdata(x_1042, x_1030);
if (lean::is_scalar(x_1034)) {
 x_1044 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1044 = x_1034;
}
lean::cnstr_set(x_1044, 0, x_1043);
lean::cnstr_set(x_1044, 1, x_1032);
x_14 = x_1044;
goto lbl_15;
}
}
else
{
obj* x_1045; obj* x_1049; 
x_1045 = lean::cnstr_get(x_1009, 0);
lean::inc(x_1045);
lean::dec(x_1009);
lean::inc(x_1);
x_1049 = l_lean_elaborator_to__pexpr___main(x_1011, x_1, x_2);
if (lean::obj_tag(x_1049) == 0)
{
obj* x_1054; obj* x_1056; obj* x_1057; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1045);
x_1054 = lean::cnstr_get(x_1049, 0);
lean::inc(x_1054);
if (lean::is_exclusive(x_1049)) {
 lean::cnstr_release(x_1049, 0);
 x_1056 = x_1049;
} else {
 lean::dec(x_1049);
 x_1056 = lean::box(0);
}
if (lean::is_scalar(x_1056)) {
 x_1057 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1057 = x_1056;
}
lean::cnstr_set(x_1057, 0, x_1054);
return x_1057;
}
else
{
obj* x_1058; obj* x_1061; obj* x_1063; obj* x_1065; obj* x_1066; obj* x_1067; obj* x_1068; obj* x_1069; obj* x_1071; obj* x_1072; obj* x_1073; 
x_1058 = lean::cnstr_get(x_1049, 0);
lean::inc(x_1058);
lean::dec(x_1049);
x_1061 = lean::cnstr_get(x_1058, 0);
lean::inc(x_1061);
x_1063 = lean::cnstr_get(x_1058, 1);
lean::inc(x_1063);
if (lean::is_exclusive(x_1058)) {
 lean::cnstr_release(x_1058, 0);
 lean::cnstr_release(x_1058, 1);
 x_1065 = x_1058;
} else {
 lean::dec(x_1058);
 x_1065 = lean::box(0);
}
x_1066 = l_lean_parser_number_view_to__nat___main(x_1045);
x_1067 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1067, 0, x_1066);
x_1068 = lean::box(0);
x_1069 = l_lean_elaborator_to__pexpr___main___closed__35;
lean::inc(x_1069);
x_1071 = l_lean_kvmap_insert__core___main(x_1068, x_1069, x_1067);
x_1072 = lean_expr_mk_mdata(x_1071, x_1061);
if (lean::is_scalar(x_1065)) {
 x_1073 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1073 = x_1065;
}
lean::cnstr_set(x_1073, 0, x_1072);
lean::cnstr_set(x_1073, 1, x_1063);
x_14 = x_1073;
goto lbl_15;
}
}
}
}
else
{
obj* x_1075; obj* x_1076; obj* x_1079; obj* x_1080; 
lean::dec(x_9);
x_1075 = l_lean_parser_term_let_has__view;
x_1076 = lean::cnstr_get(x_1075, 0);
lean::inc(x_1076);
lean::inc(x_0);
x_1079 = lean::apply_1(x_1076, x_0);
x_1080 = lean::cnstr_get(x_1079, 1);
lean::inc(x_1080);
if (lean::obj_tag(x_1080) == 0)
{
obj* x_1082; obj* x_1085; obj* x_1087; obj* x_1089; 
x_1082 = lean::cnstr_get(x_1080, 0);
lean::inc(x_1082);
lean::dec(x_1080);
x_1085 = lean::cnstr_get(x_1082, 0);
lean::inc(x_1085);
x_1087 = lean::cnstr_get(x_1082, 1);
lean::inc(x_1087);
x_1089 = lean::cnstr_get(x_1082, 2);
lean::inc(x_1089);
lean::dec(x_1082);
if (lean::obj_tag(x_1087) == 0)
{
if (lean::obj_tag(x_1089) == 0)
{
obj* x_1094; obj* x_1098; 
lean::dec(x_1079);
lean::dec(x_1085);
x_1094 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_1094);
lean::inc(x_0);
x_1098 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1094, x_1, x_2);
if (lean::obj_tag(x_1098) == 0)
{
obj* x_1102; obj* x_1104; obj* x_1105; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1102 = lean::cnstr_get(x_1098, 0);
lean::inc(x_1102);
if (lean::is_exclusive(x_1098)) {
 lean::cnstr_release(x_1098, 0);
 x_1104 = x_1098;
} else {
 lean::dec(x_1098);
 x_1104 = lean::box(0);
}
if (lean::is_scalar(x_1104)) {
 x_1105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1105 = x_1104;
}
lean::cnstr_set(x_1105, 0, x_1102);
return x_1105;
}
else
{
obj* x_1106; 
x_1106 = lean::cnstr_get(x_1098, 0);
lean::inc(x_1106);
lean::dec(x_1098);
x_14 = x_1106;
goto lbl_15;
}
}
else
{
obj* x_1109; obj* x_1112; obj* x_1116; 
x_1109 = lean::cnstr_get(x_1089, 0);
lean::inc(x_1109);
lean::dec(x_1089);
x_1112 = lean::cnstr_get(x_1109, 1);
lean::inc(x_1112);
lean::dec(x_1109);
lean::inc(x_1);
x_1116 = l_lean_elaborator_to__pexpr___main(x_1112, x_1, x_2);
if (lean::obj_tag(x_1116) == 0)
{
obj* x_1122; obj* x_1124; obj* x_1125; 
lean::dec(x_1079);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1085);
x_1122 = lean::cnstr_get(x_1116, 0);
lean::inc(x_1122);
if (lean::is_exclusive(x_1116)) {
 lean::cnstr_release(x_1116, 0);
 x_1124 = x_1116;
} else {
 lean::dec(x_1116);
 x_1124 = lean::box(0);
}
if (lean::is_scalar(x_1124)) {
 x_1125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1125 = x_1124;
}
lean::cnstr_set(x_1125, 0, x_1122);
return x_1125;
}
else
{
obj* x_1126; obj* x_1128; obj* x_1129; obj* x_1131; obj* x_1133; obj* x_1134; obj* x_1137; 
x_1126 = lean::cnstr_get(x_1116, 0);
lean::inc(x_1126);
if (lean::is_exclusive(x_1116)) {
 lean::cnstr_release(x_1116, 0);
 x_1128 = x_1116;
} else {
 lean::dec(x_1116);
 x_1128 = lean::box(0);
}
x_1129 = lean::cnstr_get(x_1126, 0);
lean::inc(x_1129);
x_1131 = lean::cnstr_get(x_1126, 1);
lean::inc(x_1131);
if (lean::is_exclusive(x_1126)) {
 lean::cnstr_release(x_1126, 0);
 lean::cnstr_release(x_1126, 1);
 x_1133 = x_1126;
} else {
 lean::dec(x_1126);
 x_1133 = lean::box(0);
}
x_1134 = lean::cnstr_get(x_1079, 3);
lean::inc(x_1134);
lean::inc(x_1);
x_1137 = l_lean_elaborator_to__pexpr___main(x_1134, x_1, x_1131);
if (lean::obj_tag(x_1137) == 0)
{
obj* x_1145; obj* x_1148; 
lean::dec(x_1133);
lean::dec(x_1129);
lean::dec(x_1079);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1085);
x_1145 = lean::cnstr_get(x_1137, 0);
lean::inc(x_1145);
lean::dec(x_1137);
if (lean::is_scalar(x_1128)) {
 x_1148 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1148 = x_1128;
 lean::cnstr_set_tag(x_1128, 0);
}
lean::cnstr_set(x_1148, 0, x_1145);
return x_1148;
}
else
{
obj* x_1149; obj* x_1152; obj* x_1154; obj* x_1157; obj* x_1161; 
x_1149 = lean::cnstr_get(x_1137, 0);
lean::inc(x_1149);
lean::dec(x_1137);
x_1152 = lean::cnstr_get(x_1149, 0);
lean::inc(x_1152);
x_1154 = lean::cnstr_get(x_1149, 1);
lean::inc(x_1154);
lean::dec(x_1149);
x_1157 = lean::cnstr_get(x_1079, 5);
lean::inc(x_1157);
lean::dec(x_1079);
lean::inc(x_1);
x_1161 = l_lean_elaborator_to__pexpr___main(x_1157, x_1, x_1154);
if (lean::obj_tag(x_1161) == 0)
{
obj* x_1169; obj* x_1172; 
lean::dec(x_1133);
lean::dec(x_1129);
lean::dec(x_1152);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1085);
x_1169 = lean::cnstr_get(x_1161, 0);
lean::inc(x_1169);
lean::dec(x_1161);
if (lean::is_scalar(x_1128)) {
 x_1172 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1172 = x_1128;
 lean::cnstr_set_tag(x_1128, 0);
}
lean::cnstr_set(x_1172, 0, x_1169);
return x_1172;
}
else
{
obj* x_1174; obj* x_1177; obj* x_1179; obj* x_1182; obj* x_1183; obj* x_1184; 
lean::dec(x_1128);
x_1174 = lean::cnstr_get(x_1161, 0);
lean::inc(x_1174);
lean::dec(x_1161);
x_1177 = lean::cnstr_get(x_1174, 0);
lean::inc(x_1177);
x_1179 = lean::cnstr_get(x_1174, 1);
lean::inc(x_1179);
lean::dec(x_1174);
x_1182 = l_lean_elaborator_mangle__ident(x_1085);
x_1183 = lean_expr_mk_let(x_1182, x_1129, x_1152, x_1177);
if (lean::is_scalar(x_1133)) {
 x_1184 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1184 = x_1133;
}
lean::cnstr_set(x_1184, 0, x_1183);
lean::cnstr_set(x_1184, 1, x_1179);
x_14 = x_1184;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1189; obj* x_1193; 
lean::dec(x_1079);
lean::dec(x_1089);
lean::dec(x_1085);
lean::dec(x_1087);
x_1189 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_1189);
lean::inc(x_0);
x_1193 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1189, x_1, x_2);
if (lean::obj_tag(x_1193) == 0)
{
obj* x_1197; obj* x_1199; obj* x_1200; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1197 = lean::cnstr_get(x_1193, 0);
lean::inc(x_1197);
if (lean::is_exclusive(x_1193)) {
 lean::cnstr_release(x_1193, 0);
 x_1199 = x_1193;
} else {
 lean::dec(x_1193);
 x_1199 = lean::box(0);
}
if (lean::is_scalar(x_1199)) {
 x_1200 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1200 = x_1199;
}
lean::cnstr_set(x_1200, 0, x_1197);
return x_1200;
}
else
{
obj* x_1201; 
x_1201 = lean::cnstr_get(x_1193, 0);
lean::inc(x_1201);
lean::dec(x_1193);
x_14 = x_1201;
goto lbl_15;
}
}
}
else
{
obj* x_1206; obj* x_1210; 
lean::dec(x_1079);
lean::dec(x_1080);
x_1206 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_1206);
lean::inc(x_0);
x_1210 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1206, x_1, x_2);
if (lean::obj_tag(x_1210) == 0)
{
obj* x_1214; obj* x_1216; obj* x_1217; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1214 = lean::cnstr_get(x_1210, 0);
lean::inc(x_1214);
if (lean::is_exclusive(x_1210)) {
 lean::cnstr_release(x_1210, 0);
 x_1216 = x_1210;
} else {
 lean::dec(x_1210);
 x_1216 = lean::box(0);
}
if (lean::is_scalar(x_1216)) {
 x_1217 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1217 = x_1216;
}
lean::cnstr_set(x_1217, 0, x_1214);
return x_1217;
}
else
{
obj* x_1218; 
x_1218 = lean::cnstr_get(x_1210, 0);
lean::inc(x_1218);
lean::dec(x_1210);
x_14 = x_1218;
goto lbl_15;
}
}
}
}
else
{
obj* x_1222; obj* x_1223; obj* x_1226; obj* x_1227; obj* x_1230; 
lean::dec(x_9);
x_1222 = l_lean_parser_term_show_has__view;
x_1223 = lean::cnstr_get(x_1222, 0);
lean::inc(x_1223);
lean::inc(x_0);
x_1226 = lean::apply_1(x_1223, x_0);
x_1227 = lean::cnstr_get(x_1226, 1);
lean::inc(x_1227);
lean::inc(x_1);
x_1230 = l_lean_elaborator_to__pexpr___main(x_1227, x_1, x_2);
if (lean::obj_tag(x_1230) == 0)
{
obj* x_1235; obj* x_1237; obj* x_1238; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1226);
x_1235 = lean::cnstr_get(x_1230, 0);
lean::inc(x_1235);
if (lean::is_exclusive(x_1230)) {
 lean::cnstr_release(x_1230, 0);
 x_1237 = x_1230;
} else {
 lean::dec(x_1230);
 x_1237 = lean::box(0);
}
if (lean::is_scalar(x_1237)) {
 x_1238 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1238 = x_1237;
}
lean::cnstr_set(x_1238, 0, x_1235);
return x_1238;
}
else
{
obj* x_1239; obj* x_1241; obj* x_1242; obj* x_1244; obj* x_1246; obj* x_1247; obj* x_1250; obj* x_1254; 
x_1239 = lean::cnstr_get(x_1230, 0);
lean::inc(x_1239);
if (lean::is_exclusive(x_1230)) {
 lean::cnstr_release(x_1230, 0);
 x_1241 = x_1230;
} else {
 lean::dec(x_1230);
 x_1241 = lean::box(0);
}
x_1242 = lean::cnstr_get(x_1239, 0);
lean::inc(x_1242);
x_1244 = lean::cnstr_get(x_1239, 1);
lean::inc(x_1244);
if (lean::is_exclusive(x_1239)) {
 lean::cnstr_release(x_1239, 0);
 lean::cnstr_release(x_1239, 1);
 x_1246 = x_1239;
} else {
 lean::dec(x_1239);
 x_1246 = lean::box(0);
}
x_1247 = lean::cnstr_get(x_1226, 3);
lean::inc(x_1247);
lean::dec(x_1226);
x_1250 = lean::cnstr_get(x_1247, 1);
lean::inc(x_1250);
lean::dec(x_1247);
lean::inc(x_1);
x_1254 = l_lean_elaborator_to__pexpr___main(x_1250, x_1, x_1244);
if (lean::obj_tag(x_1254) == 0)
{
obj* x_1260; obj* x_1263; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1242);
lean::dec(x_1246);
x_1260 = lean::cnstr_get(x_1254, 0);
lean::inc(x_1260);
lean::dec(x_1254);
if (lean::is_scalar(x_1241)) {
 x_1263 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1263 = x_1241;
 lean::cnstr_set_tag(x_1241, 0);
}
lean::cnstr_set(x_1263, 0, x_1260);
return x_1263;
}
else
{
obj* x_1265; obj* x_1268; obj* x_1270; obj* x_1273; uint8 x_1274; obj* x_1275; obj* x_1278; obj* x_1279; obj* x_1280; obj* x_1282; obj* x_1283; 
lean::dec(x_1241);
x_1265 = lean::cnstr_get(x_1254, 0);
lean::inc(x_1265);
lean::dec(x_1254);
x_1268 = lean::cnstr_get(x_1265, 0);
lean::inc(x_1268);
x_1270 = lean::cnstr_get(x_1265, 1);
lean::inc(x_1270);
lean::dec(x_1265);
x_1273 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1274 = 0;
x_1275 = l_lean_elaborator_to__pexpr___main___closed__38;
lean::inc(x_1275);
lean::inc(x_1273);
x_1278 = lean_expr_mk_lambda(x_1273, x_1274, x_1242, x_1275);
x_1279 = lean_expr_mk_app(x_1278, x_1268);
x_1280 = l_lean_elaborator_to__pexpr___main___closed__39;
lean::inc(x_1280);
x_1282 = l_lean_elaborator_expr_mk__annotation(x_1280, x_1279);
if (lean::is_scalar(x_1246)) {
 x_1283 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1283 = x_1246;
}
lean::cnstr_set(x_1283, 0, x_1282);
lean::cnstr_set(x_1283, 1, x_1270);
x_14 = x_1283;
goto lbl_15;
}
}
}
}
else
{
obj* x_1285; obj* x_1286; obj* x_1289; obj* x_1290; obj* x_1292; obj* x_1295; 
lean::dec(x_9);
x_1285 = l_lean_parser_term_have_has__view;
x_1286 = lean::cnstr_get(x_1285, 0);
lean::inc(x_1286);
lean::inc(x_0);
x_1289 = lean::apply_1(x_1286, x_0);
x_1292 = lean::cnstr_get(x_1289, 2);
lean::inc(x_1292);
lean::inc(x_1);
x_1295 = l_lean_elaborator_to__pexpr___main(x_1292, x_1, x_2);
if (lean::obj_tag(x_1295) == 0)
{
obj* x_1300; obj* x_1302; obj* x_1303; 
lean::dec(x_1289);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1300 = lean::cnstr_get(x_1295, 0);
lean::inc(x_1300);
if (lean::is_exclusive(x_1295)) {
 lean::cnstr_release(x_1295, 0);
 x_1302 = x_1295;
} else {
 lean::dec(x_1295);
 x_1302 = lean::box(0);
}
if (lean::is_scalar(x_1302)) {
 x_1303 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1303 = x_1302;
}
lean::cnstr_set(x_1303, 0, x_1300);
return x_1303;
}
else
{
obj* x_1304; obj* x_1306; obj* x_1307; obj* x_1309; obj* x_1311; obj* x_1312; obj* x_1315; 
x_1304 = lean::cnstr_get(x_1295, 0);
lean::inc(x_1304);
if (lean::is_exclusive(x_1295)) {
 lean::cnstr_release(x_1295, 0);
 x_1306 = x_1295;
} else {
 lean::dec(x_1295);
 x_1306 = lean::box(0);
}
x_1307 = lean::cnstr_get(x_1304, 0);
lean::inc(x_1307);
x_1309 = lean::cnstr_get(x_1304, 1);
lean::inc(x_1309);
if (lean::is_exclusive(x_1304)) {
 lean::cnstr_release(x_1304, 0);
 lean::cnstr_release(x_1304, 1);
 x_1311 = x_1304;
} else {
 lean::dec(x_1304);
 x_1311 = lean::box(0);
}
x_1312 = lean::cnstr_get(x_1289, 5);
lean::inc(x_1312);
lean::inc(x_1);
x_1315 = l_lean_elaborator_to__pexpr___main(x_1312, x_1, x_1309);
if (lean::obj_tag(x_1315) == 0)
{
obj* x_1322; obj* x_1325; 
lean::dec(x_1289);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1307);
lean::dec(x_1311);
x_1322 = lean::cnstr_get(x_1315, 0);
lean::inc(x_1322);
lean::dec(x_1315);
if (lean::is_scalar(x_1306)) {
 x_1325 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1325 = x_1306;
 lean::cnstr_set_tag(x_1306, 0);
}
lean::cnstr_set(x_1325, 0, x_1322);
return x_1325;
}
else
{
obj* x_1327; obj* x_1330; obj* x_1332; obj* x_1335; obj* x_1337; obj* x_1339; obj* x_1340; obj* x_1342; obj* x_1343; obj* x_1345; uint8 x_1346; obj* x_1347; obj* x_1348; 
lean::dec(x_1306);
x_1327 = lean::cnstr_get(x_1315, 0);
lean::inc(x_1327);
lean::dec(x_1315);
x_1330 = lean::cnstr_get(x_1327, 0);
lean::inc(x_1330);
x_1332 = lean::cnstr_get(x_1327, 1);
lean::inc(x_1332);
lean::dec(x_1327);
x_1335 = lean::cnstr_get(x_1289, 1);
lean::inc(x_1335);
x_1337 = l_lean_elaborator_to__pexpr___main___closed__41;
lean::inc(x_1337);
x_1339 = l_option_map___rarg(x_1337, x_1335);
x_1340 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_1340);
x_1342 = l_option_map___rarg(x_1340, x_1339);
x_1343 = l_lean_elaborator_to__pexpr___main___closed__37;
lean::inc(x_1343);
x_1345 = l_option_get__or__else___main___rarg(x_1342, x_1343);
x_1346 = 0;
x_1347 = lean_expr_mk_lambda(x_1345, x_1346, x_1307, x_1330);
if (lean::is_scalar(x_1311)) {
 x_1348 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1348 = x_1311;
}
lean::cnstr_set(x_1348, 0, x_1347);
lean::cnstr_set(x_1348, 1, x_1332);
x_1290 = x_1348;
goto lbl_1291;
}
}
lbl_1291:
{
obj* x_1349; obj* x_1351; obj* x_1353; obj* x_1354; 
x_1349 = lean::cnstr_get(x_1290, 0);
lean::inc(x_1349);
x_1351 = lean::cnstr_get(x_1290, 1);
lean::inc(x_1351);
if (lean::is_exclusive(x_1290)) {
 lean::cnstr_release(x_1290, 0);
 lean::cnstr_release(x_1290, 1);
 x_1353 = x_1290;
} else {
 lean::dec(x_1290);
 x_1353 = lean::box(0);
}
x_1354 = lean::cnstr_get(x_1289, 3);
lean::inc(x_1354);
lean::dec(x_1289);
if (lean::obj_tag(x_1354) == 0)
{
obj* x_1357; obj* x_1360; obj* x_1364; 
x_1357 = lean::cnstr_get(x_1354, 0);
lean::inc(x_1357);
lean::dec(x_1354);
x_1360 = lean::cnstr_get(x_1357, 1);
lean::inc(x_1360);
lean::dec(x_1357);
lean::inc(x_1);
x_1364 = l_lean_elaborator_to__pexpr___main(x_1360, x_1, x_1351);
if (lean::obj_tag(x_1364) == 0)
{
obj* x_1370; obj* x_1372; obj* x_1373; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1349);
lean::dec(x_1353);
x_1370 = lean::cnstr_get(x_1364, 0);
lean::inc(x_1370);
if (lean::is_exclusive(x_1364)) {
 lean::cnstr_release(x_1364, 0);
 x_1372 = x_1364;
} else {
 lean::dec(x_1364);
 x_1372 = lean::box(0);
}
if (lean::is_scalar(x_1372)) {
 x_1373 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1373 = x_1372;
}
lean::cnstr_set(x_1373, 0, x_1370);
return x_1373;
}
else
{
obj* x_1374; obj* x_1377; obj* x_1379; obj* x_1382; obj* x_1384; obj* x_1385; obj* x_1386; 
x_1374 = lean::cnstr_get(x_1364, 0);
lean::inc(x_1374);
lean::dec(x_1364);
x_1377 = lean::cnstr_get(x_1374, 0);
lean::inc(x_1377);
x_1379 = lean::cnstr_get(x_1374, 1);
lean::inc(x_1379);
lean::dec(x_1374);
x_1382 = l_lean_elaborator_to__pexpr___main___closed__40;
lean::inc(x_1382);
x_1384 = l_lean_elaborator_expr_mk__annotation(x_1382, x_1349);
x_1385 = lean_expr_mk_app(x_1384, x_1377);
if (lean::is_scalar(x_1353)) {
 x_1386 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1386 = x_1353;
}
lean::cnstr_set(x_1386, 0, x_1385);
lean::cnstr_set(x_1386, 1, x_1379);
x_14 = x_1386;
goto lbl_15;
}
}
else
{
obj* x_1387; obj* x_1390; obj* x_1393; obj* x_1397; 
x_1387 = lean::cnstr_get(x_1354, 0);
lean::inc(x_1387);
lean::dec(x_1354);
x_1390 = lean::cnstr_get(x_1387, 1);
lean::inc(x_1390);
lean::dec(x_1387);
x_1393 = lean::cnstr_get(x_1390, 1);
lean::inc(x_1393);
lean::dec(x_1390);
lean::inc(x_1);
x_1397 = l_lean_elaborator_to__pexpr___main(x_1393, x_1, x_1351);
if (lean::obj_tag(x_1397) == 0)
{
obj* x_1403; obj* x_1405; obj* x_1406; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1349);
lean::dec(x_1353);
x_1403 = lean::cnstr_get(x_1397, 0);
lean::inc(x_1403);
if (lean::is_exclusive(x_1397)) {
 lean::cnstr_release(x_1397, 0);
 x_1405 = x_1397;
} else {
 lean::dec(x_1397);
 x_1405 = lean::box(0);
}
if (lean::is_scalar(x_1405)) {
 x_1406 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1406 = x_1405;
}
lean::cnstr_set(x_1406, 0, x_1403);
return x_1406;
}
else
{
obj* x_1407; obj* x_1410; obj* x_1412; obj* x_1415; obj* x_1417; obj* x_1418; obj* x_1419; 
x_1407 = lean::cnstr_get(x_1397, 0);
lean::inc(x_1407);
lean::dec(x_1397);
x_1410 = lean::cnstr_get(x_1407, 0);
lean::inc(x_1410);
x_1412 = lean::cnstr_get(x_1407, 1);
lean::inc(x_1412);
lean::dec(x_1407);
x_1415 = l_lean_elaborator_to__pexpr___main___closed__40;
lean::inc(x_1415);
x_1417 = l_lean_elaborator_expr_mk__annotation(x_1415, x_1349);
x_1418 = lean_expr_mk_app(x_1417, x_1410);
if (lean::is_scalar(x_1353)) {
 x_1419 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1419 = x_1353;
}
lean::cnstr_set(x_1419, 0, x_1418);
lean::cnstr_set(x_1419, 1, x_1412);
x_14 = x_1419;
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
obj* x_1422; 
x_1422 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1422) == 0)
{
obj* x_1424; obj* x_1426; obj* x_1427; 
lean::dec(x_1);
x_1424 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_1424);
x_1426 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1426, 0, x_1424);
lean::cnstr_set(x_1426, 1, x_2);
x_1427 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1427, 0, x_1426);
return x_1427;
}
else
{
obj* x_1428; obj* x_1431; obj* x_1434; obj* x_1437; obj* x_1438; obj* x_1439; obj* x_1441; obj* x_1443; obj* x_1444; obj* x_1447; obj* x_1449; obj* x_1450; obj* x_1452; obj* x_1453; obj* x_1454; 
x_1428 = lean::cnstr_get(x_1422, 0);
lean::inc(x_1428);
lean::dec(x_1422);
x_1431 = lean::cnstr_get(x_1, 0);
lean::inc(x_1431);
lean::dec(x_1);
x_1434 = lean::cnstr_get(x_1431, 2);
lean::inc(x_1434);
lean::dec(x_1431);
x_1437 = l_lean_file__map_to__position(x_1434, x_1428);
x_1438 = lean::box(0);
x_1439 = lean::cnstr_get(x_1437, 1);
lean::inc(x_1439);
x_1441 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1441);
x_1443 = l_lean_kvmap_set__nat(x_1438, x_1441, x_1439);
x_1444 = lean::cnstr_get(x_1437, 0);
lean::inc(x_1444);
lean::dec(x_1437);
x_1447 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1447);
x_1449 = l_lean_kvmap_set__nat(x_1443, x_1447, x_1444);
x_1450 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_1450);
x_1452 = lean_expr_mk_mdata(x_1449, x_1450);
x_1453 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1453, 0, x_1452);
lean::cnstr_set(x_1453, 1, x_2);
x_1454 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1454, 0, x_1453);
return x_1454;
}
}
else
{
obj* x_1457; obj* x_1459; obj* x_1460; 
lean::dec(x_1);
lean::dec(x_0);
x_1457 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_1457);
x_1459 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1459, 0, x_1457);
lean::cnstr_set(x_1459, 1, x_2);
x_1460 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1460, 0, x_1459);
return x_1460;
}
}
}
else
{
obj* x_1462; obj* x_1463; obj* x_1466; obj* x_1467; obj* x_1470; obj* x_1471; obj* x_1473; obj* x_1475; 
lean::dec(x_9);
x_1462 = l_lean_parser_term_anonymous__constructor_has__view;
x_1463 = lean::cnstr_get(x_1462, 0);
lean::inc(x_1463);
lean::inc(x_0);
x_1466 = lean::apply_1(x_1463, x_0);
x_1467 = lean::cnstr_get(x_1466, 1);
lean::inc(x_1467);
lean::dec(x_1466);
x_1470 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_1467);
x_1471 = l_lean_expander_get__opt__type___main___closed__1;
lean::inc(x_1471);
x_1473 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_1471, x_1470);
lean::inc(x_1);
x_1475 = l_lean_elaborator_to__pexpr___main(x_1473, x_1, x_2);
if (lean::obj_tag(x_1475) == 0)
{
obj* x_1479; obj* x_1481; obj* x_1482; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1479 = lean::cnstr_get(x_1475, 0);
lean::inc(x_1479);
if (lean::is_exclusive(x_1475)) {
 lean::cnstr_release(x_1475, 0);
 x_1481 = x_1475;
} else {
 lean::dec(x_1475);
 x_1481 = lean::box(0);
}
if (lean::is_scalar(x_1481)) {
 x_1482 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1482 = x_1481;
}
lean::cnstr_set(x_1482, 0, x_1479);
return x_1482;
}
else
{
obj* x_1483; obj* x_1486; obj* x_1488; obj* x_1490; obj* x_1491; obj* x_1493; obj* x_1494; 
x_1483 = lean::cnstr_get(x_1475, 0);
lean::inc(x_1483);
lean::dec(x_1475);
x_1486 = lean::cnstr_get(x_1483, 0);
lean::inc(x_1486);
x_1488 = lean::cnstr_get(x_1483, 1);
lean::inc(x_1488);
if (lean::is_exclusive(x_1483)) {
 lean::cnstr_release(x_1483, 0);
 lean::cnstr_release(x_1483, 1);
 x_1490 = x_1483;
} else {
 lean::dec(x_1483);
 x_1490 = lean::box(0);
}
x_1491 = l_lean_elaborator_to__pexpr___main___closed__43;
lean::inc(x_1491);
x_1493 = l_lean_elaborator_expr_mk__annotation(x_1491, x_1486);
if (lean::is_scalar(x_1490)) {
 x_1494 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1494 = x_1490;
}
lean::cnstr_set(x_1494, 0, x_1493);
lean::cnstr_set(x_1494, 1, x_1488);
x_14 = x_1494;
goto lbl_15;
}
}
}
else
{
obj* x_1496; obj* x_1497; obj* x_1500; obj* x_1501; obj* x_1502; obj* x_1504; obj* x_1506; 
lean::dec(x_9);
x_1496 = l_lean_parser_term_sort__app_has__view;
x_1497 = lean::cnstr_get(x_1496, 0);
lean::inc(x_1497);
lean::inc(x_0);
x_1500 = lean::apply_1(x_1497, x_0);
x_1501 = l_lean_parser_term_sort_has__view;
x_1502 = lean::cnstr_get(x_1501, 0);
lean::inc(x_1502);
x_1504 = lean::cnstr_get(x_1500, 0);
lean::inc(x_1504);
x_1506 = lean::apply_1(x_1502, x_1504);
if (lean::obj_tag(x_1506) == 0)
{
obj* x_1508; obj* x_1512; 
lean::dec(x_1506);
x_1508 = lean::cnstr_get(x_1500, 1);
lean::inc(x_1508);
lean::dec(x_1500);
lean::inc(x_1);
x_1512 = l_lean_elaborator_to__level___main(x_1508, x_1, x_2);
if (lean::obj_tag(x_1512) == 0)
{
obj* x_1516; obj* x_1518; obj* x_1519; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1516 = lean::cnstr_get(x_1512, 0);
lean::inc(x_1516);
if (lean::is_exclusive(x_1512)) {
 lean::cnstr_release(x_1512, 0);
 x_1518 = x_1512;
} else {
 lean::dec(x_1512);
 x_1518 = lean::box(0);
}
if (lean::is_scalar(x_1518)) {
 x_1519 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1519 = x_1518;
}
lean::cnstr_set(x_1519, 0, x_1516);
return x_1519;
}
else
{
obj* x_1520; obj* x_1523; obj* x_1525; obj* x_1527; obj* x_1528; obj* x_1529; 
x_1520 = lean::cnstr_get(x_1512, 0);
lean::inc(x_1520);
lean::dec(x_1512);
x_1523 = lean::cnstr_get(x_1520, 0);
lean::inc(x_1523);
x_1525 = lean::cnstr_get(x_1520, 1);
lean::inc(x_1525);
if (lean::is_exclusive(x_1520)) {
 lean::cnstr_release(x_1520, 0);
 lean::cnstr_release(x_1520, 1);
 x_1527 = x_1520;
} else {
 lean::dec(x_1520);
 x_1527 = lean::box(0);
}
x_1528 = lean_expr_mk_sort(x_1523);
if (lean::is_scalar(x_1527)) {
 x_1529 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1529 = x_1527;
}
lean::cnstr_set(x_1529, 0, x_1528);
lean::cnstr_set(x_1529, 1, x_1525);
x_14 = x_1529;
goto lbl_15;
}
}
else
{
obj* x_1531; obj* x_1535; 
lean::dec(x_1506);
x_1531 = lean::cnstr_get(x_1500, 1);
lean::inc(x_1531);
lean::dec(x_1500);
lean::inc(x_1);
x_1535 = l_lean_elaborator_to__level___main(x_1531, x_1, x_2);
if (lean::obj_tag(x_1535) == 0)
{
obj* x_1539; obj* x_1541; obj* x_1542; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1539 = lean::cnstr_get(x_1535, 0);
lean::inc(x_1539);
if (lean::is_exclusive(x_1535)) {
 lean::cnstr_release(x_1535, 0);
 x_1541 = x_1535;
} else {
 lean::dec(x_1535);
 x_1541 = lean::box(0);
}
if (lean::is_scalar(x_1541)) {
 x_1542 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1542 = x_1541;
}
lean::cnstr_set(x_1542, 0, x_1539);
return x_1542;
}
else
{
obj* x_1543; obj* x_1546; obj* x_1548; obj* x_1550; obj* x_1551; obj* x_1552; obj* x_1553; 
x_1543 = lean::cnstr_get(x_1535, 0);
lean::inc(x_1543);
lean::dec(x_1535);
x_1546 = lean::cnstr_get(x_1543, 0);
lean::inc(x_1546);
x_1548 = lean::cnstr_get(x_1543, 1);
lean::inc(x_1548);
if (lean::is_exclusive(x_1543)) {
 lean::cnstr_release(x_1543, 0);
 lean::cnstr_release(x_1543, 1);
 x_1550 = x_1543;
} else {
 lean::dec(x_1543);
 x_1550 = lean::box(0);
}
x_1551 = level_mk_succ(x_1546);
x_1552 = lean_expr_mk_sort(x_1551);
if (lean::is_scalar(x_1550)) {
 x_1553 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1553 = x_1550;
}
lean::cnstr_set(x_1553, 0, x_1552);
lean::cnstr_set(x_1553, 1, x_1548);
x_14 = x_1553;
goto lbl_15;
}
}
}
}
else
{
obj* x_1556; obj* x_1557; obj* x_1560; 
lean::dec(x_9);
lean::dec(x_7);
x_1556 = l_lean_parser_term_sort_has__view;
x_1557 = lean::cnstr_get(x_1556, 0);
lean::inc(x_1557);
lean::inc(x_0);
x_1560 = lean::apply_1(x_1557, x_0);
if (lean::obj_tag(x_1560) == 0)
{
lean::dec(x_1560);
if (x_21 == 0)
{
obj* x_1562; 
x_1562 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1562) == 0)
{
obj* x_1564; obj* x_1566; obj* x_1567; 
lean::dec(x_1);
x_1564 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_1564);
x_1566 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1566, 0, x_1564);
lean::cnstr_set(x_1566, 1, x_2);
x_1567 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1567, 0, x_1566);
return x_1567;
}
else
{
obj* x_1568; obj* x_1571; obj* x_1574; obj* x_1577; obj* x_1578; obj* x_1579; obj* x_1581; obj* x_1583; obj* x_1584; obj* x_1587; obj* x_1589; obj* x_1590; obj* x_1592; obj* x_1593; obj* x_1594; 
x_1568 = lean::cnstr_get(x_1562, 0);
lean::inc(x_1568);
lean::dec(x_1562);
x_1571 = lean::cnstr_get(x_1, 0);
lean::inc(x_1571);
lean::dec(x_1);
x_1574 = lean::cnstr_get(x_1571, 2);
lean::inc(x_1574);
lean::dec(x_1571);
x_1577 = l_lean_file__map_to__position(x_1574, x_1568);
x_1578 = lean::box(0);
x_1579 = lean::cnstr_get(x_1577, 1);
lean::inc(x_1579);
x_1581 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1581);
x_1583 = l_lean_kvmap_set__nat(x_1578, x_1581, x_1579);
x_1584 = lean::cnstr_get(x_1577, 0);
lean::inc(x_1584);
lean::dec(x_1577);
x_1587 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1587);
x_1589 = l_lean_kvmap_set__nat(x_1583, x_1587, x_1584);
x_1590 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_1590);
x_1592 = lean_expr_mk_mdata(x_1589, x_1590);
x_1593 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1593, 0, x_1592);
lean::cnstr_set(x_1593, 1, x_2);
x_1594 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1594, 0, x_1593);
return x_1594;
}
}
else
{
obj* x_1597; obj* x_1599; obj* x_1600; 
lean::dec(x_1);
lean::dec(x_0);
x_1597 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_1597);
x_1599 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1599, 0, x_1597);
lean::cnstr_set(x_1599, 1, x_2);
x_1600 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1600, 0, x_1599);
return x_1600;
}
}
else
{
lean::dec(x_1560);
if (x_21 == 0)
{
obj* x_1602; 
x_1602 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1602) == 0)
{
obj* x_1604; obj* x_1606; obj* x_1607; 
lean::dec(x_1);
x_1604 = l_lean_elaborator_to__pexpr___main___closed__44;
lean::inc(x_1604);
x_1606 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1606, 0, x_1604);
lean::cnstr_set(x_1606, 1, x_2);
x_1607 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1607, 0, x_1606);
return x_1607;
}
else
{
obj* x_1608; obj* x_1611; obj* x_1614; obj* x_1617; obj* x_1618; obj* x_1619; obj* x_1621; obj* x_1623; obj* x_1624; obj* x_1627; obj* x_1629; obj* x_1630; obj* x_1632; obj* x_1633; obj* x_1634; 
x_1608 = lean::cnstr_get(x_1602, 0);
lean::inc(x_1608);
lean::dec(x_1602);
x_1611 = lean::cnstr_get(x_1, 0);
lean::inc(x_1611);
lean::dec(x_1);
x_1614 = lean::cnstr_get(x_1611, 2);
lean::inc(x_1614);
lean::dec(x_1611);
x_1617 = l_lean_file__map_to__position(x_1614, x_1608);
x_1618 = lean::box(0);
x_1619 = lean::cnstr_get(x_1617, 1);
lean::inc(x_1619);
x_1621 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1621);
x_1623 = l_lean_kvmap_set__nat(x_1618, x_1621, x_1619);
x_1624 = lean::cnstr_get(x_1617, 0);
lean::inc(x_1624);
lean::dec(x_1617);
x_1627 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1627);
x_1629 = l_lean_kvmap_set__nat(x_1623, x_1627, x_1624);
x_1630 = l_lean_elaborator_to__pexpr___main___closed__44;
lean::inc(x_1630);
x_1632 = lean_expr_mk_mdata(x_1629, x_1630);
x_1633 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1633, 0, x_1632);
lean::cnstr_set(x_1633, 1, x_2);
x_1634 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1634, 0, x_1633);
return x_1634;
}
}
else
{
obj* x_1637; obj* x_1639; obj* x_1640; 
lean::dec(x_1);
lean::dec(x_0);
x_1637 = l_lean_elaborator_to__pexpr___main___closed__44;
lean::inc(x_1637);
x_1639 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1639, 0, x_1637);
lean::cnstr_set(x_1639, 1, x_2);
x_1640 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1640, 0, x_1639);
return x_1640;
}
}
}
}
else
{
obj* x_1642; obj* x_1643; obj* x_1646; obj* x_1647; 
lean::dec(x_9);
x_1642 = l_lean_parser_term_pi_has__view;
x_1643 = lean::cnstr_get(x_1642, 0);
lean::inc(x_1643);
lean::inc(x_0);
x_1646 = lean::apply_1(x_1643, x_0);
x_1647 = lean::cnstr_get(x_1646, 1);
lean::inc(x_1647);
if (lean::obj_tag(x_1647) == 0)
{
obj* x_1651; obj* x_1655; 
lean::dec(x_1647);
lean::dec(x_1646);
x_1651 = l_lean_elaborator_to__pexpr___main___closed__45;
lean::inc(x_1);
lean::inc(x_1651);
lean::inc(x_0);
x_1655 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1651, x_1, x_2);
if (lean::obj_tag(x_1655) == 0)
{
obj* x_1659; obj* x_1661; obj* x_1662; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1659 = lean::cnstr_get(x_1655, 0);
lean::inc(x_1659);
if (lean::is_exclusive(x_1655)) {
 lean::cnstr_release(x_1655, 0);
 x_1661 = x_1655;
} else {
 lean::dec(x_1655);
 x_1661 = lean::box(0);
}
if (lean::is_scalar(x_1661)) {
 x_1662 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1662 = x_1661;
}
lean::cnstr_set(x_1662, 0, x_1659);
return x_1662;
}
else
{
obj* x_1663; 
x_1663 = lean::cnstr_get(x_1655, 0);
lean::inc(x_1663);
lean::dec(x_1655);
x_14 = x_1663;
goto lbl_15;
}
}
else
{
obj* x_1666; obj* x_1669; obj* x_1670; obj* x_1672; obj* x_1674; obj* x_1675; obj* x_1677; obj* x_1681; 
x_1666 = lean::cnstr_get(x_1647, 0);
lean::inc(x_1666);
lean::dec(x_1647);
x_1669 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1666);
x_1670 = lean::cnstr_get(x_1669, 0);
lean::inc(x_1670);
x_1672 = lean::cnstr_get(x_1669, 1);
lean::inc(x_1672);
if (lean::is_exclusive(x_1669)) {
 lean::cnstr_release(x_1669, 0);
 lean::cnstr_release(x_1669, 1);
 x_1674 = x_1669;
} else {
 lean::dec(x_1669);
 x_1674 = lean::box(0);
}
x_1675 = lean::cnstr_get(x_1672, 0);
lean::inc(x_1675);
x_1677 = lean::cnstr_get(x_1672, 1);
lean::inc(x_1677);
lean::dec(x_1672);
lean::inc(x_1);
x_1681 = l_lean_elaborator_to__pexpr___main(x_1677, x_1, x_2);
if (lean::obj_tag(x_1681) == 0)
{
obj* x_1689; obj* x_1691; obj* x_1692; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1675);
lean::dec(x_1674);
lean::dec(x_1670);
lean::dec(x_1646);
x_1689 = lean::cnstr_get(x_1681, 0);
lean::inc(x_1689);
if (lean::is_exclusive(x_1681)) {
 lean::cnstr_release(x_1681, 0);
 x_1691 = x_1681;
} else {
 lean::dec(x_1681);
 x_1691 = lean::box(0);
}
if (lean::is_scalar(x_1691)) {
 x_1692 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1692 = x_1691;
}
lean::cnstr_set(x_1692, 0, x_1689);
return x_1692;
}
else
{
obj* x_1693; obj* x_1695; obj* x_1696; obj* x_1698; obj* x_1701; obj* x_1705; 
x_1693 = lean::cnstr_get(x_1681, 0);
lean::inc(x_1693);
if (lean::is_exclusive(x_1681)) {
 lean::cnstr_release(x_1681, 0);
 x_1695 = x_1681;
} else {
 lean::dec(x_1681);
 x_1695 = lean::box(0);
}
x_1696 = lean::cnstr_get(x_1693, 0);
lean::inc(x_1696);
x_1698 = lean::cnstr_get(x_1693, 1);
lean::inc(x_1698);
lean::dec(x_1693);
x_1701 = lean::cnstr_get(x_1646, 3);
lean::inc(x_1701);
lean::dec(x_1646);
lean::inc(x_1);
x_1705 = l_lean_elaborator_to__pexpr___main(x_1701, x_1, x_1698);
if (lean::obj_tag(x_1705) == 0)
{
obj* x_1713; obj* x_1716; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1675);
lean::dec(x_1674);
lean::dec(x_1670);
lean::dec(x_1696);
x_1713 = lean::cnstr_get(x_1705, 0);
lean::inc(x_1713);
lean::dec(x_1705);
if (lean::is_scalar(x_1695)) {
 x_1716 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1716 = x_1695;
 lean::cnstr_set_tag(x_1695, 0);
}
lean::cnstr_set(x_1716, 0, x_1713);
return x_1716;
}
else
{
obj* x_1718; obj* x_1721; obj* x_1723; obj* x_1726; uint8 x_1727; obj* x_1729; obj* x_1730; 
lean::dec(x_1695);
x_1718 = lean::cnstr_get(x_1705, 0);
lean::inc(x_1718);
lean::dec(x_1705);
x_1721 = lean::cnstr_get(x_1718, 0);
lean::inc(x_1721);
x_1723 = lean::cnstr_get(x_1718, 1);
lean::inc(x_1723);
lean::dec(x_1718);
x_1726 = l_lean_elaborator_mangle__ident(x_1675);
x_1727 = lean::unbox(x_1670);
lean::dec(x_1670);
x_1729 = lean_expr_mk_pi(x_1726, x_1727, x_1696, x_1721);
if (lean::is_scalar(x_1674)) {
 x_1730 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1730 = x_1674;
}
lean::cnstr_set(x_1730, 0, x_1729);
lean::cnstr_set(x_1730, 1, x_1723);
x_14 = x_1730;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1732; obj* x_1733; obj* x_1736; obj* x_1737; 
lean::dec(x_9);
x_1732 = l_lean_parser_term_lambda_has__view;
x_1733 = lean::cnstr_get(x_1732, 0);
lean::inc(x_1733);
lean::inc(x_0);
x_1736 = lean::apply_1(x_1733, x_0);
x_1737 = lean::cnstr_get(x_1736, 1);
lean::inc(x_1737);
if (lean::obj_tag(x_1737) == 0)
{
obj* x_1741; obj* x_1745; 
lean::dec(x_1736);
lean::dec(x_1737);
x_1741 = l_lean_elaborator_to__pexpr___main___closed__46;
lean::inc(x_1);
lean::inc(x_1741);
lean::inc(x_0);
x_1745 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1741, x_1, x_2);
if (lean::obj_tag(x_1745) == 0)
{
obj* x_1749; obj* x_1751; obj* x_1752; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1749 = lean::cnstr_get(x_1745, 0);
lean::inc(x_1749);
if (lean::is_exclusive(x_1745)) {
 lean::cnstr_release(x_1745, 0);
 x_1751 = x_1745;
} else {
 lean::dec(x_1745);
 x_1751 = lean::box(0);
}
if (lean::is_scalar(x_1751)) {
 x_1752 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1752 = x_1751;
}
lean::cnstr_set(x_1752, 0, x_1749);
return x_1752;
}
else
{
obj* x_1753; 
x_1753 = lean::cnstr_get(x_1745, 0);
lean::inc(x_1753);
lean::dec(x_1745);
x_14 = x_1753;
goto lbl_15;
}
}
else
{
obj* x_1756; obj* x_1759; obj* x_1760; obj* x_1762; obj* x_1764; obj* x_1765; obj* x_1767; obj* x_1771; 
x_1756 = lean::cnstr_get(x_1737, 0);
lean::inc(x_1756);
lean::dec(x_1737);
x_1759 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1756);
x_1760 = lean::cnstr_get(x_1759, 0);
lean::inc(x_1760);
x_1762 = lean::cnstr_get(x_1759, 1);
lean::inc(x_1762);
if (lean::is_exclusive(x_1759)) {
 lean::cnstr_release(x_1759, 0);
 lean::cnstr_release(x_1759, 1);
 x_1764 = x_1759;
} else {
 lean::dec(x_1759);
 x_1764 = lean::box(0);
}
x_1765 = lean::cnstr_get(x_1762, 0);
lean::inc(x_1765);
x_1767 = lean::cnstr_get(x_1762, 1);
lean::inc(x_1767);
lean::dec(x_1762);
lean::inc(x_1);
x_1771 = l_lean_elaborator_to__pexpr___main(x_1767, x_1, x_2);
if (lean::obj_tag(x_1771) == 0)
{
obj* x_1779; obj* x_1781; obj* x_1782; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1760);
lean::dec(x_1765);
lean::dec(x_1764);
lean::dec(x_1736);
x_1779 = lean::cnstr_get(x_1771, 0);
lean::inc(x_1779);
if (lean::is_exclusive(x_1771)) {
 lean::cnstr_release(x_1771, 0);
 x_1781 = x_1771;
} else {
 lean::dec(x_1771);
 x_1781 = lean::box(0);
}
if (lean::is_scalar(x_1781)) {
 x_1782 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1782 = x_1781;
}
lean::cnstr_set(x_1782, 0, x_1779);
return x_1782;
}
else
{
obj* x_1783; obj* x_1785; obj* x_1786; obj* x_1788; obj* x_1791; obj* x_1795; 
x_1783 = lean::cnstr_get(x_1771, 0);
lean::inc(x_1783);
if (lean::is_exclusive(x_1771)) {
 lean::cnstr_release(x_1771, 0);
 x_1785 = x_1771;
} else {
 lean::dec(x_1771);
 x_1785 = lean::box(0);
}
x_1786 = lean::cnstr_get(x_1783, 0);
lean::inc(x_1786);
x_1788 = lean::cnstr_get(x_1783, 1);
lean::inc(x_1788);
lean::dec(x_1783);
x_1791 = lean::cnstr_get(x_1736, 3);
lean::inc(x_1791);
lean::dec(x_1736);
lean::inc(x_1);
x_1795 = l_lean_elaborator_to__pexpr___main(x_1791, x_1, x_1788);
if (lean::obj_tag(x_1795) == 0)
{
obj* x_1803; obj* x_1806; 
lean::dec(x_1786);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1760);
lean::dec(x_1765);
lean::dec(x_1764);
x_1803 = lean::cnstr_get(x_1795, 0);
lean::inc(x_1803);
lean::dec(x_1795);
if (lean::is_scalar(x_1785)) {
 x_1806 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1806 = x_1785;
 lean::cnstr_set_tag(x_1785, 0);
}
lean::cnstr_set(x_1806, 0, x_1803);
return x_1806;
}
else
{
obj* x_1808; obj* x_1811; obj* x_1813; obj* x_1816; uint8 x_1817; obj* x_1819; obj* x_1820; 
lean::dec(x_1785);
x_1808 = lean::cnstr_get(x_1795, 0);
lean::inc(x_1808);
lean::dec(x_1795);
x_1811 = lean::cnstr_get(x_1808, 0);
lean::inc(x_1811);
x_1813 = lean::cnstr_get(x_1808, 1);
lean::inc(x_1813);
lean::dec(x_1808);
x_1816 = l_lean_elaborator_mangle__ident(x_1765);
x_1817 = lean::unbox(x_1760);
lean::dec(x_1760);
x_1819 = lean_expr_mk_lambda(x_1816, x_1817, x_1786, x_1811);
if (lean::is_scalar(x_1764)) {
 x_1820 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1820 = x_1764;
}
lean::cnstr_set(x_1820, 0, x_1819);
lean::cnstr_set(x_1820, 1, x_1813);
x_14 = x_1820;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1822; obj* x_1823; obj* x_1826; obj* x_1827; obj* x_1830; 
lean::dec(x_9);
x_1822 = l_lean_parser_term_app_has__view;
x_1823 = lean::cnstr_get(x_1822, 0);
lean::inc(x_1823);
lean::inc(x_0);
x_1826 = lean::apply_1(x_1823, x_0);
x_1827 = lean::cnstr_get(x_1826, 0);
lean::inc(x_1827);
lean::inc(x_1);
x_1830 = l_lean_elaborator_to__pexpr___main(x_1827, x_1, x_2);
if (lean::obj_tag(x_1830) == 0)
{
obj* x_1835; obj* x_1837; obj* x_1838; 
lean::dec(x_1826);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1835 = lean::cnstr_get(x_1830, 0);
lean::inc(x_1835);
if (lean::is_exclusive(x_1830)) {
 lean::cnstr_release(x_1830, 0);
 x_1837 = x_1830;
} else {
 lean::dec(x_1830);
 x_1837 = lean::box(0);
}
if (lean::is_scalar(x_1837)) {
 x_1838 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1838 = x_1837;
}
lean::cnstr_set(x_1838, 0, x_1835);
return x_1838;
}
else
{
obj* x_1839; obj* x_1841; obj* x_1842; obj* x_1844; obj* x_1846; obj* x_1847; obj* x_1851; 
x_1839 = lean::cnstr_get(x_1830, 0);
lean::inc(x_1839);
if (lean::is_exclusive(x_1830)) {
 lean::cnstr_release(x_1830, 0);
 x_1841 = x_1830;
} else {
 lean::dec(x_1830);
 x_1841 = lean::box(0);
}
x_1842 = lean::cnstr_get(x_1839, 0);
lean::inc(x_1842);
x_1844 = lean::cnstr_get(x_1839, 1);
lean::inc(x_1844);
if (lean::is_exclusive(x_1839)) {
 lean::cnstr_release(x_1839, 0);
 lean::cnstr_release(x_1839, 1);
 x_1846 = x_1839;
} else {
 lean::dec(x_1839);
 x_1846 = lean::box(0);
}
x_1847 = lean::cnstr_get(x_1826, 1);
lean::inc(x_1847);
lean::dec(x_1826);
lean::inc(x_1);
x_1851 = l_lean_elaborator_to__pexpr___main(x_1847, x_1, x_1844);
if (lean::obj_tag(x_1851) == 0)
{
obj* x_1857; obj* x_1860; 
lean::dec(x_7);
lean::dec(x_1846);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1842);
x_1857 = lean::cnstr_get(x_1851, 0);
lean::inc(x_1857);
lean::dec(x_1851);
if (lean::is_scalar(x_1841)) {
 x_1860 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1860 = x_1841;
 lean::cnstr_set_tag(x_1841, 0);
}
lean::cnstr_set(x_1860, 0, x_1857);
return x_1860;
}
else
{
obj* x_1862; obj* x_1865; obj* x_1867; obj* x_1870; obj* x_1871; 
lean::dec(x_1841);
x_1862 = lean::cnstr_get(x_1851, 0);
lean::inc(x_1862);
lean::dec(x_1851);
x_1865 = lean::cnstr_get(x_1862, 0);
lean::inc(x_1865);
x_1867 = lean::cnstr_get(x_1862, 1);
lean::inc(x_1867);
lean::dec(x_1862);
x_1870 = lean_expr_mk_app(x_1842, x_1865);
if (lean::is_scalar(x_1846)) {
 x_1871 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1871 = x_1846;
}
lean::cnstr_set(x_1871, 0, x_1870);
lean::cnstr_set(x_1871, 1, x_1867);
x_14 = x_1871;
goto lbl_15;
}
}
}
}
else
{
obj* x_1873; obj* x_1874; obj* x_1877; obj* x_1878; obj* x_1880; 
lean::dec(x_9);
x_1873 = l_lean_parser_ident__univs_has__view;
x_1874 = lean::cnstr_get(x_1873, 0);
lean::inc(x_1874);
lean::inc(x_0);
x_1877 = lean::apply_1(x_1874, x_0);
x_1878 = lean::cnstr_get(x_1877, 0);
lean::inc(x_1878);
x_1880 = lean::cnstr_get(x_1877, 1);
lean::inc(x_1880);
lean::dec(x_1877);
if (lean::obj_tag(x_1880) == 0)
{
obj* x_1884; obj* x_1885; obj* x_1886; obj* x_1887; obj* x_1890; obj* x_1891; obj* x_1892; obj* x_1894; obj* x_1895; obj* x_1896; uint8 x_1897; 
lean::inc(x_1878);
x_1884 = l_lean_elaborator_mangle__ident(x_1878);
x_1885 = lean::box(0);
x_1886 = lean_expr_mk_const(x_1884, x_1885);
x_1887 = lean::cnstr_get(x_1878, 3);
lean::inc(x_1887);
lean::dec(x_1878);
x_1890 = lean::mk_nat_obj(0u);
x_1891 = l_list_enum__from___main___rarg(x_1890, x_1887);
x_1892 = l_lean_elaborator_to__pexpr___main___closed__47;
lean::inc(x_1892);
x_1894 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(x_1892, x_1891);
x_1895 = lean_expr_mk_mdata(x_1894, x_1886);
x_1896 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1897 = lean_name_dec_eq(x_7, x_1896);
lean::dec(x_7);
if (x_1897 == 0)
{
obj* x_1899; 
x_1899 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1899) == 0)
{
obj* x_1901; obj* x_1902; 
lean::dec(x_1);
x_1901 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1901, 0, x_1895);
lean::cnstr_set(x_1901, 1, x_2);
x_1902 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1902, 0, x_1901);
return x_1902;
}
else
{
obj* x_1903; obj* x_1906; obj* x_1909; obj* x_1912; obj* x_1913; obj* x_1915; obj* x_1917; obj* x_1918; obj* x_1921; obj* x_1923; obj* x_1924; obj* x_1925; obj* x_1926; 
x_1903 = lean::cnstr_get(x_1899, 0);
lean::inc(x_1903);
lean::dec(x_1899);
x_1906 = lean::cnstr_get(x_1, 0);
lean::inc(x_1906);
lean::dec(x_1);
x_1909 = lean::cnstr_get(x_1906, 2);
lean::inc(x_1909);
lean::dec(x_1906);
x_1912 = l_lean_file__map_to__position(x_1909, x_1903);
x_1913 = lean::cnstr_get(x_1912, 1);
lean::inc(x_1913);
x_1915 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1915);
x_1917 = l_lean_kvmap_set__nat(x_1885, x_1915, x_1913);
x_1918 = lean::cnstr_get(x_1912, 0);
lean::inc(x_1918);
lean::dec(x_1912);
x_1921 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1921);
x_1923 = l_lean_kvmap_set__nat(x_1917, x_1921, x_1918);
x_1924 = lean_expr_mk_mdata(x_1923, x_1895);
x_1925 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1925, 0, x_1924);
lean::cnstr_set(x_1925, 1, x_2);
x_1926 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1926, 0, x_1925);
return x_1926;
}
}
else
{
obj* x_1929; obj* x_1930; 
lean::dec(x_1);
lean::dec(x_0);
x_1929 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1929, 0, x_1895);
lean::cnstr_set(x_1929, 1, x_2);
x_1930 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1930, 0, x_1929);
return x_1930;
}
}
else
{
obj* x_1931; obj* x_1934; obj* x_1938; 
x_1931 = lean::cnstr_get(x_1880, 0);
lean::inc(x_1931);
lean::dec(x_1880);
x_1934 = lean::cnstr_get(x_1931, 1);
lean::inc(x_1934);
lean::dec(x_1931);
lean::inc(x_1);
x_1938 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_1934, x_1, x_2);
if (lean::obj_tag(x_1938) == 0)
{
obj* x_1943; obj* x_1945; obj* x_1946; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1878);
x_1943 = lean::cnstr_get(x_1938, 0);
lean::inc(x_1943);
if (lean::is_exclusive(x_1938)) {
 lean::cnstr_release(x_1938, 0);
 x_1945 = x_1938;
} else {
 lean::dec(x_1938);
 x_1945 = lean::box(0);
}
if (lean::is_scalar(x_1945)) {
 x_1946 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1946 = x_1945;
}
lean::cnstr_set(x_1946, 0, x_1943);
return x_1946;
}
else
{
obj* x_1947; obj* x_1950; obj* x_1952; obj* x_1954; obj* x_1956; obj* x_1957; obj* x_1958; obj* x_1961; obj* x_1962; obj* x_1963; obj* x_1965; obj* x_1966; obj* x_1967; 
x_1947 = lean::cnstr_get(x_1938, 0);
lean::inc(x_1947);
lean::dec(x_1938);
x_1950 = lean::cnstr_get(x_1947, 0);
lean::inc(x_1950);
x_1952 = lean::cnstr_get(x_1947, 1);
lean::inc(x_1952);
if (lean::is_exclusive(x_1947)) {
 lean::cnstr_release(x_1947, 0);
 lean::cnstr_release(x_1947, 1);
 x_1954 = x_1947;
} else {
 lean::dec(x_1947);
 x_1954 = lean::box(0);
}
lean::inc(x_1878);
x_1956 = l_lean_elaborator_mangle__ident(x_1878);
x_1957 = lean_expr_mk_const(x_1956, x_1950);
x_1958 = lean::cnstr_get(x_1878, 3);
lean::inc(x_1958);
lean::dec(x_1878);
x_1961 = lean::mk_nat_obj(0u);
x_1962 = l_list_enum__from___main___rarg(x_1961, x_1958);
x_1963 = l_lean_elaborator_to__pexpr___main___closed__47;
lean::inc(x_1963);
x_1965 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(x_1963, x_1962);
x_1966 = lean_expr_mk_mdata(x_1965, x_1957);
if (lean::is_scalar(x_1954)) {
 x_1967 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1967 = x_1954;
}
lean::cnstr_set(x_1967, 0, x_1966);
lean::cnstr_set(x_1967, 1, x_1952);
x_14 = x_1967;
goto lbl_15;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_1971; obj* x_1973; obj* x_1974; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1971 = lean::cnstr_get(x_12, 0);
lean::inc(x_1971);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_1973 = x_12;
} else {
 lean::dec(x_12);
 x_1973 = lean::box(0);
}
if (lean::is_scalar(x_1973)) {
 x_1974 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1974 = x_1973;
}
lean::cnstr_set(x_1974, 0, x_1971);
return x_1974;
}
else
{
obj* x_1975; obj* x_1977; obj* x_1978; obj* x_1980; obj* x_1982; obj* x_1983; uint8 x_1984; 
x_1975 = lean::cnstr_get(x_12, 0);
lean::inc(x_1975);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_1977 = x_12;
} else {
 lean::dec(x_12);
 x_1977 = lean::box(0);
}
x_1978 = lean::cnstr_get(x_1975, 0);
lean::inc(x_1978);
x_1980 = lean::cnstr_get(x_1975, 1);
lean::inc(x_1980);
if (lean::is_exclusive(x_1975)) {
 lean::cnstr_release(x_1975, 0);
 lean::cnstr_release(x_1975, 1);
 x_1982 = x_1975;
} else {
 lean::dec(x_1975);
 x_1982 = lean::box(0);
}
x_1983 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1984 = lean_name_dec_eq(x_7, x_1983);
lean::dec(x_7);
if (x_1984 == 0)
{
obj* x_1986; 
x_1986 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1986) == 0)
{
obj* x_1988; obj* x_1989; 
lean::dec(x_1);
if (lean::is_scalar(x_1982)) {
 x_1988 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1988 = x_1982;
}
lean::cnstr_set(x_1988, 0, x_1978);
lean::cnstr_set(x_1988, 1, x_1980);
if (lean::is_scalar(x_1977)) {
 x_1989 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1989 = x_1977;
}
lean::cnstr_set(x_1989, 0, x_1988);
return x_1989;
}
else
{
obj* x_1990; obj* x_1993; obj* x_1996; obj* x_1999; obj* x_2000; obj* x_2001; obj* x_2003; obj* x_2005; obj* x_2006; obj* x_2009; obj* x_2011; obj* x_2012; obj* x_2013; obj* x_2014; 
x_1990 = lean::cnstr_get(x_1986, 0);
lean::inc(x_1990);
lean::dec(x_1986);
x_1993 = lean::cnstr_get(x_1, 0);
lean::inc(x_1993);
lean::dec(x_1);
x_1996 = lean::cnstr_get(x_1993, 2);
lean::inc(x_1996);
lean::dec(x_1993);
x_1999 = l_lean_file__map_to__position(x_1996, x_1990);
x_2000 = lean::box(0);
x_2001 = lean::cnstr_get(x_1999, 1);
lean::inc(x_2001);
x_2003 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_2003);
x_2005 = l_lean_kvmap_set__nat(x_2000, x_2003, x_2001);
x_2006 = lean::cnstr_get(x_1999, 0);
lean::inc(x_2006);
lean::dec(x_1999);
x_2009 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_2009);
x_2011 = l_lean_kvmap_set__nat(x_2005, x_2009, x_2006);
x_2012 = lean_expr_mk_mdata(x_2011, x_1978);
if (lean::is_scalar(x_1982)) {
 x_2013 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2013 = x_1982;
}
lean::cnstr_set(x_2013, 0, x_2012);
lean::cnstr_set(x_2013, 1, x_1980);
if (lean::is_scalar(x_1977)) {
 x_2014 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2014 = x_1977;
}
lean::cnstr_set(x_2014, 0, x_2013);
return x_2014;
}
}
else
{
obj* x_2017; obj* x_2018; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_1982)) {
 x_2017 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2017 = x_1982;
}
lean::cnstr_set(x_2017, 0, x_1978);
lean::cnstr_set(x_2017, 1, x_1980);
if (lean::is_scalar(x_1977)) {
 x_2018 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2018 = x_1977;
}
lean::cnstr_set(x_2018, 0, x_2017);
return x_2018;
}
}
}
lbl_15:
{
obj* x_2019; obj* x_2021; obj* x_2023; obj* x_2024; uint8 x_2025; 
x_2019 = lean::cnstr_get(x_14, 0);
lean::inc(x_2019);
x_2021 = lean::cnstr_get(x_14, 1);
lean::inc(x_2021);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_2023 = x_14;
} else {
 lean::dec(x_14);
 x_2023 = lean::box(0);
}
x_2024 = l_lean_elaborator_to__pexpr___main___closed__2;
x_2025 = lean_name_dec_eq(x_7, x_2024);
lean::dec(x_7);
if (x_2025 == 0)
{
obj* x_2027; 
x_2027 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_2027) == 0)
{
obj* x_2029; obj* x_2030; 
lean::dec(x_1);
if (lean::is_scalar(x_2023)) {
 x_2029 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2029 = x_2023;
}
lean::cnstr_set(x_2029, 0, x_2019);
lean::cnstr_set(x_2029, 1, x_2021);
x_2030 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2030, 0, x_2029);
return x_2030;
}
else
{
obj* x_2031; obj* x_2034; obj* x_2037; obj* x_2040; obj* x_2041; obj* x_2042; obj* x_2044; obj* x_2046; obj* x_2047; obj* x_2050; obj* x_2052; obj* x_2053; obj* x_2054; obj* x_2055; 
x_2031 = lean::cnstr_get(x_2027, 0);
lean::inc(x_2031);
lean::dec(x_2027);
x_2034 = lean::cnstr_get(x_1, 0);
lean::inc(x_2034);
lean::dec(x_1);
x_2037 = lean::cnstr_get(x_2034, 2);
lean::inc(x_2037);
lean::dec(x_2034);
x_2040 = l_lean_file__map_to__position(x_2037, x_2031);
x_2041 = lean::box(0);
x_2042 = lean::cnstr_get(x_2040, 1);
lean::inc(x_2042);
x_2044 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_2044);
x_2046 = l_lean_kvmap_set__nat(x_2041, x_2044, x_2042);
x_2047 = lean::cnstr_get(x_2040, 0);
lean::inc(x_2047);
lean::dec(x_2040);
x_2050 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_2050);
x_2052 = l_lean_kvmap_set__nat(x_2046, x_2050, x_2047);
x_2053 = lean_expr_mk_mdata(x_2052, x_2019);
if (lean::is_scalar(x_2023)) {
 x_2054 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2054 = x_2023;
}
lean::cnstr_set(x_2054, 0, x_2053);
lean::cnstr_set(x_2054, 1, x_2021);
x_2055 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2055, 0, x_2054);
return x_2055;
}
}
else
{
obj* x_2058; obj* x_2059; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_2023)) {
 x_2058 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2058 = x_2023;
}
lean::cnstr_set(x_2058, 0, x_2019);
lean::cnstr_set(x_2058, 1, x_2021);
x_2059 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2059, 0, x_2058);
return x_2059;
}
}
lbl_17:
{
obj* x_2060; obj* x_2062; obj* x_2064; 
x_2060 = lean::cnstr_get(x_16, 0);
lean::inc(x_2060);
x_2062 = lean::cnstr_get(x_16, 1);
lean::inc(x_2062);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_2064 = x_16;
} else {
 lean::dec(x_16);
 x_2064 = lean::box(0);
}
if (lean::obj_tag(x_2060) == 0)
{
obj* x_2067; obj* x_2071; 
lean::dec(x_9);
lean::dec(x_2064);
x_2067 = l_lean_elaborator_to__pexpr___main___closed__5;
lean::inc(x_1);
lean::inc(x_2067);
lean::inc(x_0);
x_2071 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2067, x_1, x_2062);
if (lean::obj_tag(x_2071) == 0)
{
obj* x_2075; obj* x_2077; obj* x_2078; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_2075 = lean::cnstr_get(x_2071, 0);
lean::inc(x_2075);
if (lean::is_exclusive(x_2071)) {
 lean::cnstr_release(x_2071, 0);
 x_2077 = x_2071;
} else {
 lean::dec(x_2071);
 x_2077 = lean::box(0);
}
if (lean::is_scalar(x_2077)) {
 x_2078 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2078 = x_2077;
}
lean::cnstr_set(x_2078, 0, x_2075);
return x_2078;
}
else
{
obj* x_2079; 
x_2079 = lean::cnstr_get(x_2071, 0);
lean::inc(x_2079);
lean::dec(x_2071);
x_14 = x_2079;
goto lbl_15;
}
}
else
{
obj* x_2082; obj* x_2084; obj* x_2087; obj* x_2088; obj* x_2089; obj* x_2090; obj* x_2092; obj* x_2093; obj* x_2094; obj* x_2095; obj* x_2096; 
x_2082 = lean::cnstr_get(x_2060, 0);
lean::inc(x_2082);
x_2084 = lean::cnstr_get(x_2060, 1);
lean::inc(x_2084);
lean::dec(x_2060);
x_2087 = lean::box(0);
x_2088 = lean::mk_nat_obj(0u);
x_2089 = l_list_length__aux___main___rarg(x_9, x_2088);
x_2090 = l_lean_elaborator_to__pexpr___main___closed__6;
lean::inc(x_2090);
x_2092 = l_lean_kvmap_set__nat(x_2087, x_2090, x_2089);
x_2093 = l_list_reverse___rarg(x_2084);
x_2094 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_2082, x_2093);
x_2095 = lean_expr_mk_mdata(x_2092, x_2094);
if (lean::is_scalar(x_2064)) {
 x_2096 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2096 = x_2064;
}
lean::cnstr_set(x_2096, 0, x_2095);
lean::cnstr_set(x_2096, 1, x_2062);
x_14 = x_2096;
goto lbl_15;
}
}
}
default:
{
obj* x_2097; 
x_2097 = lean::box(0);
x_3 = x_2097;
goto lbl_4;
}
}
lbl_4:
{
obj* x_2100; obj* x_2101; obj* x_2102; obj* x_2103; obj* x_2105; obj* x_2107; 
lean::dec(x_3);
lean::inc(x_0);
x_2100 = l_lean_parser_syntax_to__format___main(x_0);
x_2101 = lean::mk_nat_obj(80u);
x_2102 = l_lean_format_pretty(x_2100, x_2101);
x_2103 = l_lean_elaborator_to__pexpr___main___closed__1;
lean::inc(x_2103);
x_2105 = lean::string_append(x_2103, x_2102);
lean::dec(x_2102);
x_2107 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2105, x_1, x_2);
return x_2107;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
} else {
 lean::dec(x_0);
 x_12 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
} else {
 lean::dec(x_0);
 x_38 = lean::box(0);
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
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
lean::dec(x_11);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_18);
return x_20;
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
lean::cnstr_set(x_2, 2, x_1);
return x_2;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
} else {
 lean::dec(x_0);
 x_12 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
} else {
 lean::dec(x_0);
 x_38 = lean::box(0);
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
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
lean::dec(x_11);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_18);
return x_20;
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
lean::cnstr_set(x_2, 2, x_1);
return x_2;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
} else {
 lean::dec(x_0);
 x_12 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
} else {
 lean::dec(x_0);
 x_38 = lean::box(0);
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
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_40 = x_8;
} else {
 lean::dec(x_8);
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
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_67; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_82; 
x_42 = lean::cnstr_get(x_8, 0);
lean::inc(x_42);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_44 = x_8;
} else {
 lean::dec(x_8);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_42, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_49 = x_42;
} else {
 lean::dec(x_42);
 x_49 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
} else {
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
} else {
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
} else {
 lean::dec(x_21);
 x_28 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 x_25 = x_18;
} else {
 lean::dec(x_18);
 x_25 = lean::box(0);
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
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 x_29 = x_18;
} else {
 lean::dec(x_18);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 lean::cnstr_release(x_27, 1);
 x_34 = x_27;
} else {
 lean::dec(x_27);
 x_34 = lean::box(0);
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
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::dec(x_3);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
} else {
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_15 = x_8;
} else {
 lean::dec(x_8);
 x_15 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("private");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = 1;
x_4 = l_lean_kvmap_set__bool(x_0, x_2, x_3);
return x_4;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("protected");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = 1;
x_4 = l_lean_kvmap_set__bool(x_0, x_2, x_3);
return x_4;
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
obj* x_43; obj* x_46; obj* x_49; obj* x_51; 
x_43 = lean::cnstr_get(x_31, 0);
lean::inc(x_43);
lean::dec(x_31);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
x_49 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
lean::inc(x_49);
x_51 = l_lean_kvmap_set__string(x_3, x_49, x_46);
if (lean::obj_tag(x_6) == 0)
{
x_17 = x_51;
goto lbl_18;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_6, 0);
lean::inc(x_52);
lean::dec(x_6);
if (lean::obj_tag(x_52) == 0)
{
obj* x_56; uint8 x_57; obj* x_59; 
lean::dec(x_52);
x_56 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
x_57 = 1;
lean::inc(x_56);
x_59 = l_lean_kvmap_set__bool(x_51, x_56, x_57);
x_17 = x_59;
goto lbl_18;
}
else
{
obj* x_61; uint8 x_62; obj* x_64; 
lean::dec(x_52);
x_61 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
x_62 = 1;
lean::inc(x_61);
x_64 = l_lean_kvmap_set__bool(x_51, x_61, x_62);
x_17 = x_64;
goto lbl_18;
}
}
}
}
lbl_18:
{
obj* x_65; obj* x_67; obj* x_68; obj* x_70; 
x_65 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
lean::inc(x_65);
x_67 = l_lean_kvmap_set__bool(x_17, x_65, x_10);
x_68 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
lean::inc(x_68);
x_70 = l_lean_kvmap_set__bool(x_67, x_68, x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_71; 
x_71 = l_lean_elaborator_attrs__to__pexpr(x_3, x_1, x_2);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_70);
x_73 = lean::cnstr_get(x_71, 0);
lean::inc(x_73);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_75 = x_71;
} else {
 lean::dec(x_71);
 x_75 = lean::box(0);
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
obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_77 = lean::cnstr_get(x_71, 0);
lean::inc(x_77);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_79 = x_71;
} else {
 lean::dec(x_71);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
} else {
 lean::dec(x_77);
 x_84 = lean::box(0);
}
x_85 = lean_expr_mk_mdata(x_70, x_80);
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_82);
if (lean::is_scalar(x_79)) {
 x_87 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_87 = x_79;
}
lean::cnstr_set(x_87, 0, x_86);
return x_87;
}
}
else
{
obj* x_88; obj* x_91; obj* x_94; 
x_88 = lean::cnstr_get(x_14, 0);
lean::inc(x_88);
lean::dec(x_14);
x_91 = lean::cnstr_get(x_88, 1);
lean::inc(x_91);
lean::dec(x_88);
x_94 = l_lean_elaborator_attrs__to__pexpr(x_91, x_1, x_2);
if (lean::obj_tag(x_94) == 0)
{
obj* x_96; obj* x_98; obj* x_99; 
lean::dec(x_70);
x_96 = lean::cnstr_get(x_94, 0);
lean::inc(x_96);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 x_98 = x_94;
} else {
 lean::dec(x_94);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
return x_99;
}
else
{
obj* x_100; obj* x_102; obj* x_103; obj* x_105; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_94, 0);
lean::inc(x_100);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 x_102 = x_94;
} else {
 lean::dec(x_94);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_100, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_100, 1);
lean::inc(x_105);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 x_107 = x_100;
} else {
 lean::dec(x_100);
 x_107 = lean::box(0);
}
x_108 = lean_expr_mk_mdata(x_70, x_103);
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_105);
if (lean::is_scalar(x_102)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_102;
}
lean::cnstr_set(x_110, 0, x_109);
return x_110;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
}
x_12 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_7);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_17 = x_12;
} else {
 lean::dec(x_12);
 x_17 = lean::box(0);
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
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_33 = x_24;
} else {
 lean::dec(x_24);
 x_33 = lean::box(0);
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
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_37 = x_24;
} else {
 lean::dec(x_24);
 x_37 = lean::box(0);
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
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::dec(x_3);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
} else {
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_15 = x_8;
} else {
 lean::dec(x_8);
 x_15 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
} else {
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
} else {
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
} else {
 lean::dec(x_21);
 x_28 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_25 = x_17;
} else {
 lean::dec(x_17);
 x_25 = lean::box(0);
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
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_29 = x_17;
} else {
 lean::dec(x_17);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 lean::cnstr_release(x_27, 1);
 x_34 = x_27;
} else {
 lean::dec(x_27);
 x_34 = lean::box(0);
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
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 1);
 x_60 = x_50;
} else {
 lean::dec(x_50);
 x_60 = lean::box(0);
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
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_79 = x_72;
} else {
 lean::dec(x_72);
 x_79 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
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
lean::dec(x_11);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_18);
return x_20;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("defs");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = l_lean_kvmap_set__name(x_0, x_2, x_4);
return x_5;
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
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 x_45 = x_34;
} else {
 lean::dec(x_34);
 x_45 = lean::box(0);
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
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 x_49 = x_34;
} else {
 lean::dec(x_34);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_54 = x_47;
} else {
 lean::dec(x_47);
 x_54 = lean::box(0);
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
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_54);
x_73 = lean::cnstr_get(x_63, 0);
lean::inc(x_73);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 x_75 = x_63;
} else {
 lean::dec(x_63);
 x_75 = lean::box(0);
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
obj* x_77; 
x_77 = lean::cnstr_get(x_63, 0);
lean::inc(x_77);
lean::dec(x_63);
x_58 = x_55;
x_59 = x_77;
goto lbl_60;
}
}
else
{
obj* x_80; 
x_80 = lean::cnstr_get(x_6, 0);
lean::inc(x_80);
lean::dec(x_6);
if (lean::obj_tag(x_63) == 0)
{
obj* x_93; obj* x_95; obj* x_96; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_80);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_54);
x_93 = lean::cnstr_get(x_63, 0);
lean::inc(x_93);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 x_95 = x_63;
} else {
 lean::dec(x_63);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_93);
return x_96;
}
else
{
obj* x_97; obj* x_100; obj* x_103; 
x_97 = lean::cnstr_get(x_63, 0);
lean::inc(x_97);
lean::dec(x_63);
x_100 = lean::cnstr_get(x_80, 1);
lean::inc(x_100);
lean::dec(x_80);
x_103 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(x_100);
x_58 = x_103;
x_59 = x_97;
goto lbl_60;
}
}
}
else
{
obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_118; obj* x_120; obj* x_124; obj* x_125; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_134; obj* x_137; obj* x_138; obj* x_140; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_151; obj* x_152; obj* x_154; 
x_104 = lean::cnstr_get(x_6, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_52, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_52, 1);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_52, 2);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_52, 3);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_52, 4);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_114, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_114, 1);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_104, 1);
lean::inc(x_120);
lean::dec(x_104);
lean::inc(x_120);
x_124 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(x_120);
x_125 = l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(x_118, x_124);
x_126 = lean::cnstr_get(x_114, 2);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_114, 3);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_114, 4);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_114, 5);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_114, 6);
lean::inc(x_134);
lean::dec(x_114);
x_137 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_137, 0, x_116);
lean::cnstr_set(x_137, 1, x_125);
lean::cnstr_set(x_137, 2, x_126);
lean::cnstr_set(x_137, 3, x_128);
lean::cnstr_set(x_137, 4, x_130);
lean::cnstr_set(x_137, 5, x_132);
lean::cnstr_set(x_137, 6, x_134);
x_138 = lean::cnstr_get(x_52, 5);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_52, 6);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_52, 7);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_52, 8);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_52, 9);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_52, 10);
lean::inc(x_148);
lean::dec(x_52);
x_151 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_151, 0, x_106);
lean::cnstr_set(x_151, 1, x_108);
lean::cnstr_set(x_151, 2, x_110);
lean::cnstr_set(x_151, 3, x_112);
lean::cnstr_set(x_151, 4, x_137);
lean::cnstr_set(x_151, 5, x_138);
lean::cnstr_set(x_151, 6, x_140);
lean::cnstr_set(x_151, 7, x_142);
lean::cnstr_set(x_151, 8, x_144);
lean::cnstr_set(x_151, 9, x_146);
lean::cnstr_set(x_151, 10, x_148);
x_152 = l_lean_expander_get__opt__type___main(x_17);
lean::inc(x_4);
x_154 = l_lean_elaborator_to__pexpr___main(x_152, x_4, x_151);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_120);
if (lean::obj_tag(x_154) == 0)
{
obj* x_165; obj* x_167; obj* x_168; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_54);
x_165 = lean::cnstr_get(x_154, 0);
lean::inc(x_165);
if (lean::is_exclusive(x_154)) {
 lean::cnstr_release(x_154, 0);
 x_167 = x_154;
} else {
 lean::dec(x_154);
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
obj* x_169; 
x_169 = lean::cnstr_get(x_154, 0);
lean::inc(x_169);
lean::dec(x_154);
x_58 = x_55;
x_59 = x_169;
goto lbl_60;
}
}
else
{
lean::dec(x_6);
if (lean::obj_tag(x_154) == 0)
{
obj* x_183; obj* x_185; obj* x_186; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_54);
lean::dec(x_120);
x_183 = lean::cnstr_get(x_154, 0);
lean::inc(x_183);
if (lean::is_exclusive(x_154)) {
 lean::cnstr_release(x_154, 0);
 x_185 = x_154;
} else {
 lean::dec(x_154);
 x_185 = lean::box(0);
}
if (lean::is_scalar(x_185)) {
 x_186 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_186 = x_185;
}
lean::cnstr_set(x_186, 0, x_183);
return x_186;
}
else
{
obj* x_187; obj* x_190; 
x_187 = lean::cnstr_get(x_154, 0);
lean::inc(x_187);
lean::dec(x_154);
x_190 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(x_120);
x_58 = x_190;
x_59 = x_187;
goto lbl_60;
}
}
}
lbl_60:
{
obj* x_191; obj* x_193; obj* x_196; obj* x_197; obj* x_199; uint8 x_200; obj* x_203; obj* x_204; obj* x_205; obj* x_207; obj* x_208; 
x_191 = lean::cnstr_get(x_59, 0);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_59, 1);
lean::inc(x_193);
lean::dec(x_59);
x_196 = l_lean_elaborator_names__to__pexpr(x_58);
x_197 = lean::cnstr_get(x_8, 0);
lean::inc(x_197);
x_199 = l_lean_elaborator_mangle__ident(x_197);
x_200 = 4;
lean::inc(x_191);
lean::inc(x_199);
x_203 = lean_expr_local(x_199, x_199, x_191, x_200);
x_204 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_204, 0, x_203);
lean::cnstr_set(x_204, 1, x_55);
x_205 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_205);
x_207 = l_lean_expr_mk__capp(x_205, x_204);
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_213; obj* x_216; obj* x_220; 
lean::dec(x_191);
lean::dec(x_8);
lean::dec(x_54);
x_213 = lean::cnstr_get(x_12, 0);
lean::inc(x_213);
lean::dec(x_12);
x_216 = lean::cnstr_get(x_213, 1);
lean::inc(x_216);
lean::dec(x_213);
lean::inc(x_4);
x_220 = l_lean_elaborator_to__pexpr___main(x_216, x_4, x_193);
if (lean::obj_tag(x_220) == 0)
{
obj* x_229; obj* x_231; obj* x_232; 
lean::dec(x_207);
lean::dec(x_196);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
x_229 = lean::cnstr_get(x_220, 0);
lean::inc(x_229);
if (lean::is_exclusive(x_220)) {
 lean::cnstr_release(x_220, 0);
 x_231 = x_220;
} else {
 lean::dec(x_220);
 x_231 = lean::box(0);
}
if (lean::is_scalar(x_231)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_231;
}
lean::cnstr_set(x_232, 0, x_229);
return x_232;
}
else
{
obj* x_233; 
x_233 = lean::cnstr_get(x_220, 0);
lean::inc(x_233);
lean::dec(x_220);
x_208 = x_233;
goto lbl_209;
}
}
case 1:
{
obj* x_238; obj* x_239; 
lean::dec(x_12);
lean::dec(x_8);
x_238 = l_lean_elaborator_mk__eqns(x_191, x_55);
if (lean::is_scalar(x_54)) {
 x_239 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_239 = x_54;
}
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_239, 1, x_193);
x_208 = x_239;
goto lbl_209;
}
default:
{
obj* x_240; obj* x_244; 
x_240 = lean::cnstr_get(x_12, 0);
lean::inc(x_240);
lean::dec(x_12);
lean::inc(x_4);
x_244 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_8, x_240, x_4, x_193);
if (lean::obj_tag(x_244) == 0)
{
obj* x_255; obj* x_257; obj* x_258; 
lean::dec(x_191);
lean::dec(x_207);
lean::dec(x_196);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_30);
lean::dec(x_57);
lean::dec(x_54);
x_255 = lean::cnstr_get(x_244, 0);
lean::inc(x_255);
if (lean::is_exclusive(x_244)) {
 lean::cnstr_release(x_244, 0);
 x_257 = x_244;
} else {
 lean::dec(x_244);
 x_257 = lean::box(0);
}
if (lean::is_scalar(x_257)) {
 x_258 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_258 = x_257;
}
lean::cnstr_set(x_258, 0, x_255);
return x_258;
}
else
{
obj* x_259; obj* x_262; obj* x_264; obj* x_267; obj* x_268; 
x_259 = lean::cnstr_get(x_244, 0);
lean::inc(x_259);
lean::dec(x_244);
x_262 = lean::cnstr_get(x_259, 0);
lean::inc(x_262);
x_264 = lean::cnstr_get(x_259, 1);
lean::inc(x_264);
lean::dec(x_259);
x_267 = l_lean_elaborator_mk__eqns(x_191, x_262);
if (lean::is_scalar(x_54)) {
 x_268 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_268 = x_54;
}
lean::cnstr_set(x_268, 0, x_267);
lean::cnstr_set(x_268, 1, x_264);
x_208 = x_268;
goto lbl_209;
}
}
}
lbl_209:
{
obj* x_269; obj* x_271; obj* x_275; 
x_269 = lean::cnstr_get(x_208, 0);
lean::inc(x_269);
x_271 = lean::cnstr_get(x_208, 1);
lean::inc(x_271);
lean::dec(x_208);
lean::inc(x_4);
x_275 = l_lean_elaborator_simple__binders__to__pexpr(x_30, x_4, x_271);
if (lean::obj_tag(x_275) == 0)
{
obj* x_283; obj* x_286; 
lean::dec(x_207);
lean::dec(x_196);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_269);
lean::dec(x_50);
lean::dec(x_57);
x_283 = lean::cnstr_get(x_275, 0);
lean::inc(x_283);
lean::dec(x_275);
if (lean::is_scalar(x_49)) {
 x_286 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_286 = x_49;
 lean::cnstr_set_tag(x_49, 0);
}
lean::cnstr_set(x_286, 0, x_283);
return x_286;
}
else
{
obj* x_288; obj* x_291; obj* x_293; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_303; obj* x_304; obj* x_306; obj* x_307; 
lean::dec(x_49);
x_288 = lean::cnstr_get(x_275, 0);
lean::inc(x_288);
lean::dec(x_275);
x_291 = lean::cnstr_get(x_288, 0);
lean::inc(x_291);
x_293 = lean::cnstr_get(x_288, 1);
lean::inc(x_293);
lean::dec(x_288);
x_296 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_296, 0, x_269);
lean::cnstr_set(x_296, 1, x_55);
x_297 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_297, 0, x_291);
lean::cnstr_set(x_297, 1, x_296);
x_298 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_298, 0, x_207);
lean::cnstr_set(x_298, 1, x_297);
x_299 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_299, 0, x_196);
lean::cnstr_set(x_299, 1, x_298);
x_300 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_300, 0, x_57);
lean::cnstr_set(x_300, 1, x_299);
x_301 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_301, 0, x_50);
lean::cnstr_set(x_301, 1, x_300);
lean::inc(x_205);
x_303 = l_lean_expr_mk__capp(x_205, x_301);
x_304 = l_lean_elaborator_elab__def__like___closed__2;
lean::inc(x_304);
x_306 = lean_expr_mk_mdata(x_304, x_303);
x_307 = l_lean_elaborator_old__elab__command(x_0, x_306, x_4, x_293);
return x_307;
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_37 = x_30;
} else {
 lean::dec(x_30);
 x_37 = lean::box(0);
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
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_57 = x_50;
} else {
 lean::dec(x_50);
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
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 x_77 = x_69;
} else {
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
obj* x_79; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_90; uint8 x_91; obj* x_93; obj* x_94; 
x_79 = lean::cnstr_get(x_69, 0);
lean::inc(x_79);
lean::dec(x_69);
x_82 = lean::cnstr_get(x_79, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_79, 1);
lean::inc(x_84);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 lean::cnstr_release(x_79, 1);
 x_86 = x_79;
} else {
 lean::dec(x_79);
 x_86 = lean::box(0);
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
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 x_109 = x_102;
} else {
 lean::dec(x_102);
 x_109 = lean::box(0);
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
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_118 = x_14;
} else {
 lean::dec(x_14);
 x_118 = lean::box(0);
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
if (lean::is_exclusive(x_119)) {
 lean::cnstr_release(x_119, 0);
 x_125 = x_119;
} else {
 lean::dec(x_119);
 x_125 = lean::box(0);
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
if (lean::is_exclusive(x_119)) {
 lean::cnstr_release(x_119, 0);
 x_129 = x_119;
} else {
 lean::dec(x_119);
 x_129 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_22 = x_16;
} else {
 lean::dec(x_16);
 x_22 = lean::box(0);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_26 = x_16;
} else {
 lean::dec(x_16);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 x_31 = x_24;
} else {
 lean::dec(x_24);
 x_31 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
} else {
 lean::dec(x_1);
 x_13 = lean::box(0);
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
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 x_34 = x_27;
} else {
 lean::dec(x_27);
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
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_80 = x_14;
} else {
 lean::dec(x_14);
 x_80 = lean::box(0);
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
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 x_103 = x_93;
} else {
 lean::dec(x_93);
 x_103 = lean::box(0);
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
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 x_107 = x_93;
} else {
 lean::dec(x_93);
 x_107 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string(".");
x_2 = l_lean_name_to__string__with__sep___main(x_1, x_0);
x_3 = l_lean_parser_substring_of__string(x_2);
x_4 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_0);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set(x_4, 4, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
return x_5;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("constant");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = l_lean_kvmap_set__name(x_0, x_2, x_4);
return x_5;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("inductives");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = l_lean_kvmap_set__name(x_0, x_2, x_4);
return x_5;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("structure");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = l_lean_kvmap_set__name(x_0, x_2, x_4);
return x_5;
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
if (lean::is_exclusive(x_113)) {
 lean::cnstr_release(x_113, 0);
 x_120 = x_113;
} else {
 lean::dec(x_113);
 x_120 = lean::box(0);
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
if (lean::is_exclusive(x_113)) {
 lean::cnstr_release(x_113, 0);
 x_124 = x_113;
} else {
 lean::dec(x_113);
 x_124 = lean::box(0);
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
if (lean::is_exclusive(x_207)) {
 lean::cnstr_release(x_207, 0);
 x_218 = x_207;
} else {
 lean::dec(x_207);
 x_218 = lean::box(0);
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
if (lean::is_exclusive(x_207)) {
 lean::cnstr_release(x_207, 0);
 x_222 = x_207;
} else {
 lean::dec(x_207);
 x_222 = lean::box(0);
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
obj* x_250; obj* x_253; 
lean::dec(x_199);
lean::dec(x_187);
lean::dec(x_223);
lean::dec(x_176);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
x_250 = lean::cnstr_get(x_241, 0);
lean::inc(x_250);
lean::dec(x_241);
if (lean::is_scalar(x_222)) {
 x_253 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_253 = x_222;
 lean::cnstr_set_tag(x_222, 0);
}
lean::cnstr_set(x_253, 0, x_250);
x_5 = x_253;
goto lbl_6;
}
else
{
obj* x_254; obj* x_256; obj* x_257; obj* x_259; obj* x_262; obj* x_263; obj* x_265; obj* x_266; obj* x_267; 
x_254 = lean::cnstr_get(x_241, 0);
lean::inc(x_254);
if (lean::is_exclusive(x_241)) {
 lean::cnstr_release(x_241, 0);
 x_256 = x_241;
} else {
 lean::dec(x_241);
 x_256 = lean::box(0);
}
x_257 = lean::cnstr_get(x_254, 0);
lean::inc(x_257);
x_259 = lean::cnstr_get(x_254, 1);
lean::inc(x_259);
lean::dec(x_254);
x_262 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_262, 0, x_257);
lean::cnstr_set(x_262, 1, x_228);
x_263 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_263);
x_265 = l_lean_expr_mk__capp(x_263, x_262);
if (lean::obj_tag(x_176) == 0)
{
obj* x_269; obj* x_271; 
x_269 = l_lean_expander_get__opt__type___main(x_187);
lean::inc(x_1);
x_271 = l_lean_elaborator_to__pexpr___main(x_269, x_1, x_259);
if (lean::obj_tag(x_176) == 0)
{
if (lean::obj_tag(x_271) == 0)
{
obj* x_280; obj* x_283; 
lean::dec(x_199);
lean::dec(x_222);
lean::dec(x_223);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_265);
x_280 = lean::cnstr_get(x_271, 0);
lean::inc(x_280);
lean::dec(x_271);
if (lean::is_scalar(x_256)) {
 x_283 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_283 = x_256;
 lean::cnstr_set_tag(x_256, 0);
}
lean::cnstr_set(x_283, 0, x_280);
x_5 = x_283;
goto lbl_6;
}
else
{
obj* x_285; 
lean::dec(x_256);
x_285 = lean::cnstr_get(x_271, 0);
lean::inc(x_285);
lean::dec(x_271);
x_266 = x_228;
x_267 = x_285;
goto lbl_268;
}
}
else
{
obj* x_288; 
x_288 = lean::cnstr_get(x_176, 0);
lean::inc(x_288);
lean::dec(x_176);
if (lean::obj_tag(x_271) == 0)
{
obj* x_300; obj* x_303; 
lean::dec(x_199);
lean::dec(x_222);
lean::dec(x_223);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_288);
lean::dec(x_265);
x_300 = lean::cnstr_get(x_271, 0);
lean::inc(x_300);
lean::dec(x_271);
if (lean::is_scalar(x_256)) {
 x_303 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_303 = x_256;
 lean::cnstr_set_tag(x_256, 0);
}
lean::cnstr_set(x_303, 0, x_300);
x_5 = x_303;
goto lbl_6;
}
else
{
obj* x_305; obj* x_308; obj* x_311; 
lean::dec(x_256);
x_305 = lean::cnstr_get(x_271, 0);
lean::inc(x_305);
lean::dec(x_271);
x_308 = lean::cnstr_get(x_288, 1);
lean::inc(x_308);
lean::dec(x_288);
x_311 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_308);
x_266 = x_311;
x_267 = x_305;
goto lbl_268;
}
}
}
else
{
obj* x_312; obj* x_314; obj* x_316; obj* x_318; obj* x_320; obj* x_322; obj* x_324; obj* x_326; obj* x_328; obj* x_332; obj* x_333; obj* x_334; obj* x_336; obj* x_338; obj* x_340; obj* x_342; obj* x_345; obj* x_346; obj* x_348; obj* x_350; obj* x_352; obj* x_354; obj* x_356; obj* x_359; obj* x_360; obj* x_362; 
x_312 = lean::cnstr_get(x_176, 0);
lean::inc(x_312);
x_314 = lean::cnstr_get(x_259, 0);
lean::inc(x_314);
x_316 = lean::cnstr_get(x_259, 1);
lean::inc(x_316);
x_318 = lean::cnstr_get(x_259, 2);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_259, 3);
lean::inc(x_320);
x_322 = lean::cnstr_get(x_259, 4);
lean::inc(x_322);
x_324 = lean::cnstr_get(x_322, 0);
lean::inc(x_324);
x_326 = lean::cnstr_get(x_322, 1);
lean::inc(x_326);
x_328 = lean::cnstr_get(x_312, 1);
lean::inc(x_328);
lean::dec(x_312);
lean::inc(x_328);
x_332 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(x_328);
x_333 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__5(x_326, x_332);
x_334 = lean::cnstr_get(x_322, 2);
lean::inc(x_334);
x_336 = lean::cnstr_get(x_322, 3);
lean::inc(x_336);
x_338 = lean::cnstr_get(x_322, 4);
lean::inc(x_338);
x_340 = lean::cnstr_get(x_322, 5);
lean::inc(x_340);
x_342 = lean::cnstr_get(x_322, 6);
lean::inc(x_342);
lean::dec(x_322);
x_345 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_345, 0, x_324);
lean::cnstr_set(x_345, 1, x_333);
lean::cnstr_set(x_345, 2, x_334);
lean::cnstr_set(x_345, 3, x_336);
lean::cnstr_set(x_345, 4, x_338);
lean::cnstr_set(x_345, 5, x_340);
lean::cnstr_set(x_345, 6, x_342);
x_346 = lean::cnstr_get(x_259, 5);
lean::inc(x_346);
x_348 = lean::cnstr_get(x_259, 6);
lean::inc(x_348);
x_350 = lean::cnstr_get(x_259, 7);
lean::inc(x_350);
x_352 = lean::cnstr_get(x_259, 8);
lean::inc(x_352);
x_354 = lean::cnstr_get(x_259, 9);
lean::inc(x_354);
x_356 = lean::cnstr_get(x_259, 10);
lean::inc(x_356);
lean::dec(x_259);
x_359 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_359, 0, x_314);
lean::cnstr_set(x_359, 1, x_316);
lean::cnstr_set(x_359, 2, x_318);
lean::cnstr_set(x_359, 3, x_320);
lean::cnstr_set(x_359, 4, x_345);
lean::cnstr_set(x_359, 5, x_346);
lean::cnstr_set(x_359, 6, x_348);
lean::cnstr_set(x_359, 7, x_350);
lean::cnstr_set(x_359, 8, x_352);
lean::cnstr_set(x_359, 9, x_354);
lean::cnstr_set(x_359, 10, x_356);
x_360 = l_lean_expander_get__opt__type___main(x_187);
lean::inc(x_1);
x_362 = l_lean_elaborator_to__pexpr___main(x_360, x_1, x_359);
if (lean::obj_tag(x_176) == 0)
{
lean::dec(x_328);
if (lean::obj_tag(x_362) == 0)
{
obj* x_372; obj* x_375; 
lean::dec(x_199);
lean::dec(x_222);
lean::dec(x_223);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_265);
x_372 = lean::cnstr_get(x_362, 0);
lean::inc(x_372);
lean::dec(x_362);
if (lean::is_scalar(x_256)) {
 x_375 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_375 = x_256;
 lean::cnstr_set_tag(x_256, 0);
}
lean::cnstr_set(x_375, 0, x_372);
x_5 = x_375;
goto lbl_6;
}
else
{
obj* x_377; 
lean::dec(x_256);
x_377 = lean::cnstr_get(x_362, 0);
lean::inc(x_377);
lean::dec(x_362);
x_266 = x_228;
x_267 = x_377;
goto lbl_268;
}
}
else
{
lean::dec(x_176);
if (lean::obj_tag(x_362) == 0)
{
obj* x_390; obj* x_393; 
lean::dec(x_199);
lean::dec(x_222);
lean::dec(x_223);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_265);
lean::dec(x_328);
x_390 = lean::cnstr_get(x_362, 0);
lean::inc(x_390);
lean::dec(x_362);
if (lean::is_scalar(x_256)) {
 x_393 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_393 = x_256;
 lean::cnstr_set_tag(x_256, 0);
}
lean::cnstr_set(x_393, 0, x_390);
x_5 = x_393;
goto lbl_6;
}
else
{
obj* x_395; obj* x_398; 
lean::dec(x_256);
x_395 = lean::cnstr_get(x_362, 0);
lean::inc(x_395);
lean::dec(x_362);
x_398 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(x_328);
x_266 = x_398;
x_267 = x_395;
goto lbl_268;
}
}
}
lbl_268:
{
obj* x_399; obj* x_401; obj* x_405; 
x_399 = lean::cnstr_get(x_267, 0);
lean::inc(x_399);
x_401 = lean::cnstr_get(x_267, 1);
lean::inc(x_401);
lean::dec(x_267);
lean::inc(x_1);
x_405 = l_lean_elaborator_simple__binders__to__pexpr(x_199, x_1, x_401);
if (lean::obj_tag(x_405) == 0)
{
obj* x_414; obj* x_417; 
lean::dec(x_223);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_265);
lean::dec(x_399);
lean::dec(x_266);
x_414 = lean::cnstr_get(x_405, 0);
lean::inc(x_414);
lean::dec(x_405);
if (lean::is_scalar(x_222)) {
 x_417 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_417 = x_222;
 lean::cnstr_set_tag(x_222, 0);
}
lean::cnstr_set(x_417, 0, x_414);
x_5 = x_417;
goto lbl_6;
}
else
{
obj* x_418; obj* x_421; obj* x_423; obj* x_429; 
x_418 = lean::cnstr_get(x_405, 0);
lean::inc(x_418);
lean::dec(x_405);
x_421 = lean::cnstr_get(x_418, 0);
lean::inc(x_421);
x_423 = lean::cnstr_get(x_418, 1);
lean::inc(x_423);
lean::dec(x_418);
lean::inc(x_1);
lean::inc(x_182);
lean::inc(x_0);
x_429 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_182, x_1, x_423);
if (lean::obj_tag(x_429) == 0)
{
obj* x_439; obj* x_442; 
lean::dec(x_223);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_265);
lean::dec(x_421);
lean::dec(x_399);
lean::dec(x_266);
x_439 = lean::cnstr_get(x_429, 0);
lean::inc(x_439);
lean::dec(x_429);
if (lean::is_scalar(x_222)) {
 x_442 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_442 = x_222;
 lean::cnstr_set_tag(x_222, 0);
}
lean::cnstr_set(x_442, 0, x_439);
x_5 = x_442;
goto lbl_6;
}
else
{
obj* x_444; obj* x_447; obj* x_449; obj* x_452; obj* x_453; obj* x_456; uint8 x_457; obj* x_459; obj* x_460; obj* x_462; obj* x_464; obj* x_465; obj* x_467; obj* x_468; obj* x_470; obj* x_471; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_482; obj* x_483; obj* x_485; obj* x_486; 
lean::dec(x_222);
x_444 = lean::cnstr_get(x_429, 0);
lean::inc(x_444);
lean::dec(x_429);
x_447 = lean::cnstr_get(x_444, 0);
lean::inc(x_447);
x_449 = lean::cnstr_get(x_444, 1);
lean::inc(x_449);
lean::dec(x_444);
x_452 = l_lean_elaborator_names__to__pexpr(x_266);
x_453 = lean::cnstr_get(x_178, 0);
lean::inc(x_453);
lean::dec(x_178);
x_456 = l_lean_elaborator_mangle__ident(x_453);
x_457 = 0;
lean::inc(x_456);
x_459 = lean_expr_local(x_456, x_456, x_399, x_457);
x_460 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_460, 0, x_459);
lean::cnstr_set(x_460, 1, x_228);
lean::inc(x_263);
x_462 = l_lean_expr_mk__capp(x_263, x_460);
lean::inc(x_263);
x_464 = l_lean_expr_mk__capp(x_263, x_447);
x_465 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_465, 0, x_464);
lean::cnstr_set(x_465, 1, x_228);
lean::inc(x_263);
x_467 = l_lean_expr_mk__capp(x_263, x_465);
x_468 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(x_182);
lean::inc(x_263);
x_470 = l_lean_expr_mk__capp(x_263, x_468);
x_471 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_471, 0, x_470);
lean::cnstr_set(x_471, 1, x_228);
lean::inc(x_263);
x_473 = l_lean_expr_mk__capp(x_263, x_471);
x_474 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_474, 0, x_473);
lean::cnstr_set(x_474, 1, x_228);
x_475 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_475, 0, x_467);
lean::cnstr_set(x_475, 1, x_474);
x_476 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_476, 0, x_421);
lean::cnstr_set(x_476, 1, x_475);
x_477 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_477, 0, x_462);
lean::cnstr_set(x_477, 1, x_476);
x_478 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_478, 0, x_452);
lean::cnstr_set(x_478, 1, x_477);
x_479 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_479, 0, x_265);
lean::cnstr_set(x_479, 1, x_478);
x_480 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_480, 0, x_223);
lean::cnstr_set(x_480, 1, x_479);
lean::inc(x_263);
x_482 = l_lean_expr_mk__capp(x_263, x_480);
x_483 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
lean::inc(x_483);
x_485 = lean_expr_mk_mdata(x_483, x_482);
x_486 = l_lean_elaborator_old__elab__command(x_0, x_485, x_1, x_449);
x_5 = x_486;
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
obj* x_493; obj* x_495; 
lean::dec(x_180);
lean::dec(x_176);
lean::dec(x_174);
lean::dec(x_178);
lean::dec(x_182);
lean::dec(x_11);
x_493 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_493);
x_495 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_493, x_1, x_2);
x_5 = x_495;
goto lbl_6;
}
}
default:
{
obj* x_496; obj* x_499; obj* x_501; obj* x_503; obj* x_505; obj* x_507; obj* x_509; obj* x_511; 
x_496 = lean::cnstr_get(x_12, 0);
lean::inc(x_496);
lean::dec(x_12);
x_499 = lean::cnstr_get(x_496, 0);
lean::inc(x_499);
x_501 = lean::cnstr_get(x_496, 1);
lean::inc(x_501);
x_503 = lean::cnstr_get(x_496, 2);
lean::inc(x_503);
x_505 = lean::cnstr_get(x_496, 3);
lean::inc(x_505);
x_507 = lean::cnstr_get(x_496, 4);
lean::inc(x_507);
x_509 = lean::cnstr_get(x_496, 6);
lean::inc(x_509);
x_511 = lean::cnstr_get(x_496, 7);
lean::inc(x_511);
lean::dec(x_496);
if (lean::obj_tag(x_499) == 0)
{
obj* x_515; obj* x_517; 
lean::dec(x_499);
x_515 = lean::cnstr_get(x_505, 0);
lean::inc(x_515);
x_517 = lean::cnstr_get(x_505, 1);
lean::inc(x_517);
lean::dec(x_505);
if (lean::obj_tag(x_515) == 0)
{
obj* x_528; obj* x_530; 
lean::dec(x_509);
lean::dec(x_507);
lean::dec(x_11);
lean::dec(x_503);
lean::dec(x_501);
lean::dec(x_511);
lean::dec(x_517);
lean::dec(x_515);
x_528 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_528);
x_530 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_528, x_1, x_2);
x_5 = x_530;
goto lbl_6;
}
else
{
obj* x_531; obj* x_534; obj* x_538; 
x_531 = lean::cnstr_get(x_515, 0);
lean::inc(x_531);
lean::dec(x_515);
x_534 = lean::cnstr_get(x_11, 0);
lean::inc(x_534);
lean::dec(x_11);
lean::inc(x_1);
x_538 = l_lean_elaborator_decl__modifiers__to__pexpr(x_534, x_1, x_2);
if (lean::obj_tag(x_538) == 0)
{
obj* x_548; obj* x_550; obj* x_551; 
lean::dec(x_509);
lean::dec(x_507);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_503);
lean::dec(x_501);
lean::dec(x_531);
lean::dec(x_511);
lean::dec(x_517);
x_548 = lean::cnstr_get(x_538, 0);
lean::inc(x_548);
if (lean::is_exclusive(x_538)) {
 lean::cnstr_release(x_538, 0);
 x_550 = x_538;
} else {
 lean::dec(x_538);
 x_550 = lean::box(0);
}
if (lean::is_scalar(x_550)) {
 x_551 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_551 = x_550;
}
lean::cnstr_set(x_551, 0, x_548);
x_5 = x_551;
goto lbl_6;
}
else
{
obj* x_552; obj* x_554; obj* x_555; obj* x_557; obj* x_560; obj* x_561; obj* x_562; 
x_552 = lean::cnstr_get(x_538, 0);
lean::inc(x_552);
if (lean::is_exclusive(x_538)) {
 lean::cnstr_release(x_538, 0);
 x_554 = x_538;
} else {
 lean::dec(x_538);
 x_554 = lean::box(0);
}
x_555 = lean::cnstr_get(x_552, 0);
lean::inc(x_555);
x_557 = lean::cnstr_get(x_552, 1);
lean::inc(x_557);
lean::dec(x_552);
x_560 = lean::box(0);
if (lean::obj_tag(x_501) == 0)
{
obj* x_564; obj* x_566; 
x_564 = l_lean_expander_get__opt__type___main(x_517);
lean::inc(x_1);
x_566 = l_lean_elaborator_to__pexpr___main(x_564, x_1, x_557);
if (lean::obj_tag(x_501) == 0)
{
if (lean::obj_tag(x_566) == 0)
{
obj* x_576; obj* x_578; obj* x_579; 
lean::dec(x_509);
lean::dec(x_555);
lean::dec(x_507);
lean::dec(x_554);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_503);
lean::dec(x_531);
lean::dec(x_511);
x_576 = lean::cnstr_get(x_566, 0);
lean::inc(x_576);
if (lean::is_exclusive(x_566)) {
 lean::cnstr_release(x_566, 0);
 x_578 = x_566;
} else {
 lean::dec(x_566);
 x_578 = lean::box(0);
}
if (lean::is_scalar(x_578)) {
 x_579 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_579 = x_578;
}
lean::cnstr_set(x_579, 0, x_576);
x_5 = x_579;
goto lbl_6;
}
else
{
obj* x_580; 
x_580 = lean::cnstr_get(x_566, 0);
lean::inc(x_580);
lean::dec(x_566);
x_561 = x_560;
x_562 = x_580;
goto lbl_563;
}
}
else
{
obj* x_583; 
x_583 = lean::cnstr_get(x_501, 0);
lean::inc(x_583);
lean::dec(x_501);
if (lean::obj_tag(x_566) == 0)
{
obj* x_596; obj* x_598; obj* x_599; 
lean::dec(x_509);
lean::dec(x_555);
lean::dec(x_507);
lean::dec(x_554);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_503);
lean::dec(x_531);
lean::dec(x_511);
lean::dec(x_583);
x_596 = lean::cnstr_get(x_566, 0);
lean::inc(x_596);
if (lean::is_exclusive(x_566)) {
 lean::cnstr_release(x_566, 0);
 x_598 = x_566;
} else {
 lean::dec(x_566);
 x_598 = lean::box(0);
}
if (lean::is_scalar(x_598)) {
 x_599 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_599 = x_598;
}
lean::cnstr_set(x_599, 0, x_596);
x_5 = x_599;
goto lbl_6;
}
else
{
obj* x_600; obj* x_603; obj* x_606; 
x_600 = lean::cnstr_get(x_566, 0);
lean::inc(x_600);
lean::dec(x_566);
x_603 = lean::cnstr_get(x_583, 1);
lean::inc(x_603);
lean::dec(x_583);
x_606 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(x_603);
x_561 = x_606;
x_562 = x_600;
goto lbl_563;
}
}
}
else
{
obj* x_607; obj* x_609; obj* x_611; obj* x_613; obj* x_615; obj* x_617; obj* x_619; obj* x_621; obj* x_623; obj* x_627; obj* x_628; obj* x_629; obj* x_631; obj* x_633; obj* x_635; obj* x_637; obj* x_640; obj* x_641; obj* x_643; obj* x_645; obj* x_647; obj* x_649; obj* x_651; obj* x_654; obj* x_655; obj* x_657; 
x_607 = lean::cnstr_get(x_501, 0);
lean::inc(x_607);
x_609 = lean::cnstr_get(x_557, 0);
lean::inc(x_609);
x_611 = lean::cnstr_get(x_557, 1);
lean::inc(x_611);
x_613 = lean::cnstr_get(x_557, 2);
lean::inc(x_613);
x_615 = lean::cnstr_get(x_557, 3);
lean::inc(x_615);
x_617 = lean::cnstr_get(x_557, 4);
lean::inc(x_617);
x_619 = lean::cnstr_get(x_617, 0);
lean::inc(x_619);
x_621 = lean::cnstr_get(x_617, 1);
lean::inc(x_621);
x_623 = lean::cnstr_get(x_607, 1);
lean::inc(x_623);
lean::dec(x_607);
lean::inc(x_623);
x_627 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(x_623);
x_628 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(x_621, x_627);
x_629 = lean::cnstr_get(x_617, 2);
lean::inc(x_629);
x_631 = lean::cnstr_get(x_617, 3);
lean::inc(x_631);
x_633 = lean::cnstr_get(x_617, 4);
lean::inc(x_633);
x_635 = lean::cnstr_get(x_617, 5);
lean::inc(x_635);
x_637 = lean::cnstr_get(x_617, 6);
lean::inc(x_637);
lean::dec(x_617);
x_640 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_640, 0, x_619);
lean::cnstr_set(x_640, 1, x_628);
lean::cnstr_set(x_640, 2, x_629);
lean::cnstr_set(x_640, 3, x_631);
lean::cnstr_set(x_640, 4, x_633);
lean::cnstr_set(x_640, 5, x_635);
lean::cnstr_set(x_640, 6, x_637);
x_641 = lean::cnstr_get(x_557, 5);
lean::inc(x_641);
x_643 = lean::cnstr_get(x_557, 6);
lean::inc(x_643);
x_645 = lean::cnstr_get(x_557, 7);
lean::inc(x_645);
x_647 = lean::cnstr_get(x_557, 8);
lean::inc(x_647);
x_649 = lean::cnstr_get(x_557, 9);
lean::inc(x_649);
x_651 = lean::cnstr_get(x_557, 10);
lean::inc(x_651);
lean::dec(x_557);
x_654 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_654, 0, x_609);
lean::cnstr_set(x_654, 1, x_611);
lean::cnstr_set(x_654, 2, x_613);
lean::cnstr_set(x_654, 3, x_615);
lean::cnstr_set(x_654, 4, x_640);
lean::cnstr_set(x_654, 5, x_641);
lean::cnstr_set(x_654, 6, x_643);
lean::cnstr_set(x_654, 7, x_645);
lean::cnstr_set(x_654, 8, x_647);
lean::cnstr_set(x_654, 9, x_649);
lean::cnstr_set(x_654, 10, x_651);
x_655 = l_lean_expander_get__opt__type___main(x_517);
lean::inc(x_1);
x_657 = l_lean_elaborator_to__pexpr___main(x_655, x_1, x_654);
if (lean::obj_tag(x_501) == 0)
{
lean::dec(x_623);
if (lean::obj_tag(x_657) == 0)
{
obj* x_668; obj* x_670; obj* x_671; 
lean::dec(x_509);
lean::dec(x_555);
lean::dec(x_507);
lean::dec(x_554);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_503);
lean::dec(x_531);
lean::dec(x_511);
x_668 = lean::cnstr_get(x_657, 0);
lean::inc(x_668);
if (lean::is_exclusive(x_657)) {
 lean::cnstr_release(x_657, 0);
 x_670 = x_657;
} else {
 lean::dec(x_657);
 x_670 = lean::box(0);
}
if (lean::is_scalar(x_670)) {
 x_671 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_671 = x_670;
}
lean::cnstr_set(x_671, 0, x_668);
x_5 = x_671;
goto lbl_6;
}
else
{
obj* x_672; 
x_672 = lean::cnstr_get(x_657, 0);
lean::inc(x_672);
lean::dec(x_657);
x_561 = x_560;
x_562 = x_672;
goto lbl_563;
}
}
else
{
lean::dec(x_501);
if (lean::obj_tag(x_657) == 0)
{
obj* x_686; obj* x_688; obj* x_689; 
lean::dec(x_509);
lean::dec(x_555);
lean::dec(x_507);
lean::dec(x_554);
lean::dec(x_1);
lean::dec(x_623);
lean::dec(x_0);
lean::dec(x_503);
lean::dec(x_531);
lean::dec(x_511);
x_686 = lean::cnstr_get(x_657, 0);
lean::inc(x_686);
if (lean::is_exclusive(x_657)) {
 lean::cnstr_release(x_657, 0);
 x_688 = x_657;
} else {
 lean::dec(x_657);
 x_688 = lean::box(0);
}
if (lean::is_scalar(x_688)) {
 x_689 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_689 = x_688;
}
lean::cnstr_set(x_689, 0, x_686);
x_5 = x_689;
goto lbl_6;
}
else
{
obj* x_690; obj* x_693; 
x_690 = lean::cnstr_get(x_657, 0);
lean::inc(x_690);
lean::dec(x_657);
x_693 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(x_623);
x_561 = x_693;
x_562 = x_690;
goto lbl_563;
}
}
}
lbl_563:
{
obj* x_694; obj* x_696; obj* x_700; 
x_694 = lean::cnstr_get(x_562, 0);
lean::inc(x_694);
x_696 = lean::cnstr_get(x_562, 1);
lean::inc(x_696);
lean::dec(x_562);
lean::inc(x_1);
x_700 = l_lean_elaborator_simple__binders__to__pexpr(x_531, x_1, x_696);
if (lean::obj_tag(x_700) == 0)
{
obj* x_710; obj* x_713; 
lean::dec(x_509);
lean::dec(x_555);
lean::dec(x_507);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_503);
lean::dec(x_511);
lean::dec(x_561);
lean::dec(x_694);
x_710 = lean::cnstr_get(x_700, 0);
lean::inc(x_710);
lean::dec(x_700);
if (lean::is_scalar(x_554)) {
 x_713 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_713 = x_554;
 lean::cnstr_set_tag(x_554, 0);
}
lean::cnstr_set(x_713, 0, x_710);
x_5 = x_713;
goto lbl_6;
}
else
{
obj* x_714; obj* x_717; obj* x_719; obj* x_722; obj* x_723; obj* x_726; obj* x_727; uint8 x_728; obj* x_731; obj* x_732; 
x_714 = lean::cnstr_get(x_700, 0);
lean::inc(x_714);
lean::dec(x_700);
x_717 = lean::cnstr_get(x_714, 0);
lean::inc(x_717);
x_719 = lean::cnstr_get(x_714, 1);
lean::inc(x_719);
lean::dec(x_714);
x_722 = l_lean_elaborator_names__to__pexpr(x_561);
x_723 = lean::cnstr_get(x_503, 0);
lean::inc(x_723);
lean::dec(x_503);
x_726 = l_lean_elaborator_mangle__ident(x_723);
x_727 = l_lean_elaborator_dummy;
x_728 = 0;
lean::inc(x_727);
lean::inc(x_726);
x_731 = lean_expr_local(x_726, x_726, x_727, x_728);
if (lean::obj_tag(x_507) == 0)
{
x_732 = x_560;
goto lbl_733;
}
else
{
obj* x_734; obj* x_737; 
x_734 = lean::cnstr_get(x_507, 0);
lean::inc(x_734);
lean::dec(x_507);
x_737 = lean::cnstr_get(x_734, 1);
lean::inc(x_737);
lean::dec(x_734);
x_732 = x_737;
goto lbl_733;
}
lbl_733:
{
obj* x_741; 
lean::inc(x_1);
x_741 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_732, x_1, x_719);
if (lean::obj_tag(x_741) == 0)
{
obj* x_751; obj* x_754; 
lean::dec(x_509);
lean::dec(x_555);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_511);
lean::dec(x_694);
lean::dec(x_722);
lean::dec(x_717);
lean::dec(x_731);
x_751 = lean::cnstr_get(x_741, 0);
lean::inc(x_751);
lean::dec(x_741);
if (lean::is_scalar(x_554)) {
 x_754 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_754 = x_554;
 lean::cnstr_set_tag(x_554, 0);
}
lean::cnstr_set(x_754, 0, x_751);
x_5 = x_754;
goto lbl_6;
}
else
{
obj* x_755; obj* x_758; obj* x_760; obj* x_763; obj* x_765; obj* x_768; obj* x_769; 
x_755 = lean::cnstr_get(x_741, 0);
lean::inc(x_755);
lean::dec(x_741);
x_758 = lean::cnstr_get(x_755, 0);
lean::inc(x_758);
x_760 = lean::cnstr_get(x_755, 1);
lean::inc(x_760);
lean::dec(x_755);
x_763 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_763);
x_765 = l_lean_expr_mk__capp(x_763, x_758);
lean::inc(x_1);
lean::inc(x_0);
x_768 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_511, x_1, x_760);
if (lean::obj_tag(x_509) == 0)
{
obj* x_771; 
x_771 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7;
lean::inc(x_771);
x_769 = x_771;
goto lbl_770;
}
else
{
obj* x_773; obj* x_775; obj* x_778; 
x_773 = lean::cnstr_get(x_509, 0);
lean::inc(x_773);
x_775 = lean::cnstr_get(x_773, 0);
lean::inc(x_775);
lean::dec(x_773);
x_778 = l_lean_elaborator_mangle__ident(x_775);
x_769 = x_778;
goto lbl_770;
}
lbl_770:
{
obj* x_781; 
lean::inc(x_727);
lean::inc(x_769);
x_781 = lean_expr_local(x_769, x_769, x_727, x_728);
if (lean::obj_tag(x_509) == 0)
{
if (lean::obj_tag(x_768) == 0)
{
obj* x_791; obj* x_794; 
lean::dec(x_781);
lean::dec(x_765);
lean::dec(x_555);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_694);
lean::dec(x_722);
lean::dec(x_717);
lean::dec(x_731);
x_791 = lean::cnstr_get(x_768, 0);
lean::inc(x_791);
lean::dec(x_768);
if (lean::is_scalar(x_554)) {
 x_794 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_794 = x_554;
 lean::cnstr_set_tag(x_554, 0);
}
lean::cnstr_set(x_794, 0, x_791);
x_5 = x_794;
goto lbl_6;
}
else
{
obj* x_796; obj* x_799; obj* x_801; obj* x_805; obj* x_806; obj* x_807; obj* x_809; obj* x_810; obj* x_811; obj* x_812; obj* x_813; obj* x_814; obj* x_815; obj* x_816; obj* x_818; obj* x_819; obj* x_821; obj* x_822; 
lean::dec(x_554);
x_796 = lean::cnstr_get(x_768, 0);
lean::inc(x_796);
lean::dec(x_768);
x_799 = lean::cnstr_get(x_796, 0);
lean::inc(x_799);
x_801 = lean::cnstr_get(x_796, 1);
lean::inc(x_801);
lean::dec(x_796);
lean::inc(x_763);
x_805 = l_lean_expr_mk__capp(x_763, x_799);
x_806 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_806, 0, x_805);
lean::cnstr_set(x_806, 1, x_560);
x_807 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5;
lean::inc(x_807);
x_809 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_809, 0, x_807);
lean::cnstr_set(x_809, 1, x_806);
x_810 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_810, 0, x_781);
lean::cnstr_set(x_810, 1, x_809);
x_811 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_811, 0, x_694);
lean::cnstr_set(x_811, 1, x_810);
x_812 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_812, 0, x_765);
lean::cnstr_set(x_812, 1, x_811);
x_813 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_813, 0, x_717);
lean::cnstr_set(x_813, 1, x_812);
x_814 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_814, 0, x_731);
lean::cnstr_set(x_814, 1, x_813);
x_815 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_815, 0, x_722);
lean::cnstr_set(x_815, 1, x_814);
x_816 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_816, 0, x_555);
lean::cnstr_set(x_816, 1, x_815);
lean::inc(x_763);
x_818 = l_lean_expr_mk__capp(x_763, x_816);
x_819 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
lean::inc(x_819);
x_821 = lean_expr_mk_mdata(x_819, x_818);
x_822 = l_lean_elaborator_old__elab__command(x_0, x_821, x_1, x_801);
x_5 = x_822;
goto lbl_6;
}
}
else
{
obj* x_823; 
x_823 = lean::cnstr_get(x_509, 0);
lean::inc(x_823);
lean::dec(x_509);
if (lean::obj_tag(x_768) == 0)
{
obj* x_836; obj* x_839; 
lean::dec(x_781);
lean::dec(x_765);
lean::dec(x_555);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_823);
lean::dec(x_694);
lean::dec(x_722);
lean::dec(x_717);
lean::dec(x_731);
x_836 = lean::cnstr_get(x_768, 0);
lean::inc(x_836);
lean::dec(x_768);
if (lean::is_scalar(x_554)) {
 x_839 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_839 = x_554;
 lean::cnstr_set_tag(x_554, 0);
}
lean::cnstr_set(x_839, 0, x_836);
x_5 = x_839;
goto lbl_6;
}
else
{
obj* x_841; obj* x_844; obj* x_846; obj* x_849; obj* x_852; obj* x_854; obj* x_855; obj* x_856; obj* x_857; obj* x_858; obj* x_859; obj* x_860; obj* x_861; obj* x_862; obj* x_863; obj* x_865; obj* x_866; obj* x_868; obj* x_869; 
lean::dec(x_554);
x_841 = lean::cnstr_get(x_768, 0);
lean::inc(x_841);
lean::dec(x_768);
x_844 = lean::cnstr_get(x_841, 0);
lean::inc(x_844);
x_846 = lean::cnstr_get(x_841, 1);
lean::inc(x_846);
lean::dec(x_841);
x_849 = lean::cnstr_get(x_823, 1);
lean::inc(x_849);
lean::dec(x_823);
x_852 = l_lean_elaborator_infer__mod__to__pexpr(x_849);
lean::inc(x_763);
x_854 = l_lean_expr_mk__capp(x_763, x_844);
x_855 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_855, 0, x_854);
lean::cnstr_set(x_855, 1, x_560);
x_856 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_856, 0, x_852);
lean::cnstr_set(x_856, 1, x_855);
x_857 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_857, 0, x_781);
lean::cnstr_set(x_857, 1, x_856);
x_858 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_858, 0, x_694);
lean::cnstr_set(x_858, 1, x_857);
x_859 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_859, 0, x_765);
lean::cnstr_set(x_859, 1, x_858);
x_860 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_860, 0, x_717);
lean::cnstr_set(x_860, 1, x_859);
x_861 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_861, 0, x_731);
lean::cnstr_set(x_861, 1, x_860);
x_862 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_862, 0, x_722);
lean::cnstr_set(x_862, 1, x_861);
x_863 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_863, 0, x_555);
lean::cnstr_set(x_863, 1, x_862);
lean::inc(x_763);
x_865 = l_lean_expr_mk__capp(x_763, x_863);
x_866 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
lean::inc(x_866);
x_868 = lean_expr_mk_mdata(x_866, x_865);
x_869 = l_lean_elaborator_old__elab__command(x_0, x_868, x_1, x_846);
x_5 = x_869;
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
obj* x_878; obj* x_880; 
lean::dec(x_509);
lean::dec(x_507);
lean::dec(x_11);
lean::dec(x_505);
lean::dec(x_503);
lean::dec(x_501);
lean::dec(x_499);
lean::dec(x_511);
x_878 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_878);
x_880 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_878, x_1, x_2);
x_5 = x_880;
goto lbl_6;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_882; obj* x_884; obj* x_885; 
lean::dec(x_3);
x_882 = lean::cnstr_get(x_5, 0);
lean::inc(x_882);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_884 = x_5;
} else {
 lean::dec(x_5);
 x_884 = lean::box(0);
}
if (lean::is_scalar(x_884)) {
 x_885 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_885 = x_884;
}
lean::cnstr_set(x_885, 0, x_882);
return x_885;
}
else
{
obj* x_886; obj* x_888; obj* x_889; obj* x_891; obj* x_892; obj* x_894; obj* x_896; obj* x_898; obj* x_900; obj* x_902; obj* x_904; obj* x_906; obj* x_908; obj* x_910; obj* x_913; obj* x_914; obj* x_915; obj* x_916; 
x_886 = lean::cnstr_get(x_5, 0);
lean::inc(x_886);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_888 = x_5;
} else {
 lean::dec(x_5);
 x_888 = lean::box(0);
}
x_889 = lean::cnstr_get(x_886, 1);
lean::inc(x_889);
if (lean::is_exclusive(x_886)) {
 lean::cnstr_release(x_886, 0);
 lean::cnstr_release(x_886, 1);
 x_891 = x_886;
} else {
 lean::dec(x_886);
 x_891 = lean::box(0);
}
x_892 = lean::cnstr_get(x_889, 0);
lean::inc(x_892);
x_894 = lean::cnstr_get(x_889, 1);
lean::inc(x_894);
x_896 = lean::cnstr_get(x_889, 2);
lean::inc(x_896);
x_898 = lean::cnstr_get(x_889, 3);
lean::inc(x_898);
x_900 = lean::cnstr_get(x_889, 5);
lean::inc(x_900);
x_902 = lean::cnstr_get(x_889, 6);
lean::inc(x_902);
x_904 = lean::cnstr_get(x_889, 7);
lean::inc(x_904);
x_906 = lean::cnstr_get(x_889, 8);
lean::inc(x_906);
x_908 = lean::cnstr_get(x_889, 9);
lean::inc(x_908);
x_910 = lean::cnstr_get(x_889, 10);
lean::inc(x_910);
lean::dec(x_889);
x_913 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_913, 0, x_892);
lean::cnstr_set(x_913, 1, x_894);
lean::cnstr_set(x_913, 2, x_896);
lean::cnstr_set(x_913, 3, x_898);
lean::cnstr_set(x_913, 4, x_3);
lean::cnstr_set(x_913, 5, x_900);
lean::cnstr_set(x_913, 6, x_902);
lean::cnstr_set(x_913, 7, x_904);
lean::cnstr_set(x_913, 8, x_906);
lean::cnstr_set(x_913, 9, x_908);
lean::cnstr_set(x_913, 10, x_910);
x_914 = lean::box(0);
if (lean::is_scalar(x_891)) {
 x_915 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_915 = x_891;
}
lean::cnstr_set(x_915, 0, x_914);
lean::cnstr_set(x_915, 1, x_913);
if (lean::is_scalar(x_888)) {
 x_916 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_916 = x_888;
}
lean::cnstr_set(x_916, 0, x_915);
return x_916;
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
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
lean::dec(x_11);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_18);
return x_20;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_10 = x_0;
} else {
 lean::dec(x_0);
 x_10 = lean::box(0);
}
lean::inc(x_6);
x_14 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_6);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
} else {
 lean::dec(x_14);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 lean::cnstr_release(x_17, 1);
 x_24 = x_17;
} else {
 lean::dec(x_17);
 x_24 = lean::box(0);
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_42 = x_11;
} else {
 lean::dec(x_11);
 x_42 = lean::box(0);
}
x_43 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_8, x_1, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_38);
lean::dec(x_42);
x_48 = lean::cnstr_get(x_43, 0);
lean::inc(x_48);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_50 = x_43;
} else {
 lean::dec(x_43);
 x_50 = lean::box(0);
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
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_54 = x_43;
} else {
 lean::dec(x_43);
 x_54 = lean::box(0);
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
obj* x_81; obj* x_82; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_92; 
lean::dec(x_15);
lean::dec(x_71);
lean::dec(x_73);
x_81 = lean::box(0);
x_82 = l_lean_name_to__string___closed__1;
lean::inc(x_70);
lean::inc(x_82);
x_85 = l_lean_name_to__string__with__sep___main(x_82, x_70);
x_86 = l_lean_parser_substring_of__string(x_85);
x_87 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_87, 0, x_81);
lean::cnstr_set(x_87, 1, x_86);
lean::cnstr_set(x_87, 2, x_70);
lean::cnstr_set(x_87, 3, x_81);
lean::cnstr_set(x_87, 4, x_81);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_87);
x_89 = l_string_join___closed__1;
lean::inc(x_1);
lean::inc(x_89);
x_92 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_88, x_89, x_1, x_2);
if (lean::obj_tag(x_92) == 0)
{
obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_19);
x_98 = lean::cnstr_get(x_92, 0);
lean::inc(x_98);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_100 = x_92;
} else {
 lean::dec(x_92);
 x_100 = lean::box(0);
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
obj* x_102; obj* x_105; uint8 x_108; obj* x_109; obj* x_110; 
x_102 = lean::cnstr_get(x_92, 0);
lean::inc(x_102);
lean::dec(x_92);
x_105 = lean::cnstr_get(x_102, 1);
lean::inc(x_105);
lean::dec(x_102);
x_108 = 0;
x_109 = lean::box(x_108);
if (lean::is_scalar(x_19)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_19;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_105);
x_11 = x_110;
goto lbl_12;
}
}
else
{
obj* x_111; obj* x_114; obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_134; uint8 x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_148; obj* x_149; obj* x_151; obj* x_153; obj* x_155; obj* x_157; obj* x_159; obj* x_162; uint8 x_163; obj* x_164; obj* x_165; 
x_111 = lean::cnstr_get(x_77, 0);
lean::inc(x_111);
lean::dec(x_77);
x_114 = lean::cnstr_get(x_111, 1);
lean::inc(x_114);
lean::dec(x_111);
x_117 = lean::cnstr_get(x_2, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_2, 1);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_2, 2);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_2, 3);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_71, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_71, 1);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_114, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_114, 1);
lean::inc(x_131);
lean::dec(x_114);
x_134 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_134, 0, x_129);
lean::cnstr_set(x_134, 1, x_131);
x_135 = lean::unbox(x_15);
lean::dec(x_15);
lean::cnstr_set_scalar(x_134, sizeof(void*)*2, x_135);
x_137 = x_134;
x_138 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(x_73, x_70, x_137);
x_139 = lean::cnstr_get(x_71, 3);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_71, 4);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_71, 5);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_71, 6);
lean::inc(x_145);
lean::dec(x_71);
x_148 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_148, 0, x_125);
lean::cnstr_set(x_148, 1, x_127);
lean::cnstr_set(x_148, 2, x_138);
lean::cnstr_set(x_148, 3, x_139);
lean::cnstr_set(x_148, 4, x_141);
lean::cnstr_set(x_148, 5, x_143);
lean::cnstr_set(x_148, 6, x_145);
x_149 = lean::cnstr_get(x_2, 5);
lean::inc(x_149);
x_151 = lean::cnstr_get(x_2, 6);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_2, 7);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_2, 8);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_2, 9);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_2, 10);
lean::inc(x_159);
lean::dec(x_2);
x_162 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_162, 0, x_117);
lean::cnstr_set(x_162, 1, x_119);
lean::cnstr_set(x_162, 2, x_121);
lean::cnstr_set(x_162, 3, x_123);
lean::cnstr_set(x_162, 4, x_148);
lean::cnstr_set(x_162, 5, x_149);
lean::cnstr_set(x_162, 6, x_151);
lean::cnstr_set(x_162, 7, x_153);
lean::cnstr_set(x_162, 8, x_155);
lean::cnstr_set(x_162, 9, x_157);
lean::cnstr_set(x_162, 10, x_159);
x_163 = 0;
x_164 = lean::box(x_163);
if (lean::is_scalar(x_19)) {
 x_165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_165 = x_19;
}
lean::cnstr_set(x_165, 0, x_164);
lean::cnstr_set(x_165, 1, x_162);
x_11 = x_165;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("variables");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = l_lean_kvmap_set__name(x_0, x_2, x_4);
return x_5;
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_21 = x_16;
} else {
 lean::dec(x_16);
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
obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_32; 
x_23 = lean::cnstr_get(x_16, 0);
lean::inc(x_23);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_25 = x_16;
} else {
 lean::dec(x_16);
 x_25 = lean::box(0);
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
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 x_61 = x_56;
} else {
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
obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_72; 
x_63 = lean::cnstr_get(x_56, 0);
lean::inc(x_63);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 x_65 = x_56;
} else {
 lean::dec(x_56);
 x_65 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
} else {
 lean::dec(x_0);
 x_7 = lean::box(0);
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
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_35 = x_8;
} else {
 lean::dec(x_8);
 x_35 = lean::box(0);
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
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_39 = x_8;
} else {
 lean::dec(x_8);
 x_39 = lean::box(0);
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
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 x_61 = x_54;
} else {
 lean::dec(x_54);
 x_61 = lean::box(0);
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
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 x_109 = x_52;
} else {
 lean::dec(x_52);
 x_109 = lean::box(0);
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
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 x_113 = x_52;
} else {
 lean::dec(x_52);
 x_113 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_16 = x_8;
} else {
 lean::dec(x_8);
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
x_18 = lean::cnstr_get(x_8, 0);
lean::inc(x_18);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_20 = x_8;
} else {
 lean::dec(x_8);
 x_20 = lean::box(0);
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
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_17 = x_14;
} else {
 lean::dec(x_14);
 x_17 = lean::box(0);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_20 = x_16;
} else {
 lean::dec(x_16);
 x_20 = lean::box(0);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_45 = x_16;
} else {
 lean::dec(x_16);
 x_45 = lean::box(0);
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
} else {
 lean::dec(x_11);
 x_18 = lean::box(0);
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_22 = x_11;
} else {
 lean::dec(x_11);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 x_27 = x_20;
} else {
 lean::dec(x_20);
 x_27 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_2 = x_1;
} else {
 lean::dec(x_1);
 x_2 = lean::box(0);
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
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_9 = x_3;
} else {
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_14 = x_5;
} else {
 lean::dec(x_5);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_10, 2);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_10, 3);
lean::inc(x_21);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 lean::cnstr_release(x_10, 3);
 x_23 = x_10;
} else {
 lean::dec(x_10);
 x_23 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
} else {
 lean::dec(x_0);
 x_7 = lean::box(0);
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
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_30 = x_17;
} else {
 lean::dec(x_17);
 x_30 = lean::box(0);
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
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 x_97 = x_86;
} else {
 lean::dec(x_86);
 x_97 = lean::box(0);
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
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 x_160 = x_95;
} else {
 lean::dec(x_95);
 x_160 = lean::box(0);
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
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 x_172 = x_163;
} else {
 lean::dec(x_163);
 x_172 = lean::box(0);
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
if (lean::is_exclusive(x_161)) {
 lean::cnstr_release(x_161, 0);
 x_253 = x_161;
} else {
 lean::dec(x_161);
 x_253 = lean::box(0);
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
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_266 = x_8;
} else {
 lean::dec(x_8);
 x_266 = lean::box(0);
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
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 x_36 = x_31;
} else {
 lean::dec(x_31);
 x_36 = lean::box(0);
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
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 x_54 = x_51;
} else {
 lean::dec(x_51);
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
obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_76; obj* x_77; obj* x_78; 
x_56 = lean::cnstr_get(x_51, 0);
lean::inc(x_56);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 x_58 = x_51;
} else {
 lean::dec(x_51);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_56, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_56, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_63 = x_56;
} else {
 lean::dec(x_56);
 x_63 = lean::box(0);
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
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_5, x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 4);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 5);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 6);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 7);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 8);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 9);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 10);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_3);
lean::cnstr_set(x_26, 2, x_8);
lean::cnstr_set(x_26, 3, x_9);
lean::cnstr_set(x_26, 4, x_11);
lean::cnstr_set(x_26, 5, x_13);
lean::cnstr_set(x_26, 6, x_15);
lean::cnstr_set(x_26, 7, x_17);
lean::cnstr_set(x_26, 8, x_19);
lean::cnstr_set(x_26, 9, x_21);
lean::cnstr_set(x_26, 10, x_23);
x_27 = l_lean_elaborator_mk__notation__kind___rarg___closed__1;
lean::inc(x_27);
x_29 = lean_name_mk_numeral(x_27, x_5);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_26);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_8 = x_4;
} else {
 lean::dec(x_4);
 x_8 = lean::box(0);
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_12 = x_4;
} else {
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_17 = x_10;
} else {
 lean::dec(x_10);
 x_17 = lean::box(0);
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
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_34; uint8 x_35; obj* x_36; obj* x_37; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_57; obj* x_58; obj* x_59; 
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
lean::inc(x_34);
x_41 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_41, 0, x_30);
lean::cnstr_set(x_41, 1, x_34);
lean::cnstr_set(x_41, 2, x_33);
lean::cnstr_set(x_41, 3, x_36);
lean::cnstr_set(x_41, 4, x_37);
lean::cnstr_set_scalar(x_41, sizeof(void*)*5, x_35);
x_42 = x_41;
x_43 = lean::cnstr_get(x_2, 5);
lean::inc(x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set(x_45, 1, x_43);
x_46 = lean::cnstr_get(x_2, 6);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_2, 7);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_2, 8);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_2, 9);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_2, 10);
lean::inc(x_54);
lean::dec(x_2);
x_57 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_57, 0, x_17);
lean::cnstr_set(x_57, 1, x_19);
lean::cnstr_set(x_57, 2, x_21);
lean::cnstr_set(x_57, 3, x_23);
lean::cnstr_set(x_57, 4, x_25);
lean::cnstr_set(x_57, 5, x_45);
lean::cnstr_set(x_57, 6, x_46);
lean::cnstr_set(x_57, 7, x_48);
lean::cnstr_set(x_57, 8, x_50);
lean::cnstr_set(x_57, 9, x_52);
lean::cnstr_set(x_57, 10, x_54);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_33);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
lbl_8:
{
obj* x_62; 
lean::dec(x_7);
lean::inc(x_1);
x_62 = l_lean_elaborator_notation_elaborate__aux(x_6, x_1, x_2);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_1);
x_64 = lean::cnstr_get(x_62, 0);
lean::inc(x_64);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_66 = x_62;
} else {
 lean::dec(x_62);
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
obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_78; 
x_68 = lean::cnstr_get(x_62, 0);
lean::inc(x_68);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_70 = x_62;
} else {
 lean::dec(x_62);
 x_70 = lean::box(0);
}
x_71 = lean::cnstr_get(x_68, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
lean::dec(x_68);
lean::inc(x_1);
lean::inc(x_71);
x_78 = l_lean_elaborator_register__notation__macro(x_71, x_1, x_73);
if (lean::obj_tag(x_78) == 0)
{
obj* x_81; obj* x_84; 
lean::dec(x_1);
lean::dec(x_71);
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
lean::dec(x_78);
if (lean::is_scalar(x_70)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_70;
 lean::cnstr_set_tag(x_70, 0);
}
lean::cnstr_set(x_84, 0, x_81);
return x_84;
}
else
{
obj* x_86; obj* x_89; obj* x_91; obj* x_94; 
lean::dec(x_70);
x_86 = lean::cnstr_get(x_78, 0);
lean::inc(x_86);
lean::dec(x_78);
x_89 = lean::cnstr_get(x_86, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_86, 1);
lean::inc(x_91);
lean::dec(x_86);
x_94 = lean::cnstr_get(x_71, 0);
lean::inc(x_94);
lean::dec(x_71);
if (lean::obj_tag(x_94) == 0)
{
obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_118; obj* x_121; obj* x_122; 
x_97 = lean::cnstr_get(x_91, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_91, 1);
lean::inc(x_99);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_89);
lean::cnstr_set(x_101, 1, x_99);
x_102 = lean::cnstr_get(x_91, 2);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_91, 3);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_91, 4);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_91, 5);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_91, 6);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_91, 7);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_91, 8);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_91, 9);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_91, 10);
lean::inc(x_118);
lean::dec(x_91);
x_121 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_121, 0, x_97);
lean::cnstr_set(x_121, 1, x_101);
lean::cnstr_set(x_121, 2, x_102);
lean::cnstr_set(x_121, 3, x_104);
lean::cnstr_set(x_121, 4, x_106);
lean::cnstr_set(x_121, 5, x_108);
lean::cnstr_set(x_121, 6, x_110);
lean::cnstr_set(x_121, 7, x_112);
lean::cnstr_set(x_121, 8, x_114);
lean::cnstr_set(x_121, 9, x_116);
lean::cnstr_set(x_121, 10, x_118);
x_122 = l_lean_elaborator_update__parser__config(x_1, x_121);
return x_122;
}
else
{
obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_134; obj* x_136; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_147; obj* x_150; obj* x_151; obj* x_153; obj* x_155; obj* x_157; obj* x_159; obj* x_161; obj* x_164; obj* x_165; 
lean::dec(x_94);
x_124 = lean::cnstr_get(x_91, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_91, 1);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_91, 2);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_91, 3);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_91, 4);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_132, 0);
lean::inc(x_134);
x_136 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_136, 0, x_89);
lean::cnstr_set(x_136, 1, x_134);
x_137 = lean::cnstr_get(x_132, 1);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_132, 2);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_132, 3);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_132, 4);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_132, 5);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_132, 6);
lean::inc(x_147);
lean::dec(x_132);
x_150 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_150, 0, x_136);
lean::cnstr_set(x_150, 1, x_137);
lean::cnstr_set(x_150, 2, x_139);
lean::cnstr_set(x_150, 3, x_141);
lean::cnstr_set(x_150, 4, x_143);
lean::cnstr_set(x_150, 5, x_145);
lean::cnstr_set(x_150, 6, x_147);
x_151 = lean::cnstr_get(x_91, 5);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_91, 6);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_91, 7);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_91, 8);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_91, 9);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_91, 10);
lean::inc(x_161);
lean::dec(x_91);
x_164 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_164, 0, x_124);
lean::cnstr_set(x_164, 1, x_126);
lean::cnstr_set(x_164, 2, x_128);
lean::cnstr_set(x_164, 3, x_130);
lean::cnstr_set(x_164, 4, x_150);
lean::cnstr_set(x_164, 5, x_151);
lean::cnstr_set(x_164, 6, x_153);
lean::cnstr_set(x_164, 7, x_155);
lean::cnstr_set(x_164, 8, x_157);
lean::cnstr_set(x_164, 9, x_159);
lean::cnstr_set(x_164, 10, x_161);
x_165 = l_lean_elaborator_update__parser__config(x_1, x_164);
return x_165;
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_35 = x_29;
} else {
 lean::dec(x_29);
 x_35 = lean::box(0);
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
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_39 = x_29;
} else {
 lean::dec(x_29);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 x_44 = x_37;
} else {
 lean::dec(x_37);
 x_44 = lean::box(0);
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
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_75 = x_70;
} else {
 lean::dec(x_70);
 x_75 = lean::box(0);
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
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_79 = x_70;
} else {
 lean::dec(x_70);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
} else {
 lean::dec(x_77);
 x_84 = lean::box(0);
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
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_102 = x_96;
} else {
 lean::dec(x_96);
 x_102 = lean::box(0);
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
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_106 = x_96;
} else {
 lean::dec(x_96);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_104, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_104, 1);
lean::inc(x_109);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_111 = x_104;
} else {
 lean::dec(x_104);
 x_111 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("attribute");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = l_lean_kvmap_set__name(x_0, x_2, x_4);
return x_5;
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_17 = x_11;
} else {
 lean::dec(x_11);
 x_17 = lean::box(0);
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_21 = x_11;
} else {
 lean::dec(x_11);
 x_21 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("#check");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = l_lean_kvmap_set__name(x_0, x_2, x_4);
return x_5;
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
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_17 = x_12;
} else {
 lean::dec(x_12);
 x_17 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
} else {
 lean::dec(x_1);
 x_8 = lean::box(0);
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_8 = x_4;
} else {
 lean::dec(x_4);
 x_8 = lean::box(0);
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_12 = x_4;
} else {
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_17 = x_10;
} else {
 lean::dec(x_10);
 x_17 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("init_quot");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = l_lean_kvmap_set__name(x_0, x_2, x_4);
x_6 = l_lean_elaborator_dummy;
lean::inc(x_6);
x_8 = lean_expr_mk_mdata(x_5, x_6);
return x_8;
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
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_7 = x_2;
} else {
 lean::dec(x_2);
 x_7 = lean::box(0);
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
} else {
 lean::dec(x_4);
 x_9 = lean::box(0);
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
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
lean::dec(x_1);
x_10 = l_lean_elaborator_current__command___rarg(x_4);
x_11 = lean::box(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__4___boxed), 5, 4);
lean::closure_set(x_12, 0, x_2);
lean::closure_set(x_12, 1, x_3);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_8);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_10);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_1);
x_16 = l_lean_elaborator_current__command___rarg(x_4);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__5), 3, 2);
lean::closure_set(x_17, 0, x_2);
lean::closure_set(x_17, 1, x_3);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_19, 0, x_16);
lean::closure_set(x_19, 1, x_18);
return x_19;
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_6 = x_1;
} else {
 lean::dec(x_1);
 x_6 = lean::box(0);
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
} else {
 lean::dec(x_4);
 x_9 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_5 = x_0;
} else {
 lean::dec(x_0);
 x_5 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_4 = x_1;
} else {
 lean::dec(x_1);
 x_4 = lean::box(0);
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
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_8 = x_3;
} else {
 lean::dec(x_3);
 x_8 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
} else {
 lean::dec(x_0);
 x_12 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
} else {
 lean::dec(x_0);
 x_38 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
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
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_59);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_55);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_51);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_47);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_43);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_39);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_35);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_31);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_27);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_23);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_19);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_15);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_11);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_7);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_3);
lean::cnstr_set(x_80, 1, x_79);
x_81 = l_list_foldl___main___at_lean_elaborator_elaborators___spec__5(x_64, x_80);
return x_81;
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
if (x_3 == 0)
{
obj* x_4; obj* x_7; uint8 x_10; 
x_4 = lean::cnstr_get(x_0, 4);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 4);
lean::inc(x_7);
lean::inc(x_1);
x_10 = l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(x_1, x_7);
if (x_10 == 0)
{
obj* x_11; obj* x_14; uint8 x_15; 
x_11 = lean::cnstr_get(x_4, 5);
lean::inc(x_11);
lean::dec(x_4);
x_14 = l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(x_1, x_11);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
}
else
{
uint8 x_21; 
lean::dec(x_1);
lean::dec(x_4);
x_21 = 1;
return x_21;
}
}
else
{
uint8 x_24; 
lean::dec(x_1);
lean::dec(x_0);
x_24 = 1;
return x_24;
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
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_14 = x_2;
} else {
 lean::dec(x_2);
 x_14 = lean::box(0);
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
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
} else {
 lean::dec(x_2);
 x_9 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
} else {
 lean::dec(x_1);
 x_7 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
} else {
 lean::dec(x_1);
 x_7 = lean::box(0);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
} else {
 lean::dec(x_1);
 x_7 = lean::box(0);
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
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_53 = x_14;
} else {
 lean::dec(x_14);
 x_53 = lean::box(0);
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
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_66 = x_61;
} else {
 lean::dec(x_61);
 x_66 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_19 = x_13;
} else {
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
} else {
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_28 = x_21;
} else {
 lean::dec(x_21);
 x_28 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_5 = x_0;
} else {
 lean::dec(x_0);
 x_5 = lean::box(0);
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
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_13 = x_8;
} else {
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
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_17 = x_8;
} else {
 lean::dec(x_8);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_22 = x_15;
} else {
 lean::dec(x_15);
 x_22 = lean::box(0);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_41 = x_0;
} else {
 lean::dec(x_0);
 x_41 = lean::box(0);
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
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_49 = x_44;
} else {
 lean::dec(x_44);
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
obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_51 = lean::cnstr_get(x_44, 0);
lean::inc(x_51);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_53 = x_44;
} else {
 lean::dec(x_44);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_58 = x_51;
} else {
 lean::dec(x_51);
 x_58 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
lean::cnstr_set(x_2, 2, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
lean::cnstr_set(x_2, 2, x_1);
return x_2;
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
} else {
 lean::dec(x_1);
 x_4 = lean::box(0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_13; 
x_0 = lean::box(0);
x_1 = lean::mk_string("trace");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("as_messages");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = l_lean_options_mk;
x_6 = 1;
lean::inc(x_5);
x_8 = l_lean_kvmap_set__bool(x_5, x_4, x_6);
x_9 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1;
x_10 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2;
lean::inc(x_10);
lean::inc(x_9);
x_13 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set(x_13, 2, x_10);
lean::cnstr_set(x_13, 3, x_0);
lean::cnstr_set(x_13, 4, x_0);
lean::cnstr_set(x_13, 5, x_0);
lean::cnstr_set(x_13, 6, x_8);
return x_13;
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
obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_27; obj* x_28; obj* x_30; 
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
x_18 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_1);
lean::cnstr_set(x_18, 2, x_9);
lean::cnstr_set(x_18, 3, x_1);
lean::cnstr_set(x_18, 4, x_10);
lean::cnstr_set(x_18, 5, x_11);
lean::cnstr_set(x_18, 6, x_2);
lean::cnstr_set(x_18, 7, x_8);
lean::cnstr_set(x_18, 8, x_12);
lean::cnstr_set(x_18, 9, x_13);
lean::cnstr_set(x_18, 10, x_9);
x_19 = l_lean_elaborator_run___closed__4;
x_20 = l_lean_elaborator_run___closed__5;
x_21 = l_lean_elaborator_run___closed__6;
x_22 = l_lean_elaborator_max__recursion;
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
x_27 = l_lean_parser_rec__t_run___at_lean_elaborator_run___spec__5(x_19, x_20, x_21, x_22, x_0, x_18);
x_28 = l_lean_elaborator_run___closed__7;
lean::inc(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_30, 0, x_27);
lean::closure_set(x_30, 1, x_28);
return x_30;
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
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_empty___closed__1);
 l_lean_elaborator_elaborator__t = _init_l_lean_elaborator_elaborator__t();
lean::mark_persistent(l_lean_elaborator_elaborator__t);
 l_lean_elaborator_elaborator__m = _init_l_lean_elaborator_elaborator__m();
lean::mark_persistent(l_lean_elaborator_elaborator__m);
 l_lean_elaborator_elaborator = _init_l_lean_elaborator_elaborator();
lean::mark_persistent(l_lean_elaborator_elaborator);
 l_lean_elaborator_coelaborator__m = _init_l_lean_elaborator_coelaborator__m();
lean::mark_persistent(l_lean_elaborator_coelaborator__m);
 l_lean_elaborator_coelaborator = _init_l_lean_elaborator_coelaborator();
lean::mark_persistent(l_lean_elaborator_coelaborator);
 l_lean_elaborator_elaborator__t___at_lean_elaborator_command_elaborate___spec__2 = _init_l_lean_elaborator_elaborator__t___at_lean_elaborator_command_elaborate___spec__2();
lean::mark_persistent(l_lean_elaborator_elaborator__t___at_lean_elaborator_command_elaborate___spec__2);
 l_lean_elaborator_coelaborator__m_monad__coroutine = _init_l_lean_elaborator_coelaborator__m_monad__coroutine();
lean::mark_persistent(l_lean_elaborator_coelaborator__m_monad__coroutine);
 l_lean_elaborator_current__command___rarg___closed__1 = _init_l_lean_elaborator_current__command___rarg___closed__1();
lean::mark_persistent(l_lean_elaborator_current__command___rarg___closed__1);
 l_lean_elaborator_level__get__app__args___main___closed__1 = _init_l_lean_elaborator_level__get__app__args___main___closed__1();
lean::mark_persistent(l_lean_elaborator_level__get__app__args___main___closed__1);
 l_lean_elaborator_to__level___main___closed__1 = _init_l_lean_elaborator_to__level___main___closed__1();
lean::mark_persistent(l_lean_elaborator_to__level___main___closed__1);
 l_lean_elaborator_to__level___main___closed__2 = _init_l_lean_elaborator_to__level___main___closed__2();
lean::mark_persistent(l_lean_elaborator_to__level___main___closed__2);
 l_lean_elaborator_to__level___main___closed__3 = _init_l_lean_elaborator_to__level___main___closed__3();
lean::mark_persistent(l_lean_elaborator_to__level___main___closed__3);
 l_lean_elaborator_to__level___main___closed__4 = _init_l_lean_elaborator_to__level___main___closed__4();
lean::mark_persistent(l_lean_elaborator_to__level___main___closed__4);
 l_lean_elaborator_expr_mk__annotation___closed__1 = _init_l_lean_elaborator_expr_mk__annotation___closed__1();
lean::mark_persistent(l_lean_elaborator_expr_mk__annotation___closed__1);
 l_lean_elaborator_dummy = _init_l_lean_elaborator_dummy();
lean::mark_persistent(l_lean_elaborator_dummy);
 l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1 = _init_l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1();
lean::mark_persistent(l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1);
 l_lean_elaborator_mk__eqns___closed__1 = _init_l_lean_elaborator_mk__eqns___closed__1();
lean::mark_persistent(l_lean_elaborator_mk__eqns___closed__1);
 l_lean_elaborator_mk__eqns___closed__2 = _init_l_lean_elaborator_mk__eqns___closed__2();
lean::mark_persistent(l_lean_elaborator_mk__eqns___closed__2);
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1);
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1);
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2);
 l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1 = _init_l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1();
lean::mark_persistent(l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1);
 l_lean_elaborator_to__pexpr___main___closed__1 = _init_l_lean_elaborator_to__pexpr___main___closed__1();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__1);
 l_lean_elaborator_to__pexpr___main___closed__2 = _init_l_lean_elaborator_to__pexpr___main___closed__2();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__2);
 l_lean_elaborator_to__pexpr___main___closed__3 = _init_l_lean_elaborator_to__pexpr___main___closed__3();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__3);
 l_lean_elaborator_to__pexpr___main___closed__4 = _init_l_lean_elaborator_to__pexpr___main___closed__4();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__4);
 l_lean_elaborator_to__pexpr___main___closed__5 = _init_l_lean_elaborator_to__pexpr___main___closed__5();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__5);
 l_lean_elaborator_to__pexpr___main___closed__6 = _init_l_lean_elaborator_to__pexpr___main___closed__6();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__6);
 l_lean_elaborator_to__pexpr___main___closed__7 = _init_l_lean_elaborator_to__pexpr___main___closed__7();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__7);
 l_lean_elaborator_to__pexpr___main___closed__8 = _init_l_lean_elaborator_to__pexpr___main___closed__8();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__8);
 l_lean_elaborator_to__pexpr___main___closed__9 = _init_l_lean_elaborator_to__pexpr___main___closed__9();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__9);
 l_lean_elaborator_to__pexpr___main___closed__10 = _init_l_lean_elaborator_to__pexpr___main___closed__10();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__10);
 l_lean_elaborator_to__pexpr___main___closed__11 = _init_l_lean_elaborator_to__pexpr___main___closed__11();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__11);
 l_lean_elaborator_to__pexpr___main___closed__12 = _init_l_lean_elaborator_to__pexpr___main___closed__12();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__12);
 l_lean_elaborator_to__pexpr___main___closed__13 = _init_l_lean_elaborator_to__pexpr___main___closed__13();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__13);
 l_lean_elaborator_to__pexpr___main___closed__14 = _init_l_lean_elaborator_to__pexpr___main___closed__14();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__14);
 l_lean_elaborator_to__pexpr___main___closed__15 = _init_l_lean_elaborator_to__pexpr___main___closed__15();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__15);
 l_lean_elaborator_to__pexpr___main___closed__16 = _init_l_lean_elaborator_to__pexpr___main___closed__16();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__16);
 l_lean_elaborator_to__pexpr___main___closed__17 = _init_l_lean_elaborator_to__pexpr___main___closed__17();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__17);
 l_lean_elaborator_to__pexpr___main___closed__18 = _init_l_lean_elaborator_to__pexpr___main___closed__18();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__18);
 l_lean_elaborator_to__pexpr___main___closed__19 = _init_l_lean_elaborator_to__pexpr___main___closed__19();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__19);
 l_lean_elaborator_to__pexpr___main___closed__20 = _init_l_lean_elaborator_to__pexpr___main___closed__20();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__20);
 l_lean_elaborator_to__pexpr___main___closed__21 = _init_l_lean_elaborator_to__pexpr___main___closed__21();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__21);
 l_lean_elaborator_to__pexpr___main___closed__22 = _init_l_lean_elaborator_to__pexpr___main___closed__22();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__22);
 l_lean_elaborator_to__pexpr___main___closed__23 = _init_l_lean_elaborator_to__pexpr___main___closed__23();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__23);
 l_lean_elaborator_to__pexpr___main___closed__24 = _init_l_lean_elaborator_to__pexpr___main___closed__24();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__24);
 l_lean_elaborator_to__pexpr___main___closed__25 = _init_l_lean_elaborator_to__pexpr___main___closed__25();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__25);
 l_lean_elaborator_to__pexpr___main___closed__26 = _init_l_lean_elaborator_to__pexpr___main___closed__26();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__26);
 l_lean_elaborator_to__pexpr___main___closed__27 = _init_l_lean_elaborator_to__pexpr___main___closed__27();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__27);
 l_lean_elaborator_to__pexpr___main___closed__28 = _init_l_lean_elaborator_to__pexpr___main___closed__28();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__28);
 l_lean_elaborator_to__pexpr___main___closed__29 = _init_l_lean_elaborator_to__pexpr___main___closed__29();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__29);
 l_lean_elaborator_to__pexpr___main___closed__30 = _init_l_lean_elaborator_to__pexpr___main___closed__30();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__30);
 l_lean_elaborator_to__pexpr___main___closed__31 = _init_l_lean_elaborator_to__pexpr___main___closed__31();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__31);
 l_lean_elaborator_to__pexpr___main___closed__32 = _init_l_lean_elaborator_to__pexpr___main___closed__32();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__32);
 l_lean_elaborator_to__pexpr___main___closed__33 = _init_l_lean_elaborator_to__pexpr___main___closed__33();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__33);
 l_lean_elaborator_to__pexpr___main___closed__34 = _init_l_lean_elaborator_to__pexpr___main___closed__34();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__34);
 l_lean_elaborator_to__pexpr___main___closed__35 = _init_l_lean_elaborator_to__pexpr___main___closed__35();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__35);
 l_lean_elaborator_to__pexpr___main___closed__36 = _init_l_lean_elaborator_to__pexpr___main___closed__36();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__36);
 l_lean_elaborator_to__pexpr___main___closed__37 = _init_l_lean_elaborator_to__pexpr___main___closed__37();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__37);
 l_lean_elaborator_to__pexpr___main___closed__38 = _init_l_lean_elaborator_to__pexpr___main___closed__38();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__38);
 l_lean_elaborator_to__pexpr___main___closed__39 = _init_l_lean_elaborator_to__pexpr___main___closed__39();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__39);
 l_lean_elaborator_to__pexpr___main___closed__40 = _init_l_lean_elaborator_to__pexpr___main___closed__40();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__40);
 l_lean_elaborator_to__pexpr___main___closed__41 = _init_l_lean_elaborator_to__pexpr___main___closed__41();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__41);
 l_lean_elaborator_to__pexpr___main___closed__42 = _init_l_lean_elaborator_to__pexpr___main___closed__42();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__42);
 l_lean_elaborator_to__pexpr___main___closed__43 = _init_l_lean_elaborator_to__pexpr___main___closed__43();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__43);
 l_lean_elaborator_to__pexpr___main___closed__44 = _init_l_lean_elaborator_to__pexpr___main___closed__44();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__44);
 l_lean_elaborator_to__pexpr___main___closed__45 = _init_l_lean_elaborator_to__pexpr___main___closed__45();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__45);
 l_lean_elaborator_to__pexpr___main___closed__46 = _init_l_lean_elaborator_to__pexpr___main___closed__46();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__46);
 l_lean_elaborator_to__pexpr___main___closed__47 = _init_l_lean_elaborator_to__pexpr___main___closed__47();
lean::mark_persistent(l_lean_elaborator_to__pexpr___main___closed__47);
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6);
 l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1 = _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1);
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13);
 l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1 = _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1);
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__1 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__1();
lean::mark_persistent(l_lean_elaborator_decl__modifiers__to__pexpr___closed__1);
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__2 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__2();
lean::mark_persistent(l_lean_elaborator_decl__modifiers__to__pexpr___closed__2);
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__3 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__3();
lean::mark_persistent(l_lean_elaborator_decl__modifiers__to__pexpr___closed__3);
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__4 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__4();
lean::mark_persistent(l_lean_elaborator_decl__modifiers__to__pexpr___closed__4);
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__5 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__5();
lean::mark_persistent(l_lean_elaborator_decl__modifiers__to__pexpr___closed__5);
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__6 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__6();
lean::mark_persistent(l_lean_elaborator_decl__modifiers__to__pexpr___closed__6);
 l_lean_elaborator_decl__modifiers__to__pexpr___closed__7 = _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__7();
lean::mark_persistent(l_lean_elaborator_decl__modifiers__to__pexpr___closed__7);
 l_lean_elaborator_locally___rarg___closed__1 = _init_l_lean_elaborator_locally___rarg___closed__1();
lean::mark_persistent(l_lean_elaborator_locally___rarg___closed__1);
 l_lean_elaborator_elab__def__like___closed__1 = _init_l_lean_elaborator_elab__def__like___closed__1();
lean::mark_persistent(l_lean_elaborator_elab__def__like___closed__1);
 l_lean_elaborator_elab__def__like___closed__2 = _init_l_lean_elaborator_elab__def__like___closed__2();
lean::mark_persistent(l_lean_elaborator_elab__def__like___closed__2);
 l_lean_elaborator_infer__mod__to__pexpr___closed__1 = _init_l_lean_elaborator_infer__mod__to__pexpr___closed__1();
lean::mark_persistent(l_lean_elaborator_infer__mod__to__pexpr___closed__1);
 l_lean_elaborator_infer__mod__to__pexpr___closed__2 = _init_l_lean_elaborator_infer__mod__to__pexpr___closed__2();
lean::mark_persistent(l_lean_elaborator_infer__mod__to__pexpr___closed__2);
 l_lean_elaborator_infer__mod__to__pexpr___closed__3 = _init_l_lean_elaborator_infer__mod__to__pexpr___closed__3();
lean::mark_persistent(l_lean_elaborator_infer__mod__to__pexpr___closed__3);
 l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1);
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1);
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2);
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3);
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4);
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5);
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6);
 l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7 = _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7);
 l_lean_elaborator_variables_elaborate___closed__1 = _init_l_lean_elaborator_variables_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_variables_elaborate___closed__1);
 l_lean_elaborator_variables_elaborate___closed__2 = _init_l_lean_elaborator_variables_elaborate___closed__2();
lean::mark_persistent(l_lean_elaborator_variables_elaborate___closed__2);
 l_lean_elaborator_module_header_elaborate___closed__1 = _init_l_lean_elaborator_module_header_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_module_header_elaborate___closed__1);
 l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1 = _init_l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1();
lean::mark_persistent(l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1);
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1);
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2);
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3);
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4);
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5);
 l_lean_elaborator_command__parser__config_register__notation__parser___closed__1 = _init_l_lean_elaborator_command__parser__config_register__notation__parser___closed__1();
lean::mark_persistent(l_lean_elaborator_command__parser__config_register__notation__parser___closed__1);
 l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1 = _init_l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1();
lean::mark_persistent(l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1);
 l_lean_elaborator_yield__to__outside___rarg___closed__1 = _init_l_lean_elaborator_yield__to__outside___rarg___closed__1();
lean::mark_persistent(l_lean_elaborator_yield__to__outside___rarg___closed__1);
 l_lean_elaborator_postprocess__notation__spec___closed__1 = _init_l_lean_elaborator_postprocess__notation__spec___closed__1();
lean::mark_persistent(l_lean_elaborator_postprocess__notation__spec___closed__1);
 l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1);
 l_lean_elaborator_match__spec___closed__1 = _init_l_lean_elaborator_match__spec___closed__1();
lean::mark_persistent(l_lean_elaborator_match__spec___closed__1);
 l_lean_elaborator_notation_elaborate__aux___closed__1 = _init_l_lean_elaborator_notation_elaborate__aux___closed__1();
lean::mark_persistent(l_lean_elaborator_notation_elaborate__aux___closed__1);
 l_lean_elaborator_mk__notation__kind___rarg___closed__1 = _init_l_lean_elaborator_mk__notation__kind___rarg___closed__1();
lean::mark_persistent(l_lean_elaborator_mk__notation__kind___rarg___closed__1);
 l_lean_elaborator_notation_elaborate___closed__1 = _init_l_lean_elaborator_notation_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_notation_elaborate___closed__1);
 l_lean_elaborator_notation_elaborate___closed__2 = _init_l_lean_elaborator_notation_elaborate___closed__2();
lean::mark_persistent(l_lean_elaborator_notation_elaborate___closed__2);
 l_lean_elaborator_universe_elaborate___closed__1 = _init_l_lean_elaborator_universe_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_universe_elaborate___closed__1);
 l_lean_elaborator_universe_elaborate___closed__2 = _init_l_lean_elaborator_universe_elaborate___closed__2();
lean::mark_persistent(l_lean_elaborator_universe_elaborate___closed__2);
 l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1);
 l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2 = _init_l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2);
 l_lean_elaborator_attribute_elaborate___closed__1 = _init_l_lean_elaborator_attribute_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_attribute_elaborate___closed__1);
 l_lean_elaborator_attribute_elaborate___closed__2 = _init_l_lean_elaborator_attribute_elaborate___closed__2();
lean::mark_persistent(l_lean_elaborator_attribute_elaborate___closed__2);
 l_lean_elaborator_check_elaborate___closed__1 = _init_l_lean_elaborator_check_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_check_elaborate___closed__1);
 l_lean_elaborator_init__quot_elaborate___closed__1 = _init_l_lean_elaborator_init__quot_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_init__quot_elaborate___closed__1);
 l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1 = _init_l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1);
 l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1 = _init_l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1();
lean::mark_persistent(l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1);
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1();
lean::mark_persistent(l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1);
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2();
lean::mark_persistent(l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2);
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3();
lean::mark_persistent(l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3);
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4();
lean::mark_persistent(l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4);
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5();
lean::mark_persistent(l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5);
 l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1 = _init_l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1();
lean::mark_persistent(l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1);
 l_lean_elaborator_end__scope___lambda__2___closed__1 = _init_l_lean_elaborator_end__scope___lambda__2___closed__1();
lean::mark_persistent(l_lean_elaborator_end__scope___lambda__2___closed__1);
 l_lean_elaborator_end__scope___lambda__2___closed__2 = _init_l_lean_elaborator_end__scope___lambda__2___closed__2();
lean::mark_persistent(l_lean_elaborator_end__scope___lambda__2___closed__2);
 l_lean_elaborator_end__scope___lambda__3___closed__1 = _init_l_lean_elaborator_end__scope___lambda__3___closed__1();
lean::mark_persistent(l_lean_elaborator_end__scope___lambda__3___closed__1);
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1);
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1);
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2);
 l_lean_elaborator_section_elaborate___lambda__1___closed__1 = _init_l_lean_elaborator_section_elaborate___lambda__1___closed__1();
lean::mark_persistent(l_lean_elaborator_section_elaborate___lambda__1___closed__1);
 l_lean_elaborator_section_elaborate___closed__1 = _init_l_lean_elaborator_section_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_section_elaborate___closed__1);
 l_lean_elaborator_namespace_elaborate___lambda__1___closed__1 = _init_l_lean_elaborator_namespace_elaborate___lambda__1___closed__1();
lean::mark_persistent(l_lean_elaborator_namespace_elaborate___lambda__1___closed__1);
 l_lean_elaborator_namespace_elaborate___closed__1 = _init_l_lean_elaborator_namespace_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_namespace_elaborate___closed__1);
 l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1 = _init_l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1();
lean::mark_persistent(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1);
 l_lean_elaborator_elaborators = _init_l_lean_elaborator_elaborators();
lean::mark_persistent(l_lean_elaborator_elaborators);
 l_lean_elaborator_resolve__context___main___closed__1 = _init_l_lean_elaborator_resolve__context___main___closed__1();
lean::mark_persistent(l_lean_elaborator_resolve__context___main___closed__1);
 l_lean_elaborator_max__recursion = _init_l_lean_elaborator_max__recursion();
lean::mark_persistent(l_lean_elaborator_max__recursion);
 l_lean_elaborator_max__commands = _init_l_lean_elaborator_max__commands();
lean::mark_persistent(l_lean_elaborator_max__commands);
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1);
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2);
 l_lean_elaborator_run___lambda__1___closed__1 = _init_l_lean_elaborator_run___lambda__1___closed__1();
lean::mark_persistent(l_lean_elaborator_run___lambda__1___closed__1);
 l_lean_elaborator_run___lambda__2___closed__1 = _init_l_lean_elaborator_run___lambda__2___closed__1();
lean::mark_persistent(l_lean_elaborator_run___lambda__2___closed__1);
 l_lean_elaborator_run___lambda__4___closed__1 = _init_l_lean_elaborator_run___lambda__4___closed__1();
lean::mark_persistent(l_lean_elaborator_run___lambda__4___closed__1);
 l_lean_elaborator_run___closed__1 = _init_l_lean_elaborator_run___closed__1();
lean::mark_persistent(l_lean_elaborator_run___closed__1);
 l_lean_elaborator_run___closed__2 = _init_l_lean_elaborator_run___closed__2();
lean::mark_persistent(l_lean_elaborator_run___closed__2);
 l_lean_elaborator_run___closed__3 = _init_l_lean_elaborator_run___closed__3();
lean::mark_persistent(l_lean_elaborator_run___closed__3);
 l_lean_elaborator_run___closed__4 = _init_l_lean_elaborator_run___closed__4();
lean::mark_persistent(l_lean_elaborator_run___closed__4);
 l_lean_elaborator_run___closed__5 = _init_l_lean_elaborator_run___closed__5();
lean::mark_persistent(l_lean_elaborator_run___closed__5);
 l_lean_elaborator_run___closed__6 = _init_l_lean_elaborator_run___closed__6();
lean::mark_persistent(l_lean_elaborator_run___closed__6);
 l_lean_elaborator_run___closed__7 = _init_l_lean_elaborator_run___closed__7();
lean::mark_persistent(l_lean_elaborator_run___closed__7);
}
