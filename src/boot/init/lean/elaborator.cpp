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
x_8 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_12 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_14 = x_1;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_23; uint8 x_24; 
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_23 = lean::apply_2(x_0, x_8, x_2);
x_24 = lean::unbox(x_23);
if (x_24 == 0)
{
obj* x_28; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_0);
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_6);
lean::cnstr_set(x_28, 1, x_2);
lean::cnstr_set(x_28, 2, x_3);
lean::cnstr_set(x_28, 3, x_12);
return x_28;
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_12, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_8);
lean::cnstr_set(x_30, 2, x_10);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; 
x_31 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_6, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_8);
lean::cnstr_set(x_32, 2, x_10);
lean::cnstr_set(x_32, 3, x_12);
return x_32;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_45; uint8 x_46; 
x_33 = lean::cnstr_get(x_1, 0);
x_35 = lean::cnstr_get(x_1, 1);
x_37 = lean::cnstr_get(x_1, 2);
x_39 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_41 = x_1;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_1);
 x_41 = lean::box(0);
}
lean::inc(x_35);
lean::inc(x_2);
lean::inc(x_0);
x_45 = lean::apply_2(x_0, x_2, x_35);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_50; uint8 x_51; 
lean::inc(x_2);
lean::inc(x_35);
lean::inc(x_0);
x_50 = lean::apply_2(x_0, x_35, x_2);
x_51 = lean::unbox(x_50);
if (x_51 == 0)
{
obj* x_55; 
lean::dec(x_35);
lean::dec(x_0);
lean::dec(x_37);
if (lean::is_scalar(x_41)) {
 x_55 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_55 = x_41;
}
lean::cnstr_set(x_55, 0, x_33);
lean::cnstr_set(x_55, 1, x_2);
lean::cnstr_set(x_55, 2, x_3);
lean::cnstr_set(x_55, 3, x_39);
return x_55;
}
else
{
uint8 x_57; 
lean::inc(x_39);
x_57 = l_rbnode_get__color___main___rarg(x_39);
if (x_57 == 0)
{
obj* x_59; obj* x_60; 
lean::dec(x_41);
x_59 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_39, x_2, x_3);
x_60 = l_rbnode_balance2__node___main___rarg(x_59, x_35, x_37, x_33);
return x_60;
}
else
{
obj* x_61; obj* x_62; 
x_61 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_41)) {
 x_62 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_62 = x_41;
}
lean::cnstr_set(x_62, 0, x_33);
lean::cnstr_set(x_62, 1, x_35);
lean::cnstr_set(x_62, 2, x_37);
lean::cnstr_set(x_62, 3, x_61);
return x_62;
}
}
}
else
{
uint8 x_64; 
lean::inc(x_33);
x_64 = l_rbnode_get__color___main___rarg(x_33);
if (x_64 == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_41);
x_66 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_33, x_2, x_3);
x_67 = l_rbnode_balance1__node___main___rarg(x_66, x_35, x_37, x_39);
return x_67;
}
else
{
obj* x_68; obj* x_69; 
x_68 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_33, x_2, x_3);
if (lean::is_scalar(x_41)) {
 x_69 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_69 = x_41;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_35);
lean::cnstr_set(x_69, 2, x_37);
lean::cnstr_set(x_69, 3, x_39);
return x_69;
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
default:
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
if (x_21 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_8);
lean::inc(x_3);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_10, x_3);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_30; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_14);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_12);
return x_30;
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
x_8 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_12 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_14 = x_1;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_23; uint8 x_24; 
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_23 = lean::apply_2(x_0, x_8, x_2);
x_24 = lean::unbox(x_23);
if (x_24 == 0)
{
obj* x_28; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_0);
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_6);
lean::cnstr_set(x_28, 1, x_2);
lean::cnstr_set(x_28, 2, x_3);
lean::cnstr_set(x_28, 3, x_12);
return x_28;
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_12, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_8);
lean::cnstr_set(x_30, 2, x_10);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; 
x_31 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_6, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_8);
lean::cnstr_set(x_32, 2, x_10);
lean::cnstr_set(x_32, 3, x_12);
return x_32;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_45; uint8 x_46; 
x_33 = lean::cnstr_get(x_1, 0);
x_35 = lean::cnstr_get(x_1, 1);
x_37 = lean::cnstr_get(x_1, 2);
x_39 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_41 = x_1;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_1);
 x_41 = lean::box(0);
}
lean::inc(x_35);
lean::inc(x_2);
lean::inc(x_0);
x_45 = lean::apply_2(x_0, x_2, x_35);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_50; uint8 x_51; 
lean::inc(x_2);
lean::inc(x_35);
lean::inc(x_0);
x_50 = lean::apply_2(x_0, x_35, x_2);
x_51 = lean::unbox(x_50);
if (x_51 == 0)
{
obj* x_55; 
lean::dec(x_35);
lean::dec(x_0);
lean::dec(x_37);
if (lean::is_scalar(x_41)) {
 x_55 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_55 = x_41;
}
lean::cnstr_set(x_55, 0, x_33);
lean::cnstr_set(x_55, 1, x_2);
lean::cnstr_set(x_55, 2, x_3);
lean::cnstr_set(x_55, 3, x_39);
return x_55;
}
else
{
uint8 x_57; 
lean::inc(x_39);
x_57 = l_rbnode_get__color___main___rarg(x_39);
if (x_57 == 0)
{
obj* x_59; obj* x_60; 
lean::dec(x_41);
x_59 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_39, x_2, x_3);
x_60 = l_rbnode_balance2__node___main___rarg(x_59, x_35, x_37, x_33);
return x_60;
}
else
{
obj* x_61; obj* x_62; 
x_61 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_41)) {
 x_62 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_62 = x_41;
}
lean::cnstr_set(x_62, 0, x_33);
lean::cnstr_set(x_62, 1, x_35);
lean::cnstr_set(x_62, 2, x_37);
lean::cnstr_set(x_62, 3, x_61);
return x_62;
}
}
}
else
{
uint8 x_64; 
lean::inc(x_33);
x_64 = l_rbnode_get__color___main___rarg(x_33);
if (x_64 == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_41);
x_66 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_33, x_2, x_3);
x_67 = l_rbnode_balance1__node___main___rarg(x_66, x_35, x_37, x_39);
return x_67;
}
else
{
obj* x_68; obj* x_69; 
x_68 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_33, x_2, x_3);
if (lean::is_scalar(x_41)) {
 x_69 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_69 = x_41;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_35);
lean::cnstr_set(x_69, 2, x_37);
lean::cnstr_set(x_69, 3, x_39);
return x_69;
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
obj* x_2; obj* x_3; 
x_2 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
x_3 = l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__6___rarg(x_0, x_2, x_1);
return x_3;
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_5 = x_1;
} else {
 lean::inc(x_3);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = l_coroutine_monad___closed__1;
x_1 = l_lean_elaborator_elaborator__t_monad___rarg(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_1);
x_3 = l_except__t_monad___rarg(x_0);
lean::inc(x_3);
x_5 = l_state__t_monad___rarg(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg), 4, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg), 3, 1);
lean::closure_set(x_8, 0, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_yield___rarg), 2, 0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_10, 0, x_8);
lean::closure_set(x_10, 1, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_11, 0, x_7);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_12, 0, x_6);
lean::closure_set(x_12, 1, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_13, 0, x_2);
lean::closure_set(x_13, 1, x_12);
return x_13;
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg___lambda__1), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_lean_elaborator_current__command___rarg___closed__1;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_4, 0, x_3);
lean::closure_set(x_4, 1, x_2);
return x_4;
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
obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; 
lean::inc(x_0);
x_6 = l_lean_parser_syntax_to__format___main(x_0);
x_7 = lean::mk_nat_obj(80u);
x_8 = l_lean_format_pretty(x_6, x_7);
x_9 = l_lean_elaborator_level__get__app__args___main___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_12 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_10, x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_16; uint8 x_17; 
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_16 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_17 = lean_name_dec_eq(x_13, x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_19 = lean_name_dec_eq(x_13, x_18);
lean::dec(x_13);
if (x_19 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; 
lean::inc(x_0);
x_22 = l_lean_parser_syntax_to__format___main(x_0);
x_23 = lean::mk_nat_obj(80u);
x_24 = l_lean_format_pretty(x_22, x_23);
x_25 = l_lean_elaborator_level__get__app__args___main___closed__1;
x_26 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_28 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_26, x_1, x_2);
return x_28;
}
else
{
obj* x_29; obj* x_30; obj* x_34; 
x_29 = l_lean_parser_level_trailing_has__view;
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
lean::dec(x_29);
lean::inc(x_0);
x_34 = lean::apply_1(x_30, x_0);
if (lean::obj_tag(x_34) == 0)
{
obj* x_36; obj* x_39; obj* x_41; 
lean::dec(x_0);
x_36 = lean::cnstr_get(x_34, 0);
lean::inc(x_36);
lean::dec(x_34);
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = l_lean_elaborator_level__get__app__args___main(x_39, x_1, x_2);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_36);
x_43 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_set(x_41, 0, lean::box(0));
 x_45 = x_41;
} else {
 lean::inc(x_43);
 lean::dec(x_41);
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
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_47 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_set(x_41, 0, lean::box(0));
 x_49 = x_41;
} else {
 lean::inc(x_47);
 lean::dec(x_41);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 0);
x_52 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_set(x_47, 0, lean::box(0));
 lean::cnstr_set(x_47, 1, lean::box(0));
 x_54 = x_47;
} else {
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_47);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_50, 0);
x_57 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_set(x_50, 0, lean::box(0));
 lean::cnstr_set(x_50, 1, lean::box(0));
 x_59 = x_50;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::dec(x_50);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_36, 1);
lean::inc(x_60);
lean::dec(x_36);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_57);
if (lean::is_scalar(x_54)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_54;
}
lean::cnstr_set(x_64, 0, x_55);
lean::cnstr_set(x_64, 1, x_63);
if (lean::is_scalar(x_59)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_59;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_52);
if (lean::is_scalar(x_49)) {
 x_66 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_66 = x_49;
}
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_1);
lean::dec(x_34);
x_69 = lean::box(0);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_0);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_2);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_13);
lean::dec(x_1);
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_0);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_2);
x_78 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
return x_78;
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_23 = x_13;
} else {
 lean::inc(x_21);
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
x_26 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 lean::cnstr_set(x_21, 1, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_23 = x_13;
} else {
 lean::inc(x_21);
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
x_26 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 lean::cnstr_set(x_21, 1, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
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
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_10 = x_5;
} else {
 lean::inc(x_8);
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
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_14 = x_5;
} else {
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_12, 0);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_19 = x_12;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
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
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
lean::dec(x_20);
lean::inc(x_0);
x_32 = l_lean_parser_syntax_to__format___main(x_0);
x_33 = lean::mk_nat_obj(80u);
x_34 = l_lean_format_pretty(x_32, x_33);
x_35 = l_lean_elaborator_to__level___main___closed__1;
x_36 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_38 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_36, x_1, x_17);
return x_38;
}
else
{
obj* x_39; obj* x_42; uint8 x_43; 
x_39 = lean::cnstr_get(x_26, 0);
lean::inc(x_39);
lean::dec(x_26);
x_42 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_43 = lean_name_dec_eq(x_39, x_42);
if (x_43 == 0)
{
obj* x_44; uint8 x_45; 
x_44 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_45 = lean_name_dec_eq(x_39, x_44);
lean::dec(x_39);
if (x_45 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_58; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
lean::dec(x_20);
lean::inc(x_0);
x_52 = l_lean_parser_syntax_to__format___main(x_0);
x_53 = lean::mk_nat_obj(80u);
x_54 = l_lean_format_pretty(x_52, x_53);
x_55 = l_lean_elaborator_to__level___main___closed__1;
x_56 = lean::string_append(x_55, x_54);
lean::dec(x_54);
x_58 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_56, x_1, x_17);
return x_58;
}
else
{
obj* x_59; obj* x_60; obj* x_63; 
x_59 = l_lean_parser_level_trailing_has__view;
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
lean::dec(x_59);
x_63 = lean::apply_1(x_60, x_20);
if (lean::obj_tag(x_63) == 0)
{
obj* x_68; obj* x_69; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
lean::dec(x_63);
x_68 = l_lean_elaborator_to__level___main___closed__2;
x_69 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_68, x_1, x_17);
return x_69;
}
else
{
obj* x_70; 
x_70 = lean::cnstr_get(x_63, 0);
lean::inc(x_70);
lean::dec(x_63);
if (lean::obj_tag(x_22) == 0)
{
obj* x_74; obj* x_76; 
lean::dec(x_0);
x_74 = lean::cnstr_get(x_70, 0);
lean::inc(x_74);
x_76 = l_lean_elaborator_to__level___main(x_74, x_1, x_17);
if (lean::obj_tag(x_76) == 0)
{
obj* x_79; obj* x_82; 
lean::dec(x_70);
lean::dec(x_19);
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
lean::dec(x_76);
if (lean::is_scalar(x_14)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_14;
 lean::cnstr_set_tag(x_14, 0);
}
lean::cnstr_set(x_82, 0, x_79);
return x_82;
}
else
{
obj* x_83; obj* x_86; obj* x_88; obj* x_91; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_83 = lean::cnstr_get(x_76, 0);
lean::inc(x_83);
lean::dec(x_76);
x_86 = lean::cnstr_get(x_83, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_83, 1);
lean::inc(x_88);
lean::dec(x_83);
x_91 = lean::cnstr_get(x_70, 2);
lean::inc(x_91);
lean::dec(x_70);
x_94 = l_lean_parser_number_view_to__nat___main(x_91);
x_95 = l_lean_elaborator_level__add___main(x_86, x_94);
if (lean::is_scalar(x_19)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_19;
}
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_88);
if (lean::is_scalar(x_14)) {
 x_97 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_97 = x_14;
}
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
}
else
{
obj* x_102; obj* x_103; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_70);
lean::dec(x_19);
x_102 = l_lean_elaborator_to__level___main___closed__2;
x_103 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_102, x_1, x_17);
return x_103;
}
}
}
}
else
{
obj* x_105; obj* x_106; obj* x_109; 
lean::dec(x_39);
x_105 = l_lean_parser_level_leading_has__view;
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
lean::dec(x_105);
x_109 = lean::apply_1(x_106, x_20);
switch (lean::obj_tag(x_109)) {
case 0:
{
lean::dec(x_109);
if (lean::obj_tag(x_22) == 0)
{
obj* x_113; obj* x_114; 
lean::dec(x_14);
lean::dec(x_19);
x_113 = l_lean_elaborator_to__level___main___closed__2;
x_114 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_113, x_1, x_17);
return x_114;
}
else
{
obj* x_116; obj* x_118; obj* x_122; 
lean::dec(x_0);
x_116 = lean::cnstr_get(x_22, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_22, 1);
lean::inc(x_118);
lean::dec(x_22);
lean::inc(x_1);
x_122 = l_lean_elaborator_to__level___main(x_116, x_1, x_17);
if (lean::obj_tag(x_122) == 0)
{
obj* x_126; obj* x_129; 
lean::dec(x_1);
lean::dec(x_19);
lean::dec(x_118);
x_126 = lean::cnstr_get(x_122, 0);
lean::inc(x_126);
lean::dec(x_122);
if (lean::is_scalar(x_14)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_14;
 lean::cnstr_set_tag(x_14, 0);
}
lean::cnstr_set(x_129, 0, x_126);
return x_129;
}
else
{
obj* x_130; obj* x_133; obj* x_135; obj* x_138; 
x_130 = lean::cnstr_get(x_122, 0);
lean::inc(x_130);
lean::dec(x_122);
x_133 = lean::cnstr_get(x_130, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_130, 1);
lean::inc(x_135);
lean::dec(x_130);
x_138 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_118, x_1, x_135);
if (lean::obj_tag(x_138) == 0)
{
obj* x_141; obj* x_144; 
lean::dec(x_19);
lean::dec(x_133);
x_141 = lean::cnstr_get(x_138, 0);
lean::inc(x_141);
lean::dec(x_138);
if (lean::is_scalar(x_14)) {
 x_144 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_144 = x_14;
 lean::cnstr_set_tag(x_14, 0);
}
lean::cnstr_set(x_144, 0, x_141);
return x_144;
}
else
{
obj* x_145; obj* x_148; obj* x_150; obj* x_153; obj* x_154; obj* x_155; 
x_145 = lean::cnstr_get(x_138, 0);
lean::inc(x_145);
lean::dec(x_138);
x_148 = lean::cnstr_get(x_145, 0);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_145, 1);
lean::inc(x_150);
lean::dec(x_145);
x_153 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(x_133, x_148);
if (lean::is_scalar(x_19)) {
 x_154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_154 = x_19;
}
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_150);
if (lean::is_scalar(x_14)) {
 x_155 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_155 = x_14;
}
lean::cnstr_set(x_155, 0, x_154);
return x_155;
}
}
}
}
case 1:
{
lean::dec(x_109);
if (lean::obj_tag(x_22) == 0)
{
obj* x_159; obj* x_160; 
lean::dec(x_14);
lean::dec(x_19);
x_159 = l_lean_elaborator_to__level___main___closed__2;
x_160 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_159, x_1, x_17);
return x_160;
}
else
{
obj* x_162; obj* x_164; obj* x_168; 
lean::dec(x_0);
x_162 = lean::cnstr_get(x_22, 0);
lean::inc(x_162);
x_164 = lean::cnstr_get(x_22, 1);
lean::inc(x_164);
lean::dec(x_22);
lean::inc(x_1);
x_168 = l_lean_elaborator_to__level___main(x_162, x_1, x_17);
if (lean::obj_tag(x_168) == 0)
{
obj* x_172; obj* x_175; 
lean::dec(x_164);
lean::dec(x_1);
lean::dec(x_19);
x_172 = lean::cnstr_get(x_168, 0);
lean::inc(x_172);
lean::dec(x_168);
if (lean::is_scalar(x_14)) {
 x_175 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_175 = x_14;
 lean::cnstr_set_tag(x_14, 0);
}
lean::cnstr_set(x_175, 0, x_172);
return x_175;
}
else
{
obj* x_176; obj* x_179; obj* x_181; obj* x_184; 
x_176 = lean::cnstr_get(x_168, 0);
lean::inc(x_176);
lean::dec(x_168);
x_179 = lean::cnstr_get(x_176, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_176, 1);
lean::inc(x_181);
lean::dec(x_176);
x_184 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_164, x_1, x_181);
if (lean::obj_tag(x_184) == 0)
{
obj* x_187; obj* x_190; 
lean::dec(x_19);
lean::dec(x_179);
x_187 = lean::cnstr_get(x_184, 0);
lean::inc(x_187);
lean::dec(x_184);
if (lean::is_scalar(x_14)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_14;
 lean::cnstr_set_tag(x_14, 0);
}
lean::cnstr_set(x_190, 0, x_187);
return x_190;
}
else
{
obj* x_191; obj* x_194; obj* x_196; obj* x_199; obj* x_200; obj* x_201; 
x_191 = lean::cnstr_get(x_184, 0);
lean::inc(x_191);
lean::dec(x_184);
x_194 = lean::cnstr_get(x_191, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_191, 1);
lean::inc(x_196);
lean::dec(x_191);
x_199 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(x_179, x_194);
if (lean::is_scalar(x_19)) {
 x_200 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_200 = x_19;
}
lean::cnstr_set(x_200, 0, x_199);
lean::cnstr_set(x_200, 1, x_196);
if (lean::is_scalar(x_14)) {
 x_201 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_201 = x_14;
}
lean::cnstr_set(x_201, 0, x_200);
return x_201;
}
}
}
}
case 2:
{
lean::dec(x_109);
if (lean::obj_tag(x_22) == 0)
{
obj* x_205; obj* x_206; obj* x_207; 
lean::dec(x_1);
lean::dec(x_0);
x_205 = l_lean_elaborator_to__level___main___closed__3;
if (lean::is_scalar(x_19)) {
 x_206 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_206 = x_19;
}
lean::cnstr_set(x_206, 0, x_205);
lean::cnstr_set(x_206, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_207 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_207 = x_14;
}
lean::cnstr_set(x_207, 0, x_206);
return x_207;
}
else
{
obj* x_211; obj* x_212; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
x_211 = l_lean_elaborator_to__level___main___closed__2;
x_212 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_211, x_1, x_17);
return x_212;
}
}
case 3:
{
obj* x_217; obj* x_218; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
lean::dec(x_109);
x_217 = l_lean_elaborator_to__level___main___closed__2;
x_218 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_217, x_1, x_17);
return x_218;
}
case 4:
{
obj* x_219; 
x_219 = lean::cnstr_get(x_109, 0);
lean::inc(x_219);
lean::dec(x_109);
if (lean::obj_tag(x_22) == 0)
{
obj* x_224; obj* x_225; obj* x_226; obj* x_227; 
lean::dec(x_1);
lean::dec(x_0);
x_224 = l_lean_parser_number_view_to__nat___main(x_219);
x_225 = l_lean_level_of__nat___main(x_224);
if (lean::is_scalar(x_19)) {
 x_226 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_226 = x_19;
}
lean::cnstr_set(x_226, 0, x_225);
lean::cnstr_set(x_226, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_227 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_227 = x_14;
}
lean::cnstr_set(x_227, 0, x_226);
return x_227;
}
else
{
obj* x_232; obj* x_233; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_219);
lean::dec(x_19);
x_232 = l_lean_elaborator_to__level___main___closed__2;
x_233 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_232, x_1, x_17);
return x_233;
}
}
default:
{
obj* x_234; 
x_234 = lean::cnstr_get(x_109, 0);
lean::inc(x_234);
lean::dec(x_109);
if (lean::obj_tag(x_22) == 0)
{
obj* x_237; obj* x_238; obj* x_240; obj* x_244; 
x_237 = l_lean_elaborator_mangle__ident(x_234);
x_238 = lean::cnstr_get(x_17, 4);
lean::inc(x_238);
x_240 = lean::cnstr_get(x_238, 1);
lean::inc(x_240);
lean::dec(x_238);
lean::inc(x_237);
x_244 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_240, x_237);
if (lean::obj_tag(x_244) == 0)
{
obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_252; obj* x_253; obj* x_254; 
lean::dec(x_14);
lean::dec(x_19);
x_247 = l_lean_name_to__string___closed__1;
x_248 = l_lean_name_to__string__with__sep___main(x_247, x_237);
x_249 = l_lean_elaborator_to__level___main___closed__4;
x_250 = lean::string_append(x_249, x_248);
lean::dec(x_248);
x_252 = l_char_has__repr___closed__1;
x_253 = lean::string_append(x_250, x_252);
x_254 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_253, x_1, x_17);
return x_254;
}
else
{
obj* x_258; obj* x_259; obj* x_260; 
lean::dec(x_244);
lean::dec(x_1);
lean::dec(x_0);
x_258 = level_mk_param(x_237);
if (lean::is_scalar(x_19)) {
 x_259 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_259 = x_19;
}
lean::cnstr_set(x_259, 0, x_258);
lean::cnstr_set(x_259, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_260 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_260 = x_14;
}
lean::cnstr_set(x_260, 0, x_259);
return x_260;
}
}
else
{
obj* x_265; obj* x_266; 
lean::dec(x_234);
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_19);
x_265 = l_lean_elaborator_to__level___main___closed__2;
x_266 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_265, x_1, x_17);
return x_266;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(0);
x_3 = l_lean_elaborator_expr_mk__annotation___closed__1;
x_4 = l_lean_kvmap_set__name(x_2, x_3, x_0);
x_5 = lean_expr_mk_mdata(x_4, x_1);
return x_5;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_20; uint8 x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
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
x_25 = l_lean_elaborator_expr_mk__annotation(x_24, x_23);
x_26 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_25, x_14);
x_27 = lean_expr_mk_app(x_26, x_16);
if (lean::is_scalar(x_8)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_8;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_20);
return x_28;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(x_0, x_1);
x_3 = l_lean_elaborator_mk__eqns___closed__1;
x_4 = l_lean_expr_mk__capp(x_3, x_2);
x_5 = l_lean_elaborator_mk__eqns___closed__2;
x_6 = l_lean_elaborator_expr_mk__annotation(x_5, x_4);
return x_6;
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_22 = x_16;
} else {
 lean::inc(x_20);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_26 = x_16;
} else {
 lean::inc(x_24);
 lean::dec(x_16);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
x_29 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 lean::cnstr_set(x_24, 1, lean::box(0));
 x_31 = x_24;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 x_22 = x_15;
} else {
 lean::inc(x_20);
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
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 x_26 = x_15;
} else {
 lean::inc(x_24);
 lean::dec(x_15);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
x_29 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 lean::cnstr_set(x_24, 1, lean::box(0));
 x_31 = x_24;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
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
x_51 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_set(x_46, 0, lean::box(0));
 lean::cnstr_set(x_46, 1, lean::box(0));
 x_53 = x_46;
} else {
 lean::inc(x_49);
 lean::inc(x_51);
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
obj* x_64; obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_64 = lean::cnstr_get(x_54, 0);
lean::inc(x_64);
lean::dec(x_54);
x_67 = lean::cnstr_get(x_64, 0);
x_69 = lean::cnstr_get(x_64, 1);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_set(x_64, 0, lean::box(0));
 lean::cnstr_set(x_64, 1, lean::box(0));
 x_71 = x_64;
} else {
 lean::inc(x_67);
 lean::inc(x_69);
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
if (lean::is_scalar(x_53)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_53;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_72);
if (lean::is_scalar(x_11)) {
 x_75 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_75 = x_11;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_67);
if (lean::is_scalar(x_71)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_71;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_69);
if (lean::is_scalar(x_26)) {
 x_77 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_77 = x_26;
}
lean::cnstr_set(x_77, 0, x_76);
return x_77;
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_22 = x_16;
} else {
 lean::inc(x_20);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_26 = x_16;
} else {
 lean::inc(x_24);
 lean::dec(x_16);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
x_29 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 lean::cnstr_set(x_24, 1, lean::box(0));
 x_31 = x_24;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
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
x_19 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_21 = x_16;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
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
x_35 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_set(x_32, 0, lean::box(0));
 lean::cnstr_set(x_32, 1, lean::box(0));
 x_37 = x_32;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
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
x_19 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_21 = x_16;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
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
x_40 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_set(x_37, 0, lean::box(0));
 lean::cnstr_set(x_37, 1, lean::box(0));
 x_42 = x_37;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
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
x_56 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_set(x_53, 0, lean::box(0));
 lean::cnstr_set(x_53, 1, lean::box(0));
 x_58 = x_53;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_31 = x_23;
} else {
 lean::inc(x_29);
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_35 = x_23;
} else {
 lean::inc(x_33);
 lean::dec(x_23);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 0);
x_38 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_set(x_33, 0, lean::box(0));
 lean::cnstr_set(x_33, 1, lean::box(0));
 x_40 = x_33;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
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
obj* x_50; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
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
x_64 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_65 = lean_expr_mk_mdata(x_64, x_36);
if (lean::is_scalar(x_13)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_13;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_40)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_40;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_35)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_35;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_73; 
lean::dec(x_14);
x_70 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_73 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
if (lean::obj_tag(x_73) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_78 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 x_80 = x_73;
} else {
 lean::inc(x_78);
 lean::dec(x_73);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
return x_81;
}
else
{
obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_90; 
x_82 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 x_84 = x_73;
} else {
 lean::inc(x_82);
 lean::dec(x_73);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_82, 0);
x_87 = lean::cnstr_get(x_82, 1);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_set(x_82, 0, lean::box(0));
 lean::cnstr_set(x_82, 1, lean::box(0));
 x_89 = x_82;
} else {
 lean::inc(x_85);
 lean::inc(x_87);
 lean::dec(x_82);
 x_89 = lean::box(0);
}
x_90 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_11, x_2, x_87);
if (lean::obj_tag(x_90) == 0)
{
obj* x_94; obj* x_97; 
lean::dec(x_13);
lean::dec(x_85);
lean::dec(x_89);
x_94 = lean::cnstr_get(x_90, 0);
lean::inc(x_94);
lean::dec(x_90);
if (lean::is_scalar(x_84)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_84;
 lean::cnstr_set_tag(x_84, 0);
}
lean::cnstr_set(x_97, 0, x_94);
return x_97;
}
else
{
obj* x_98; obj* x_101; obj* x_103; obj* x_106; obj* x_107; obj* x_108; 
x_98 = lean::cnstr_get(x_90, 0);
lean::inc(x_98);
lean::dec(x_90);
x_101 = lean::cnstr_get(x_98, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_98, 1);
lean::inc(x_103);
lean::dec(x_98);
if (lean::is_scalar(x_13)) {
 x_106 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_106 = x_13;
}
lean::cnstr_set(x_106, 0, x_85);
lean::cnstr_set(x_106, 1, x_101);
if (lean::is_scalar(x_89)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_89;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_103);
if (lean::is_scalar(x_84)) {
 x_108 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_108 = x_84;
}
lean::cnstr_set(x_108, 0, x_107);
return x_108;
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
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(x_4);
x_8 = lean_expr_mk_app(x_2, x_7);
return x_8;
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_21; 
lean::dec(x_14);
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_21 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_26);
 lean::dec(x_21);
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
obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 x_32 = x_21;
} else {
 lean::inc(x_30);
 lean::dec(x_21);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_30, 0);
x_35 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_set(x_30, 0, lean::box(0));
 lean::cnstr_set(x_30, 1, lean::box(0));
 x_37 = x_30;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_30);
 x_37 = lean::box(0);
}
x_38 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_11, x_2, x_35);
if (lean::obj_tag(x_38) == 0)
{
obj* x_42; obj* x_45; 
lean::dec(x_13);
lean::dec(x_33);
lean::dec(x_37);
x_42 = lean::cnstr_get(x_38, 0);
lean::inc(x_42);
lean::dec(x_38);
if (lean::is_scalar(x_32)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_32;
 lean::cnstr_set_tag(x_32, 0);
}
lean::cnstr_set(x_45, 0, x_42);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_51; obj* x_54; obj* x_55; obj* x_56; 
x_46 = lean::cnstr_get(x_38, 0);
lean::inc(x_46);
lean::dec(x_38);
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
lean::dec(x_46);
if (lean::is_scalar(x_13)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_13;
}
lean::cnstr_set(x_54, 0, x_33);
lean::cnstr_set(x_54, 1, x_49);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_51);
if (lean::is_scalar(x_32)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_32;
}
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
obj* x_57; obj* x_60; 
x_57 = lean::cnstr_get(x_14, 0);
lean::inc(x_57);
lean::dec(x_14);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_60) == 0)
{
obj* x_63; obj* x_66; 
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_66 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_63, x_2, x_3);
if (lean::obj_tag(x_66) == 0)
{
obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_71 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_73 = x_66;
} else {
 lean::inc(x_71);
 lean::dec(x_66);
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
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
x_75 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_77 = x_66;
} else {
 lean::inc(x_75);
 lean::dec(x_66);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 0);
x_80 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 lean::cnstr_set(x_75, 1, lean::box(0));
 x_82 = x_75;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_75);
 x_82 = lean::box(0);
}
x_83 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_11, x_2, x_80);
if (lean::obj_tag(x_83) == 0)
{
obj* x_87; obj* x_90; 
lean::dec(x_13);
lean::dec(x_78);
lean::dec(x_82);
x_87 = lean::cnstr_get(x_83, 0);
lean::inc(x_87);
lean::dec(x_83);
if (lean::is_scalar(x_77)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_77;
 lean::cnstr_set_tag(x_77, 0);
}
lean::cnstr_set(x_90, 0, x_87);
return x_90;
}
else
{
obj* x_91; obj* x_94; obj* x_96; obj* x_99; obj* x_100; obj* x_101; 
x_91 = lean::cnstr_get(x_83, 0);
lean::inc(x_91);
lean::dec(x_83);
x_94 = lean::cnstr_get(x_91, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_91, 1);
lean::inc(x_96);
lean::dec(x_91);
if (lean::is_scalar(x_13)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_13;
}
lean::cnstr_set(x_99, 0, x_78);
lean::cnstr_set(x_99, 1, x_94);
if (lean::is_scalar(x_82)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_82;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_96);
if (lean::is_scalar(x_77)) {
 x_101 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_101 = x_77;
}
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
obj* x_102; obj* x_106; 
x_102 = lean::cnstr_get(x_60, 0);
lean::inc(x_102);
lean::dec(x_60);
lean::inc(x_2);
x_106 = l_lean_elaborator_to__pexpr___main(x_102, x_2, x_3);
if (lean::obj_tag(x_106) == 0)
{
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_111 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_set(x_106, 0, lean::box(0));
 x_113 = x_106;
} else {
 lean::inc(x_111);
 lean::dec(x_106);
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
obj* x_115; obj* x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_123; 
x_115 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_set(x_106, 0, lean::box(0));
 x_117 = x_106;
} else {
 lean::inc(x_115);
 lean::dec(x_106);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_115, 0);
x_120 = lean::cnstr_get(x_115, 1);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_set(x_115, 0, lean::box(0));
 lean::cnstr_set(x_115, 1, lean::box(0));
 x_122 = x_115;
} else {
 lean::inc(x_118);
 lean::inc(x_120);
 lean::dec(x_115);
 x_122 = lean::box(0);
}
x_123 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_11, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_127; obj* x_130; 
lean::dec(x_13);
lean::dec(x_122);
lean::dec(x_118);
x_127 = lean::cnstr_get(x_123, 0);
lean::inc(x_127);
lean::dec(x_123);
if (lean::is_scalar(x_117)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_117;
 lean::cnstr_set_tag(x_117, 0);
}
lean::cnstr_set(x_130, 0, x_127);
return x_130;
}
else
{
obj* x_131; obj* x_134; obj* x_136; obj* x_139; obj* x_140; obj* x_141; 
x_131 = lean::cnstr_get(x_123, 0);
lean::inc(x_131);
lean::dec(x_123);
x_134 = lean::cnstr_get(x_131, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_131, 1);
lean::inc(x_136);
lean::dec(x_131);
if (lean::is_scalar(x_13)) {
 x_139 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_139 = x_13;
}
lean::cnstr_set(x_139, 0, x_118);
lean::cnstr_set(x_139, 1, x_134);
if (lean::is_scalar(x_122)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_122;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_136);
if (lean::is_scalar(x_117)) {
 x_141 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_141 = x_117;
}
lean::cnstr_set(x_141, 0, x_140);
return x_141;
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_31 = x_23;
} else {
 lean::inc(x_29);
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_35 = x_23;
} else {
 lean::inc(x_33);
 lean::dec(x_23);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 0);
x_38 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_set(x_33, 0, lean::box(0));
 lean::cnstr_set(x_33, 1, lean::box(0));
 x_40 = x_33;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
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
obj* x_50; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
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
x_64 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_65 = lean_expr_mk_mdata(x_64, x_36);
if (lean::is_scalar(x_13)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_13;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_40)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_40;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_35)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_35;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_73; 
lean::dec(x_14);
x_70 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_73 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
if (lean::obj_tag(x_73) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_78 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 x_80 = x_73;
} else {
 lean::inc(x_78);
 lean::dec(x_73);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
return x_81;
}
else
{
obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_90; 
x_82 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 x_84 = x_73;
} else {
 lean::inc(x_82);
 lean::dec(x_73);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_82, 0);
x_87 = lean::cnstr_get(x_82, 1);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_set(x_82, 0, lean::box(0));
 lean::cnstr_set(x_82, 1, lean::box(0));
 x_89 = x_82;
} else {
 lean::inc(x_85);
 lean::inc(x_87);
 lean::dec(x_82);
 x_89 = lean::box(0);
}
x_90 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_11, x_2, x_87);
if (lean::obj_tag(x_90) == 0)
{
obj* x_94; obj* x_97; 
lean::dec(x_13);
lean::dec(x_85);
lean::dec(x_89);
x_94 = lean::cnstr_get(x_90, 0);
lean::inc(x_94);
lean::dec(x_90);
if (lean::is_scalar(x_84)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_84;
 lean::cnstr_set_tag(x_84, 0);
}
lean::cnstr_set(x_97, 0, x_94);
return x_97;
}
else
{
obj* x_98; obj* x_101; obj* x_103; obj* x_106; obj* x_107; obj* x_108; 
x_98 = lean::cnstr_get(x_90, 0);
lean::inc(x_98);
lean::dec(x_90);
x_101 = lean::cnstr_get(x_98, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_98, 1);
lean::inc(x_103);
lean::dec(x_98);
if (lean::is_scalar(x_13)) {
 x_106 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_106 = x_13;
}
lean::cnstr_set(x_106, 0, x_85);
lean::cnstr_set(x_106, 1, x_101);
if (lean::is_scalar(x_89)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_89;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_103);
if (lean::is_scalar(x_84)) {
 x_108 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_108 = x_84;
}
lean::cnstr_set(x_108, 0, x_107);
return x_108;
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
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_4);
x_8 = lean_expr_mk_app(x_2, x_7);
return x_8;
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_21; 
lean::dec(x_14);
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_21 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_26);
 lean::dec(x_21);
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
obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 x_32 = x_21;
} else {
 lean::inc(x_30);
 lean::dec(x_21);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_30, 0);
x_35 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_set(x_30, 0, lean::box(0));
 lean::cnstr_set(x_30, 1, lean::box(0));
 x_37 = x_30;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_30);
 x_37 = lean::box(0);
}
x_38 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_11, x_2, x_35);
if (lean::obj_tag(x_38) == 0)
{
obj* x_42; obj* x_45; 
lean::dec(x_13);
lean::dec(x_33);
lean::dec(x_37);
x_42 = lean::cnstr_get(x_38, 0);
lean::inc(x_42);
lean::dec(x_38);
if (lean::is_scalar(x_32)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_32;
 lean::cnstr_set_tag(x_32, 0);
}
lean::cnstr_set(x_45, 0, x_42);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_51; obj* x_54; obj* x_55; obj* x_56; 
x_46 = lean::cnstr_get(x_38, 0);
lean::inc(x_46);
lean::dec(x_38);
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
lean::dec(x_46);
if (lean::is_scalar(x_13)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_13;
}
lean::cnstr_set(x_54, 0, x_33);
lean::cnstr_set(x_54, 1, x_49);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_51);
if (lean::is_scalar(x_32)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_32;
}
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
obj* x_57; obj* x_60; 
x_57 = lean::cnstr_get(x_14, 0);
lean::inc(x_57);
lean::dec(x_14);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_60) == 0)
{
obj* x_63; obj* x_66; 
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_66 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_63, x_2, x_3);
if (lean::obj_tag(x_66) == 0)
{
obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_71 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_73 = x_66;
} else {
 lean::inc(x_71);
 lean::dec(x_66);
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
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
x_75 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_77 = x_66;
} else {
 lean::inc(x_75);
 lean::dec(x_66);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 0);
x_80 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 lean::cnstr_set(x_75, 1, lean::box(0));
 x_82 = x_75;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_75);
 x_82 = lean::box(0);
}
x_83 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_11, x_2, x_80);
if (lean::obj_tag(x_83) == 0)
{
obj* x_87; obj* x_90; 
lean::dec(x_13);
lean::dec(x_78);
lean::dec(x_82);
x_87 = lean::cnstr_get(x_83, 0);
lean::inc(x_87);
lean::dec(x_83);
if (lean::is_scalar(x_77)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_77;
 lean::cnstr_set_tag(x_77, 0);
}
lean::cnstr_set(x_90, 0, x_87);
return x_90;
}
else
{
obj* x_91; obj* x_94; obj* x_96; obj* x_99; obj* x_100; obj* x_101; 
x_91 = lean::cnstr_get(x_83, 0);
lean::inc(x_91);
lean::dec(x_83);
x_94 = lean::cnstr_get(x_91, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_91, 1);
lean::inc(x_96);
lean::dec(x_91);
if (lean::is_scalar(x_13)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_13;
}
lean::cnstr_set(x_99, 0, x_78);
lean::cnstr_set(x_99, 1, x_94);
if (lean::is_scalar(x_82)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_82;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_96);
if (lean::is_scalar(x_77)) {
 x_101 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_101 = x_77;
}
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
obj* x_102; obj* x_106; 
x_102 = lean::cnstr_get(x_60, 0);
lean::inc(x_102);
lean::dec(x_60);
lean::inc(x_2);
x_106 = l_lean_elaborator_to__pexpr___main(x_102, x_2, x_3);
if (lean::obj_tag(x_106) == 0)
{
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_111 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_set(x_106, 0, lean::box(0));
 x_113 = x_106;
} else {
 lean::inc(x_111);
 lean::dec(x_106);
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
obj* x_115; obj* x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_123; 
x_115 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_set(x_106, 0, lean::box(0));
 x_117 = x_106;
} else {
 lean::inc(x_115);
 lean::dec(x_106);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_115, 0);
x_120 = lean::cnstr_get(x_115, 1);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_set(x_115, 0, lean::box(0));
 lean::cnstr_set(x_115, 1, lean::box(0));
 x_122 = x_115;
} else {
 lean::inc(x_118);
 lean::inc(x_120);
 lean::dec(x_115);
 x_122 = lean::box(0);
}
x_123 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_11, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_127; obj* x_130; 
lean::dec(x_13);
lean::dec(x_122);
lean::dec(x_118);
x_127 = lean::cnstr_get(x_123, 0);
lean::inc(x_127);
lean::dec(x_123);
if (lean::is_scalar(x_117)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_117;
 lean::cnstr_set_tag(x_117, 0);
}
lean::cnstr_set(x_130, 0, x_127);
return x_130;
}
else
{
obj* x_131; obj* x_134; obj* x_136; obj* x_139; obj* x_140; obj* x_141; 
x_131 = lean::cnstr_get(x_123, 0);
lean::inc(x_131);
lean::dec(x_123);
x_134 = lean::cnstr_get(x_131, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_131, 1);
lean::inc(x_136);
lean::dec(x_131);
if (lean::is_scalar(x_13)) {
 x_139 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_139 = x_13;
}
lean::cnstr_set(x_139, 0, x_118);
lean::cnstr_set(x_139, 1, x_134);
if (lean::is_scalar(x_122)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_122;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_136);
if (lean::is_scalar(x_117)) {
 x_141 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_141 = x_117;
}
lean::cnstr_set(x_141, 0, x_140);
return x_141;
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_31 = x_23;
} else {
 lean::inc(x_29);
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_35 = x_23;
} else {
 lean::inc(x_33);
 lean::dec(x_23);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 0);
x_38 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_set(x_33, 0, lean::box(0));
 lean::cnstr_set(x_33, 1, lean::box(0));
 x_40 = x_33;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
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
obj* x_50; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
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
x_64 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_65 = lean_expr_mk_mdata(x_64, x_36);
if (lean::is_scalar(x_13)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_13;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_40)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_40;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_35)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_35;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_73; 
lean::dec(x_14);
x_70 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_73 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
if (lean::obj_tag(x_73) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_78 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 x_80 = x_73;
} else {
 lean::inc(x_78);
 lean::dec(x_73);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
return x_81;
}
else
{
obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_90; 
x_82 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 x_84 = x_73;
} else {
 lean::inc(x_82);
 lean::dec(x_73);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_82, 0);
x_87 = lean::cnstr_get(x_82, 1);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_set(x_82, 0, lean::box(0));
 lean::cnstr_set(x_82, 1, lean::box(0));
 x_89 = x_82;
} else {
 lean::inc(x_85);
 lean::inc(x_87);
 lean::dec(x_82);
 x_89 = lean::box(0);
}
x_90 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_11, x_2, x_87);
if (lean::obj_tag(x_90) == 0)
{
obj* x_94; obj* x_97; 
lean::dec(x_13);
lean::dec(x_85);
lean::dec(x_89);
x_94 = lean::cnstr_get(x_90, 0);
lean::inc(x_94);
lean::dec(x_90);
if (lean::is_scalar(x_84)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_84;
 lean::cnstr_set_tag(x_84, 0);
}
lean::cnstr_set(x_97, 0, x_94);
return x_97;
}
else
{
obj* x_98; obj* x_101; obj* x_103; obj* x_106; obj* x_107; obj* x_108; 
x_98 = lean::cnstr_get(x_90, 0);
lean::inc(x_98);
lean::dec(x_90);
x_101 = lean::cnstr_get(x_98, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_98, 1);
lean::inc(x_103);
lean::dec(x_98);
if (lean::is_scalar(x_13)) {
 x_106 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_106 = x_13;
}
lean::cnstr_set(x_106, 0, x_85);
lean::cnstr_set(x_106, 1, x_101);
if (lean::is_scalar(x_89)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_89;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_103);
if (lean::is_scalar(x_84)) {
 x_108 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_108 = x_84;
}
lean::cnstr_set(x_108, 0, x_107);
return x_108;
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
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_4);
x_8 = lean_expr_mk_app(x_2, x_7);
return x_8;
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_21; 
lean::dec(x_14);
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_21 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_26);
 lean::dec(x_21);
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
obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 x_32 = x_21;
} else {
 lean::inc(x_30);
 lean::dec(x_21);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_30, 0);
x_35 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_set(x_30, 0, lean::box(0));
 lean::cnstr_set(x_30, 1, lean::box(0));
 x_37 = x_30;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_30);
 x_37 = lean::box(0);
}
x_38 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_11, x_2, x_35);
if (lean::obj_tag(x_38) == 0)
{
obj* x_42; obj* x_45; 
lean::dec(x_13);
lean::dec(x_33);
lean::dec(x_37);
x_42 = lean::cnstr_get(x_38, 0);
lean::inc(x_42);
lean::dec(x_38);
if (lean::is_scalar(x_32)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_32;
 lean::cnstr_set_tag(x_32, 0);
}
lean::cnstr_set(x_45, 0, x_42);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_51; obj* x_54; obj* x_55; obj* x_56; 
x_46 = lean::cnstr_get(x_38, 0);
lean::inc(x_46);
lean::dec(x_38);
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
lean::dec(x_46);
if (lean::is_scalar(x_13)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_13;
}
lean::cnstr_set(x_54, 0, x_33);
lean::cnstr_set(x_54, 1, x_49);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_51);
if (lean::is_scalar(x_32)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_32;
}
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
obj* x_57; obj* x_60; 
x_57 = lean::cnstr_get(x_14, 0);
lean::inc(x_57);
lean::dec(x_14);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_60) == 0)
{
obj* x_63; obj* x_66; 
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_66 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_63, x_2, x_3);
if (lean::obj_tag(x_66) == 0)
{
obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_71 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_73 = x_66;
} else {
 lean::inc(x_71);
 lean::dec(x_66);
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
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
x_75 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_77 = x_66;
} else {
 lean::inc(x_75);
 lean::dec(x_66);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 0);
x_80 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 lean::cnstr_set(x_75, 1, lean::box(0));
 x_82 = x_75;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_75);
 x_82 = lean::box(0);
}
x_83 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_11, x_2, x_80);
if (lean::obj_tag(x_83) == 0)
{
obj* x_87; obj* x_90; 
lean::dec(x_13);
lean::dec(x_78);
lean::dec(x_82);
x_87 = lean::cnstr_get(x_83, 0);
lean::inc(x_87);
lean::dec(x_83);
if (lean::is_scalar(x_77)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_77;
 lean::cnstr_set_tag(x_77, 0);
}
lean::cnstr_set(x_90, 0, x_87);
return x_90;
}
else
{
obj* x_91; obj* x_94; obj* x_96; obj* x_99; obj* x_100; obj* x_101; 
x_91 = lean::cnstr_get(x_83, 0);
lean::inc(x_91);
lean::dec(x_83);
x_94 = lean::cnstr_get(x_91, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_91, 1);
lean::inc(x_96);
lean::dec(x_91);
if (lean::is_scalar(x_13)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_13;
}
lean::cnstr_set(x_99, 0, x_78);
lean::cnstr_set(x_99, 1, x_94);
if (lean::is_scalar(x_82)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_82;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_96);
if (lean::is_scalar(x_77)) {
 x_101 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_101 = x_77;
}
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
obj* x_102; obj* x_106; 
x_102 = lean::cnstr_get(x_60, 0);
lean::inc(x_102);
lean::dec(x_60);
lean::inc(x_2);
x_106 = l_lean_elaborator_to__pexpr___main(x_102, x_2, x_3);
if (lean::obj_tag(x_106) == 0)
{
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_111 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_set(x_106, 0, lean::box(0));
 x_113 = x_106;
} else {
 lean::inc(x_111);
 lean::dec(x_106);
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
obj* x_115; obj* x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_123; 
x_115 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_set(x_106, 0, lean::box(0));
 x_117 = x_106;
} else {
 lean::inc(x_115);
 lean::dec(x_106);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_115, 0);
x_120 = lean::cnstr_get(x_115, 1);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_set(x_115, 0, lean::box(0));
 lean::cnstr_set(x_115, 1, lean::box(0));
 x_122 = x_115;
} else {
 lean::inc(x_118);
 lean::inc(x_120);
 lean::dec(x_115);
 x_122 = lean::box(0);
}
x_123 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_11, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_127; obj* x_130; 
lean::dec(x_13);
lean::dec(x_122);
lean::dec(x_118);
x_127 = lean::cnstr_get(x_123, 0);
lean::inc(x_127);
lean::dec(x_123);
if (lean::is_scalar(x_117)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_117;
 lean::cnstr_set_tag(x_117, 0);
}
lean::cnstr_set(x_130, 0, x_127);
return x_130;
}
else
{
obj* x_131; obj* x_134; obj* x_136; obj* x_139; obj* x_140; obj* x_141; 
x_131 = lean::cnstr_get(x_123, 0);
lean::inc(x_131);
lean::dec(x_123);
x_134 = lean::cnstr_get(x_131, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_131, 1);
lean::inc(x_136);
lean::dec(x_131);
if (lean::is_scalar(x_13)) {
 x_139 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_139 = x_13;
}
lean::cnstr_set(x_139, 0, x_118);
lean::cnstr_set(x_139, 1, x_134);
if (lean::is_scalar(x_122)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_122;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_136);
if (lean::is_scalar(x_117)) {
 x_141 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_141 = x_117;
}
lean::cnstr_set(x_141, 0, x_140);
return x_141;
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_31 = x_23;
} else {
 lean::inc(x_29);
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
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_35 = x_23;
} else {
 lean::inc(x_33);
 lean::dec(x_23);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 0);
x_38 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_set(x_33, 0, lean::box(0));
 lean::cnstr_set(x_33, 1, lean::box(0));
 x_40 = x_33;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
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
obj* x_50; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
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
x_64 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_65 = lean_expr_mk_mdata(x_64, x_36);
if (lean::is_scalar(x_13)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_13;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_40)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_40;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_35)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_35;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_73; 
lean::dec(x_14);
x_70 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_73 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
if (lean::obj_tag(x_73) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_78 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 x_80 = x_73;
} else {
 lean::inc(x_78);
 lean::dec(x_73);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
return x_81;
}
else
{
obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_90; 
x_82 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 x_84 = x_73;
} else {
 lean::inc(x_82);
 lean::dec(x_73);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_82, 0);
x_87 = lean::cnstr_get(x_82, 1);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_set(x_82, 0, lean::box(0));
 lean::cnstr_set(x_82, 1, lean::box(0));
 x_89 = x_82;
} else {
 lean::inc(x_85);
 lean::inc(x_87);
 lean::dec(x_82);
 x_89 = lean::box(0);
}
x_90 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_11, x_2, x_87);
if (lean::obj_tag(x_90) == 0)
{
obj* x_94; obj* x_97; 
lean::dec(x_13);
lean::dec(x_85);
lean::dec(x_89);
x_94 = lean::cnstr_get(x_90, 0);
lean::inc(x_94);
lean::dec(x_90);
if (lean::is_scalar(x_84)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_84;
 lean::cnstr_set_tag(x_84, 0);
}
lean::cnstr_set(x_97, 0, x_94);
return x_97;
}
else
{
obj* x_98; obj* x_101; obj* x_103; obj* x_106; obj* x_107; obj* x_108; 
x_98 = lean::cnstr_get(x_90, 0);
lean::inc(x_98);
lean::dec(x_90);
x_101 = lean::cnstr_get(x_98, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_98, 1);
lean::inc(x_103);
lean::dec(x_98);
if (lean::is_scalar(x_13)) {
 x_106 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_106 = x_13;
}
lean::cnstr_set(x_106, 0, x_85);
lean::cnstr_set(x_106, 1, x_101);
if (lean::is_scalar(x_89)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_89;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_103);
if (lean::is_scalar(x_84)) {
 x_108 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_108 = x_84;
}
lean::cnstr_set(x_108, 0, x_107);
return x_108;
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
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_4);
x_8 = lean_expr_mk_app(x_2, x_7);
return x_8;
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
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_21; 
lean::dec(x_14);
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_21 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_26);
 lean::dec(x_21);
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
obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 x_32 = x_21;
} else {
 lean::inc(x_30);
 lean::dec(x_21);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_30, 0);
x_35 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_set(x_30, 0, lean::box(0));
 lean::cnstr_set(x_30, 1, lean::box(0));
 x_37 = x_30;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_30);
 x_37 = lean::box(0);
}
x_38 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_11, x_2, x_35);
if (lean::obj_tag(x_38) == 0)
{
obj* x_42; obj* x_45; 
lean::dec(x_13);
lean::dec(x_33);
lean::dec(x_37);
x_42 = lean::cnstr_get(x_38, 0);
lean::inc(x_42);
lean::dec(x_38);
if (lean::is_scalar(x_32)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_32;
 lean::cnstr_set_tag(x_32, 0);
}
lean::cnstr_set(x_45, 0, x_42);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_51; obj* x_54; obj* x_55; obj* x_56; 
x_46 = lean::cnstr_get(x_38, 0);
lean::inc(x_46);
lean::dec(x_38);
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
lean::dec(x_46);
if (lean::is_scalar(x_13)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_13;
}
lean::cnstr_set(x_54, 0, x_33);
lean::cnstr_set(x_54, 1, x_49);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_51);
if (lean::is_scalar(x_32)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_32;
}
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
obj* x_57; obj* x_60; 
x_57 = lean::cnstr_get(x_14, 0);
lean::inc(x_57);
lean::dec(x_14);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_60) == 0)
{
obj* x_63; obj* x_66; 
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_66 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_63, x_2, x_3);
if (lean::obj_tag(x_66) == 0)
{
obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_71 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_73 = x_66;
} else {
 lean::inc(x_71);
 lean::dec(x_66);
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
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
x_75 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_77 = x_66;
} else {
 lean::inc(x_75);
 lean::dec(x_66);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 0);
x_80 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 lean::cnstr_set(x_75, 1, lean::box(0));
 x_82 = x_75;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_75);
 x_82 = lean::box(0);
}
x_83 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_11, x_2, x_80);
if (lean::obj_tag(x_83) == 0)
{
obj* x_87; obj* x_90; 
lean::dec(x_13);
lean::dec(x_78);
lean::dec(x_82);
x_87 = lean::cnstr_get(x_83, 0);
lean::inc(x_87);
lean::dec(x_83);
if (lean::is_scalar(x_77)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_77;
 lean::cnstr_set_tag(x_77, 0);
}
lean::cnstr_set(x_90, 0, x_87);
return x_90;
}
else
{
obj* x_91; obj* x_94; obj* x_96; obj* x_99; obj* x_100; obj* x_101; 
x_91 = lean::cnstr_get(x_83, 0);
lean::inc(x_91);
lean::dec(x_83);
x_94 = lean::cnstr_get(x_91, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_91, 1);
lean::inc(x_96);
lean::dec(x_91);
if (lean::is_scalar(x_13)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_13;
}
lean::cnstr_set(x_99, 0, x_78);
lean::cnstr_set(x_99, 1, x_94);
if (lean::is_scalar(x_82)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_82;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_96);
if (lean::is_scalar(x_77)) {
 x_101 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_101 = x_77;
}
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
obj* x_102; obj* x_106; 
x_102 = lean::cnstr_get(x_60, 0);
lean::inc(x_102);
lean::dec(x_60);
lean::inc(x_2);
x_106 = l_lean_elaborator_to__pexpr___main(x_102, x_2, x_3);
if (lean::obj_tag(x_106) == 0)
{
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_111 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_set(x_106, 0, lean::box(0));
 x_113 = x_106;
} else {
 lean::inc(x_111);
 lean::dec(x_106);
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
obj* x_115; obj* x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_123; 
x_115 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_set(x_106, 0, lean::box(0));
 x_117 = x_106;
} else {
 lean::inc(x_115);
 lean::dec(x_106);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_115, 0);
x_120 = lean::cnstr_get(x_115, 1);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_set(x_115, 0, lean::box(0));
 lean::cnstr_set(x_115, 1, lean::box(0));
 x_122 = x_115;
} else {
 lean::inc(x_118);
 lean::inc(x_120);
 lean::dec(x_115);
 x_122 = lean::box(0);
}
x_123 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_11, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_127; obj* x_130; 
lean::dec(x_13);
lean::dec(x_122);
lean::dec(x_118);
x_127 = lean::cnstr_get(x_123, 0);
lean::inc(x_127);
lean::dec(x_123);
if (lean::is_scalar(x_117)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_117;
 lean::cnstr_set_tag(x_117, 0);
}
lean::cnstr_set(x_130, 0, x_127);
return x_130;
}
else
{
obj* x_131; obj* x_134; obj* x_136; obj* x_139; obj* x_140; obj* x_141; 
x_131 = lean::cnstr_get(x_123, 0);
lean::inc(x_131);
lean::dec(x_123);
x_134 = lean::cnstr_get(x_131, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_131, 1);
lean::inc(x_136);
lean::dec(x_131);
if (lean::is_scalar(x_13)) {
 x_139 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_139 = x_13;
}
lean::cnstr_set(x_139, 0, x_118);
lean::cnstr_set(x_139, 1, x_134);
if (lean::is_scalar(x_122)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_122;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_136);
if (lean::is_scalar(x_117)) {
 x_141 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_141 = x_117;
}
lean::cnstr_set(x_141, 0, x_140);
return x_141;
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_23 = x_13;
} else {
 lean::inc(x_21);
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
x_26 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 lean::cnstr_set(x_21, 1, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_23 = x_13;
} else {
 lean::inc(x_21);
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
x_26 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 lean::cnstr_set(x_21, 1, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
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
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_lean_elaborator_dummy;
x_2 = lean_expr_mk_mvar(x_0, x_1);
return x_2;
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
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_66; 
x_59 = l_lean_name_to__string___closed__1;
x_60 = l_lean_name_to__string__with__sep___main(x_59, x_7);
x_61 = l_lean_elaborator_to__pexpr___main___closed__23;
x_62 = lean::string_append(x_61, x_60);
lean::dec(x_60);
lean::inc(x_1);
lean::inc(x_0);
x_66 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_62, x_1, x_2);
if (lean::obj_tag(x_66) == 0)
{
obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_1);
lean::dec(x_0);
x_69 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
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
obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_80; 
x_73 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_75 = x_66;
} else {
 lean::inc(x_73);
 lean::dec(x_66);
 x_75 = lean::box(0);
}
x_76 = lean::cnstr_get(x_73, 0);
x_78 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 lean::cnstr_set(x_73, 1, lean::box(0));
 x_80 = x_73;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::dec(x_73);
 x_80 = lean::box(0);
}
if (x_21 == 0)
{
obj* x_81; 
x_81 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_81) == 0)
{
obj* x_83; obj* x_84; 
lean::dec(x_1);
if (lean::is_scalar(x_80)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_80;
}
lean::cnstr_set(x_83, 0, x_76);
lean::cnstr_set(x_83, 1, x_78);
if (lean::is_scalar(x_75)) {
 x_84 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_84 = x_75;
}
lean::cnstr_set(x_84, 0, x_83);
return x_84;
}
else
{
obj* x_85; obj* x_88; obj* x_91; obj* x_94; obj* x_95; obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_85 = lean::cnstr_get(x_81, 0);
lean::inc(x_85);
lean::dec(x_81);
x_88 = lean::cnstr_get(x_1, 0);
lean::inc(x_88);
lean::dec(x_1);
x_91 = lean::cnstr_get(x_88, 2);
lean::inc(x_91);
lean::dec(x_88);
x_94 = l_lean_file__map_to__position(x_91, x_85);
x_95 = lean::box(0);
x_96 = lean::cnstr_get(x_94, 1);
lean::inc(x_96);
x_98 = l_lean_elaborator_to__pexpr___main___closed__3;
x_99 = l_lean_kvmap_set__nat(x_95, x_98, x_96);
x_100 = lean::cnstr_get(x_94, 0);
lean::inc(x_100);
lean::dec(x_94);
x_103 = l_lean_elaborator_to__pexpr___main___closed__4;
x_104 = l_lean_kvmap_set__nat(x_99, x_103, x_100);
x_105 = lean_expr_mk_mdata(x_104, x_76);
if (lean::is_scalar(x_80)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_80;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_78);
if (lean::is_scalar(x_75)) {
 x_107 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_107 = x_75;
}
lean::cnstr_set(x_107, 0, x_106);
return x_107;
}
}
else
{
obj* x_110; obj* x_111; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_80)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_80;
}
lean::cnstr_set(x_110, 0, x_76);
lean::cnstr_set(x_110, 1, x_78);
if (lean::is_scalar(x_75)) {
 x_111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_111 = x_75;
}
lean::cnstr_set(x_111, 0, x_110);
return x_111;
}
}
}
else
{
obj* x_112; obj* x_113; obj* x_117; obj* x_118; obj* x_120; obj* x_122; 
x_112 = l_lean_parser_term_match_has__view;
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
lean::dec(x_112);
lean::inc(x_0);
x_117 = lean::apply_1(x_113, x_0);
x_118 = lean::cnstr_get(x_117, 5);
lean::inc(x_118);
x_120 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(x_118);
lean::inc(x_1);
x_122 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_120, x_1, x_2);
if (lean::obj_tag(x_122) == 0)
{
obj* x_124; obj* x_126; obj* x_127; 
lean::dec(x_117);
x_124 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
 lean::cnstr_set(x_122, 0, lean::box(0));
 x_126 = x_122;
} else {
 lean::inc(x_124);
 lean::dec(x_122);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
x_12 = x_127;
goto lbl_13;
}
else
{
obj* x_128; obj* x_130; obj* x_131; obj* x_133; obj* x_135; obj* x_136; obj* x_138; obj* x_140; 
x_128 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
 lean::cnstr_set(x_122, 0, lean::box(0));
 x_130 = x_122;
} else {
 lean::inc(x_128);
 lean::dec(x_122);
 x_130 = lean::box(0);
}
x_131 = lean::cnstr_get(x_128, 0);
x_133 = lean::cnstr_get(x_128, 1);
if (lean::is_exclusive(x_128)) {
 lean::cnstr_set(x_128, 0, lean::box(0));
 lean::cnstr_set(x_128, 1, lean::box(0));
 x_135 = x_128;
} else {
 lean::inc(x_131);
 lean::inc(x_133);
 lean::dec(x_128);
 x_135 = lean::box(0);
}
x_136 = lean::cnstr_get(x_117, 2);
lean::inc(x_136);
x_138 = l_lean_expander_get__opt__type___main(x_136);
lean::inc(x_1);
x_140 = l_lean_elaborator_to__pexpr___main(x_138, x_1, x_133);
if (lean::obj_tag(x_140) == 0)
{
obj* x_144; obj* x_147; 
lean::dec(x_131);
lean::dec(x_135);
lean::dec(x_117);
x_144 = lean::cnstr_get(x_140, 0);
lean::inc(x_144);
lean::dec(x_140);
if (lean::is_scalar(x_130)) {
 x_147 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_147 = x_130;
 lean::cnstr_set_tag(x_130, 0);
}
lean::cnstr_set(x_147, 0, x_144);
x_12 = x_147;
goto lbl_13;
}
else
{
obj* x_148; obj* x_151; obj* x_153; obj* x_156; 
x_148 = lean::cnstr_get(x_140, 0);
lean::inc(x_148);
lean::dec(x_140);
x_151 = lean::cnstr_get(x_148, 0);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_148, 1);
lean::inc(x_153);
lean::dec(x_148);
x_156 = l_lean_elaborator_mk__eqns(x_151, x_131);
switch (lean::obj_tag(x_156)) {
case 10:
{
obj* x_157; obj* x_159; obj* x_162; obj* x_166; 
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_156, 1);
lean::inc(x_159);
lean::dec(x_156);
x_162 = lean::cnstr_get(x_117, 1);
lean::inc(x_162);
lean::dec(x_117);
lean::inc(x_1);
x_166 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_162, x_1, x_153);
if (lean::obj_tag(x_166) == 0)
{
obj* x_170; obj* x_173; 
lean::dec(x_135);
lean::dec(x_157);
lean::dec(x_159);
x_170 = lean::cnstr_get(x_166, 0);
lean::inc(x_170);
lean::dec(x_166);
if (lean::is_scalar(x_130)) {
 x_173 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_173 = x_130;
 lean::cnstr_set_tag(x_130, 0);
}
lean::cnstr_set(x_173, 0, x_170);
x_12 = x_173;
goto lbl_13;
}
else
{
obj* x_174; obj* x_177; obj* x_179; obj* x_182; uint8 x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
x_174 = lean::cnstr_get(x_166, 0);
lean::inc(x_174);
lean::dec(x_166);
x_177 = lean::cnstr_get(x_174, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_174, 1);
lean::inc(x_179);
lean::dec(x_174);
x_182 = l_lean_elaborator_to__pexpr___main___closed__24;
x_183 = 1;
x_184 = l_lean_kvmap_set__bool(x_157, x_182, x_183);
x_185 = lean_expr_mk_mdata(x_184, x_159);
x_186 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_185, x_177);
if (lean::is_scalar(x_135)) {
 x_187 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_187 = x_135;
}
lean::cnstr_set(x_187, 0, x_186);
lean::cnstr_set(x_187, 1, x_179);
if (lean::is_scalar(x_130)) {
 x_188 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_188 = x_130;
}
lean::cnstr_set(x_188, 0, x_187);
x_12 = x_188;
goto lbl_13;
}
}
default:
{
obj* x_193; obj* x_196; 
lean::dec(x_130);
lean::dec(x_135);
lean::dec(x_117);
lean::dec(x_156);
x_193 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_1);
lean::inc(x_0);
x_196 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_193, x_1, x_153);
x_12 = x_196;
goto lbl_13;
}
}
}
}
}
}
else
{
obj* x_197; obj* x_198; obj* x_202; obj* x_203; obj* x_205; obj* x_206; obj* x_208; obj* x_210; obj* x_211; obj* x_212; obj* x_214; obj* x_216; 
x_197 = l_lean_parser_term_struct__inst_has__view;
x_198 = lean::cnstr_get(x_197, 0);
lean::inc(x_198);
lean::dec(x_197);
lean::inc(x_0);
x_202 = lean::apply_1(x_198, x_0);
x_203 = lean::cnstr_get(x_202, 3);
lean::inc(x_203);
x_205 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_203);
x_206 = lean::cnstr_get(x_205, 0);
x_208 = lean::cnstr_get(x_205, 1);
if (lean::is_exclusive(x_205)) {
 lean::cnstr_set(x_205, 0, lean::box(0));
 lean::cnstr_set(x_205, 1, lean::box(0));
 x_210 = x_205;
} else {
 lean::inc(x_206);
 lean::inc(x_208);
 lean::dec(x_205);
 x_210 = lean::box(0);
}
x_211 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_208);
x_212 = lean::cnstr_get(x_211, 0);
x_214 = lean::cnstr_get(x_211, 1);
if (lean::is_exclusive(x_211)) {
 lean::cnstr_set(x_211, 0, lean::box(0));
 lean::cnstr_set(x_211, 1, lean::box(0));
 x_216 = x_211;
} else {
 lean::inc(x_212);
 lean::inc(x_214);
 lean::dec(x_211);
 x_216 = lean::box(0);
}
if (lean::obj_tag(x_214) == 0)
{
obj* x_219; 
lean::inc(x_1);
lean::inc(x_0);
x_219 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_206, x_1, x_2);
if (lean::obj_tag(x_219) == 0)
{
obj* x_227; obj* x_229; obj* x_230; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_212);
lean::dec(x_210);
x_227 = lean::cnstr_get(x_219, 0);
if (lean::is_exclusive(x_219)) {
 lean::cnstr_set(x_219, 0, lean::box(0));
 x_229 = x_219;
} else {
 lean::inc(x_227);
 lean::dec(x_219);
 x_229 = lean::box(0);
}
if (lean::is_scalar(x_229)) {
 x_230 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_230 = x_229;
}
lean::cnstr_set(x_230, 0, x_227);
return x_230;
}
else
{
obj* x_231; obj* x_233; obj* x_234; obj* x_236; obj* x_239; obj* x_243; 
x_231 = lean::cnstr_get(x_219, 0);
if (lean::is_exclusive(x_219)) {
 lean::cnstr_set(x_219, 0, lean::box(0));
 x_233 = x_219;
} else {
 lean::inc(x_231);
 lean::dec(x_219);
 x_233 = lean::box(0);
}
x_234 = lean::cnstr_get(x_231, 0);
lean::inc(x_234);
x_236 = lean::cnstr_get(x_231, 1);
lean::inc(x_236);
lean::dec(x_231);
lean::inc(x_1);
lean::inc(x_0);
x_243 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_212, x_1, x_236);
if (lean::obj_tag(x_243) == 0)
{
obj* x_251; obj* x_254; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
lean::dec(x_234);
x_251 = lean::cnstr_get(x_243, 0);
lean::inc(x_251);
lean::dec(x_243);
if (lean::is_scalar(x_233)) {
 x_254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_254 = x_233;
 lean::cnstr_set_tag(x_233, 0);
}
lean::cnstr_set(x_254, 0, x_251);
return x_254;
}
else
{
obj* x_255; obj* x_258; obj* x_260; obj* x_263; 
x_255 = lean::cnstr_get(x_243, 0);
lean::inc(x_255);
lean::dec(x_243);
x_258 = lean::cnstr_get(x_255, 0);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_255, 1);
lean::inc(x_260);
lean::dec(x_255);
x_263 = lean::cnstr_get(x_202, 2);
lean::inc(x_263);
if (lean::obj_tag(x_263) == 0)
{
obj* x_266; 
lean::dec(x_233);
if (lean::is_scalar(x_216)) {
 x_266 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_266 = x_216;
}
lean::cnstr_set(x_266, 0, x_258);
lean::cnstr_set(x_266, 1, x_260);
x_239 = x_266;
goto lbl_240;
}
else
{
obj* x_267; obj* x_270; obj* x_274; 
x_267 = lean::cnstr_get(x_263, 0);
lean::inc(x_267);
lean::dec(x_263);
x_270 = lean::cnstr_get(x_267, 0);
lean::inc(x_270);
lean::dec(x_267);
lean::inc(x_1);
x_274 = l_lean_elaborator_to__pexpr___main(x_270, x_1, x_260);
if (lean::obj_tag(x_274) == 0)
{
obj* x_283; obj* x_286; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
lean::dec(x_234);
lean::dec(x_258);
x_283 = lean::cnstr_get(x_274, 0);
lean::inc(x_283);
lean::dec(x_274);
if (lean::is_scalar(x_233)) {
 x_286 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_286 = x_233;
 lean::cnstr_set_tag(x_233, 0);
}
lean::cnstr_set(x_286, 0, x_283);
return x_286;
}
else
{
obj* x_288; obj* x_291; obj* x_293; obj* x_296; obj* x_297; obj* x_298; obj* x_299; 
lean::dec(x_233);
x_288 = lean::cnstr_get(x_274, 0);
lean::inc(x_288);
lean::dec(x_274);
x_291 = lean::cnstr_get(x_288, 0);
lean::inc(x_291);
x_293 = lean::cnstr_get(x_288, 1);
lean::inc(x_293);
lean::dec(x_288);
x_296 = lean::box(0);
x_297 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_297, 0, x_291);
lean::cnstr_set(x_297, 1, x_296);
x_298 = l_list_append___rarg(x_258, x_297);
if (lean::is_scalar(x_216)) {
 x_299 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_299 = x_216;
}
lean::cnstr_set(x_299, 0, x_298);
lean::cnstr_set(x_299, 1, x_293);
x_239 = x_299;
goto lbl_240;
}
}
}
lbl_240:
{
obj* x_300; obj* x_302; obj* x_305; obj* x_306; obj* x_308; obj* x_309; obj* x_310; obj* x_311; uint8 x_312; obj* x_313; obj* x_314; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; 
x_300 = lean::cnstr_get(x_239, 0);
lean::inc(x_300);
x_302 = lean::cnstr_get(x_239, 1);
lean::inc(x_302);
lean::dec(x_239);
x_305 = lean::box(0);
x_306 = lean::mk_nat_obj(0u);
lean::inc(x_234);
x_308 = l_list_length__aux___main___rarg(x_234, x_306);
x_309 = l_lean_elaborator_to__pexpr___main___closed__25;
x_310 = l_lean_kvmap_set__nat(x_305, x_309, x_308);
x_311 = l_lean_elaborator_to__pexpr___main___closed__26;
x_312 = 0;
x_313 = l_lean_kvmap_set__bool(x_310, x_311, x_312);
x_314 = lean::cnstr_get(x_202, 1);
lean::inc(x_314);
lean::dec(x_202);
x_317 = l_lean_elaborator_to__pexpr___main___closed__27;
x_318 = l_option_map___rarg(x_317, x_314);
x_319 = l_lean_elaborator_to__pexpr___main___closed__28;
x_320 = l_option_map___rarg(x_319, x_318);
x_321 = l_option_get__or__else___main___rarg(x_320, x_305);
x_322 = l_lean_elaborator_to__pexpr___main___closed__29;
x_323 = l_lean_kvmap_set__name(x_313, x_322, x_321);
x_324 = l_list_append___rarg(x_234, x_300);
x_325 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(x_324);
x_326 = lean_expr_mk_mdata(x_323, x_325);
if (lean::is_scalar(x_210)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_210;
}
lean::cnstr_set(x_327, 0, x_326);
lean::cnstr_set(x_327, 1, x_302);
x_14 = x_327;
goto lbl_15;
}
}
}
else
{
obj* x_328; obj* x_330; obj* x_332; obj* x_333; 
x_328 = lean::cnstr_get(x_214, 0);
x_330 = lean::cnstr_get(x_214, 1);
if (lean::is_exclusive(x_214)) {
 lean::cnstr_set(x_214, 0, lean::box(0));
 lean::cnstr_set(x_214, 1, lean::box(0));
 x_332 = x_214;
} else {
 lean::inc(x_328);
 lean::inc(x_330);
 lean::dec(x_214);
 x_332 = lean::box(0);
}
x_333 = lean::cnstr_get(x_328, 0);
lean::inc(x_333);
lean::dec(x_328);
if (lean::obj_tag(x_333) == 0)
{
obj* x_337; obj* x_338; obj* x_341; obj* x_342; obj* x_344; 
lean::dec(x_330);
x_337 = l_lean_parser_term_struct__inst__item_has__view;
x_338 = lean::cnstr_get(x_337, 1);
lean::inc(x_338);
lean::dec(x_337);
x_341 = lean::apply_1(x_338, x_333);
x_342 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
x_344 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_341, x_342, x_1, x_2);
if (lean::obj_tag(x_344) == 0)
{
obj* x_354; obj* x_356; obj* x_357; 
lean::dec(x_332);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_212);
lean::dec(x_210);
lean::dec(x_206);
x_354 = lean::cnstr_get(x_344, 0);
if (lean::is_exclusive(x_344)) {
 lean::cnstr_set(x_344, 0, lean::box(0));
 x_356 = x_344;
} else {
 lean::inc(x_354);
 lean::dec(x_344);
 x_356 = lean::box(0);
}
if (lean::is_scalar(x_356)) {
 x_357 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_357 = x_356;
}
lean::cnstr_set(x_357, 0, x_354);
return x_357;
}
else
{
obj* x_358; obj* x_360; obj* x_361; obj* x_363; obj* x_368; 
x_358 = lean::cnstr_get(x_344, 0);
if (lean::is_exclusive(x_344)) {
 lean::cnstr_set(x_344, 0, lean::box(0));
 x_360 = x_344;
} else {
 lean::inc(x_358);
 lean::dec(x_344);
 x_360 = lean::box(0);
}
x_361 = lean::cnstr_get(x_358, 0);
lean::inc(x_361);
x_363 = lean::cnstr_get(x_358, 1);
lean::inc(x_363);
lean::dec(x_358);
lean::inc(x_1);
lean::inc(x_0);
x_368 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_206, x_1, x_363);
if (lean::obj_tag(x_368) == 0)
{
obj* x_378; obj* x_381; 
lean::dec(x_332);
lean::dec(x_361);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_212);
lean::dec(x_210);
x_378 = lean::cnstr_get(x_368, 0);
lean::inc(x_378);
lean::dec(x_368);
if (lean::is_scalar(x_360)) {
 x_381 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_381 = x_360;
 lean::cnstr_set_tag(x_360, 0);
}
lean::cnstr_set(x_381, 0, x_378);
return x_381;
}
else
{
obj* x_382; obj* x_385; obj* x_387; obj* x_390; obj* x_394; 
x_382 = lean::cnstr_get(x_368, 0);
lean::inc(x_382);
lean::dec(x_368);
x_385 = lean::cnstr_get(x_382, 0);
lean::inc(x_385);
x_387 = lean::cnstr_get(x_382, 1);
lean::inc(x_387);
lean::dec(x_382);
lean::inc(x_1);
lean::inc(x_0);
x_394 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_212, x_1, x_387);
if (lean::obj_tag(x_394) == 0)
{
obj* x_404; obj* x_407; 
lean::dec(x_332);
lean::dec(x_361);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_385);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
x_404 = lean::cnstr_get(x_394, 0);
lean::inc(x_404);
lean::dec(x_394);
if (lean::is_scalar(x_360)) {
 x_407 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_407 = x_360;
 lean::cnstr_set_tag(x_360, 0);
}
lean::cnstr_set(x_407, 0, x_404);
return x_407;
}
else
{
obj* x_408; obj* x_411; obj* x_413; obj* x_416; 
x_408 = lean::cnstr_get(x_394, 0);
lean::inc(x_408);
lean::dec(x_394);
x_411 = lean::cnstr_get(x_408, 0);
lean::inc(x_411);
x_413 = lean::cnstr_get(x_408, 1);
lean::inc(x_413);
lean::dec(x_408);
x_416 = lean::cnstr_get(x_202, 2);
lean::inc(x_416);
if (lean::obj_tag(x_416) == 0)
{
obj* x_420; 
lean::dec(x_332);
lean::dec(x_360);
if (lean::is_scalar(x_216)) {
 x_420 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_420 = x_216;
}
lean::cnstr_set(x_420, 0, x_411);
lean::cnstr_set(x_420, 1, x_413);
x_390 = x_420;
goto lbl_391;
}
else
{
obj* x_421; obj* x_424; obj* x_428; 
x_421 = lean::cnstr_get(x_416, 0);
lean::inc(x_421);
lean::dec(x_416);
x_424 = lean::cnstr_get(x_421, 0);
lean::inc(x_424);
lean::dec(x_421);
lean::inc(x_1);
x_428 = l_lean_elaborator_to__pexpr___main(x_424, x_1, x_413);
if (lean::obj_tag(x_428) == 0)
{
obj* x_439; obj* x_442; 
lean::dec(x_332);
lean::dec(x_361);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_385);
lean::dec(x_411);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
x_439 = lean::cnstr_get(x_428, 0);
lean::inc(x_439);
lean::dec(x_428);
if (lean::is_scalar(x_360)) {
 x_442 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_442 = x_360;
 lean::cnstr_set_tag(x_360, 0);
}
lean::cnstr_set(x_442, 0, x_439);
return x_442;
}
else
{
obj* x_444; obj* x_447; obj* x_449; obj* x_452; obj* x_453; obj* x_454; obj* x_455; 
lean::dec(x_360);
x_444 = lean::cnstr_get(x_428, 0);
lean::inc(x_444);
lean::dec(x_428);
x_447 = lean::cnstr_get(x_444, 0);
lean::inc(x_447);
x_449 = lean::cnstr_get(x_444, 1);
lean::inc(x_449);
lean::dec(x_444);
x_452 = lean::box(0);
if (lean::is_scalar(x_332)) {
 x_453 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_453 = x_332;
}
lean::cnstr_set(x_453, 0, x_447);
lean::cnstr_set(x_453, 1, x_452);
x_454 = l_list_append___rarg(x_411, x_453);
if (lean::is_scalar(x_216)) {
 x_455 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_455 = x_216;
}
lean::cnstr_set(x_455, 0, x_454);
lean::cnstr_set(x_455, 1, x_449);
x_390 = x_455;
goto lbl_391;
}
}
}
lbl_391:
{
obj* x_456; obj* x_458; obj* x_461; obj* x_462; obj* x_464; obj* x_465; obj* x_466; obj* x_467; uint8 x_468; obj* x_469; obj* x_470; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; 
x_456 = lean::cnstr_get(x_390, 0);
lean::inc(x_456);
x_458 = lean::cnstr_get(x_390, 1);
lean::inc(x_458);
lean::dec(x_390);
x_461 = lean::box(0);
x_462 = lean::mk_nat_obj(0u);
lean::inc(x_385);
x_464 = l_list_length__aux___main___rarg(x_385, x_462);
x_465 = l_lean_elaborator_to__pexpr___main___closed__25;
x_466 = l_lean_kvmap_set__nat(x_461, x_465, x_464);
x_467 = l_lean_elaborator_to__pexpr___main___closed__26;
x_468 = lean::unbox(x_361);
x_469 = l_lean_kvmap_set__bool(x_466, x_467, x_468);
x_470 = lean::cnstr_get(x_202, 1);
lean::inc(x_470);
lean::dec(x_202);
x_473 = l_lean_elaborator_to__pexpr___main___closed__27;
x_474 = l_option_map___rarg(x_473, x_470);
x_475 = l_lean_elaborator_to__pexpr___main___closed__28;
x_476 = l_option_map___rarg(x_475, x_474);
x_477 = l_option_get__or__else___main___rarg(x_476, x_461);
x_478 = l_lean_elaborator_to__pexpr___main___closed__29;
x_479 = l_lean_kvmap_set__name(x_469, x_478, x_477);
x_480 = l_list_append___rarg(x_385, x_456);
x_481 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_480);
x_482 = lean_expr_mk_mdata(x_479, x_481);
if (lean::is_scalar(x_210)) {
 x_483 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_483 = x_210;
}
lean::cnstr_set(x_483, 0, x_482);
lean::cnstr_set(x_483, 1, x_458);
x_14 = x_483;
goto lbl_15;
}
}
}
}
else
{
if (lean::obj_tag(x_330) == 0)
{
obj* x_487; 
lean::dec(x_333);
lean::inc(x_1);
lean::inc(x_0);
x_487 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_206, x_1, x_2);
if (lean::obj_tag(x_487) == 0)
{
obj* x_496; obj* x_498; obj* x_499; 
lean::dec(x_332);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_212);
lean::dec(x_210);
x_496 = lean::cnstr_get(x_487, 0);
if (lean::is_exclusive(x_487)) {
 lean::cnstr_set(x_487, 0, lean::box(0));
 x_498 = x_487;
} else {
 lean::inc(x_496);
 lean::dec(x_487);
 x_498 = lean::box(0);
}
if (lean::is_scalar(x_498)) {
 x_499 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_499 = x_498;
}
lean::cnstr_set(x_499, 0, x_496);
return x_499;
}
else
{
obj* x_500; obj* x_502; obj* x_503; obj* x_505; obj* x_508; obj* x_512; 
x_500 = lean::cnstr_get(x_487, 0);
if (lean::is_exclusive(x_487)) {
 lean::cnstr_set(x_487, 0, lean::box(0));
 x_502 = x_487;
} else {
 lean::inc(x_500);
 lean::dec(x_487);
 x_502 = lean::box(0);
}
x_503 = lean::cnstr_get(x_500, 0);
lean::inc(x_503);
x_505 = lean::cnstr_get(x_500, 1);
lean::inc(x_505);
lean::dec(x_500);
lean::inc(x_1);
lean::inc(x_0);
x_512 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_212, x_1, x_505);
if (lean::obj_tag(x_512) == 0)
{
obj* x_521; obj* x_524; 
lean::dec(x_332);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
lean::dec(x_503);
x_521 = lean::cnstr_get(x_512, 0);
lean::inc(x_521);
lean::dec(x_512);
if (lean::is_scalar(x_502)) {
 x_524 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_524 = x_502;
 lean::cnstr_set_tag(x_502, 0);
}
lean::cnstr_set(x_524, 0, x_521);
return x_524;
}
else
{
obj* x_525; obj* x_528; obj* x_530; obj* x_533; 
x_525 = lean::cnstr_get(x_512, 0);
lean::inc(x_525);
lean::dec(x_512);
x_528 = lean::cnstr_get(x_525, 0);
lean::inc(x_528);
x_530 = lean::cnstr_get(x_525, 1);
lean::inc(x_530);
lean::dec(x_525);
x_533 = lean::cnstr_get(x_202, 2);
lean::inc(x_533);
if (lean::obj_tag(x_533) == 0)
{
obj* x_537; 
lean::dec(x_332);
lean::dec(x_502);
if (lean::is_scalar(x_216)) {
 x_537 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_537 = x_216;
}
lean::cnstr_set(x_537, 0, x_528);
lean::cnstr_set(x_537, 1, x_530);
x_508 = x_537;
goto lbl_509;
}
else
{
obj* x_538; obj* x_541; obj* x_545; 
x_538 = lean::cnstr_get(x_533, 0);
lean::inc(x_538);
lean::dec(x_533);
x_541 = lean::cnstr_get(x_538, 0);
lean::inc(x_541);
lean::dec(x_538);
lean::inc(x_1);
x_545 = l_lean_elaborator_to__pexpr___main(x_541, x_1, x_530);
if (lean::obj_tag(x_545) == 0)
{
obj* x_555; obj* x_558; 
lean::dec(x_332);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
lean::dec(x_503);
lean::dec(x_528);
x_555 = lean::cnstr_get(x_545, 0);
lean::inc(x_555);
lean::dec(x_545);
if (lean::is_scalar(x_502)) {
 x_558 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_558 = x_502;
 lean::cnstr_set_tag(x_502, 0);
}
lean::cnstr_set(x_558, 0, x_555);
return x_558;
}
else
{
obj* x_560; obj* x_563; obj* x_565; obj* x_568; obj* x_569; obj* x_570; obj* x_571; 
lean::dec(x_502);
x_560 = lean::cnstr_get(x_545, 0);
lean::inc(x_560);
lean::dec(x_545);
x_563 = lean::cnstr_get(x_560, 0);
lean::inc(x_563);
x_565 = lean::cnstr_get(x_560, 1);
lean::inc(x_565);
lean::dec(x_560);
x_568 = lean::box(0);
if (lean::is_scalar(x_332)) {
 x_569 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_569 = x_332;
}
lean::cnstr_set(x_569, 0, x_563);
lean::cnstr_set(x_569, 1, x_568);
x_570 = l_list_append___rarg(x_528, x_569);
if (lean::is_scalar(x_216)) {
 x_571 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_571 = x_216;
}
lean::cnstr_set(x_571, 0, x_570);
lean::cnstr_set(x_571, 1, x_565);
x_508 = x_571;
goto lbl_509;
}
}
}
lbl_509:
{
obj* x_572; obj* x_574; obj* x_577; obj* x_578; obj* x_580; obj* x_581; obj* x_582; obj* x_583; uint8 x_584; obj* x_585; obj* x_586; obj* x_589; obj* x_590; obj* x_591; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; 
x_572 = lean::cnstr_get(x_508, 0);
lean::inc(x_572);
x_574 = lean::cnstr_get(x_508, 1);
lean::inc(x_574);
lean::dec(x_508);
x_577 = lean::box(0);
x_578 = lean::mk_nat_obj(0u);
lean::inc(x_503);
x_580 = l_list_length__aux___main___rarg(x_503, x_578);
x_581 = l_lean_elaborator_to__pexpr___main___closed__25;
x_582 = l_lean_kvmap_set__nat(x_577, x_581, x_580);
x_583 = l_lean_elaborator_to__pexpr___main___closed__26;
x_584 = 1;
x_585 = l_lean_kvmap_set__bool(x_582, x_583, x_584);
x_586 = lean::cnstr_get(x_202, 1);
lean::inc(x_586);
lean::dec(x_202);
x_589 = l_lean_elaborator_to__pexpr___main___closed__27;
x_590 = l_option_map___rarg(x_589, x_586);
x_591 = l_lean_elaborator_to__pexpr___main___closed__28;
x_592 = l_option_map___rarg(x_591, x_590);
x_593 = l_option_get__or__else___main___rarg(x_592, x_577);
x_594 = l_lean_elaborator_to__pexpr___main___closed__29;
x_595 = l_lean_kvmap_set__name(x_585, x_594, x_593);
x_596 = l_list_append___rarg(x_503, x_572);
x_597 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_596);
x_598 = lean_expr_mk_mdata(x_595, x_597);
if (lean::is_scalar(x_210)) {
 x_599 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_599 = x_210;
}
lean::cnstr_set(x_599, 0, x_598);
lean::cnstr_set(x_599, 1, x_574);
x_14 = x_599;
goto lbl_15;
}
}
}
else
{
obj* x_601; obj* x_602; obj* x_605; obj* x_606; obj* x_608; 
lean::dec(x_330);
x_601 = l_lean_parser_term_struct__inst__item_has__view;
x_602 = lean::cnstr_get(x_601, 1);
lean::inc(x_602);
lean::dec(x_601);
x_605 = lean::apply_1(x_602, x_333);
x_606 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
x_608 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_605, x_606, x_1, x_2);
if (lean::obj_tag(x_608) == 0)
{
obj* x_618; obj* x_620; obj* x_621; 
lean::dec(x_332);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_212);
lean::dec(x_210);
lean::dec(x_206);
x_618 = lean::cnstr_get(x_608, 0);
if (lean::is_exclusive(x_608)) {
 lean::cnstr_set(x_608, 0, lean::box(0));
 x_620 = x_608;
} else {
 lean::inc(x_618);
 lean::dec(x_608);
 x_620 = lean::box(0);
}
if (lean::is_scalar(x_620)) {
 x_621 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_621 = x_620;
}
lean::cnstr_set(x_621, 0, x_618);
return x_621;
}
else
{
obj* x_622; obj* x_624; obj* x_625; obj* x_627; obj* x_632; 
x_622 = lean::cnstr_get(x_608, 0);
if (lean::is_exclusive(x_608)) {
 lean::cnstr_set(x_608, 0, lean::box(0));
 x_624 = x_608;
} else {
 lean::inc(x_622);
 lean::dec(x_608);
 x_624 = lean::box(0);
}
x_625 = lean::cnstr_get(x_622, 0);
lean::inc(x_625);
x_627 = lean::cnstr_get(x_622, 1);
lean::inc(x_627);
lean::dec(x_622);
lean::inc(x_1);
lean::inc(x_0);
x_632 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_206, x_1, x_627);
if (lean::obj_tag(x_632) == 0)
{
obj* x_642; obj* x_645; 
lean::dec(x_332);
lean::dec(x_625);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_212);
lean::dec(x_210);
x_642 = lean::cnstr_get(x_632, 0);
lean::inc(x_642);
lean::dec(x_632);
if (lean::is_scalar(x_624)) {
 x_645 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_645 = x_624;
 lean::cnstr_set_tag(x_624, 0);
}
lean::cnstr_set(x_645, 0, x_642);
return x_645;
}
else
{
obj* x_646; obj* x_649; obj* x_651; obj* x_654; obj* x_658; 
x_646 = lean::cnstr_get(x_632, 0);
lean::inc(x_646);
lean::dec(x_632);
x_649 = lean::cnstr_get(x_646, 0);
lean::inc(x_649);
x_651 = lean::cnstr_get(x_646, 1);
lean::inc(x_651);
lean::dec(x_646);
lean::inc(x_1);
lean::inc(x_0);
x_658 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_212, x_1, x_651);
if (lean::obj_tag(x_658) == 0)
{
obj* x_668; obj* x_671; 
lean::dec(x_332);
lean::dec(x_625);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_649);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
x_668 = lean::cnstr_get(x_658, 0);
lean::inc(x_668);
lean::dec(x_658);
if (lean::is_scalar(x_624)) {
 x_671 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_671 = x_624;
 lean::cnstr_set_tag(x_624, 0);
}
lean::cnstr_set(x_671, 0, x_668);
return x_671;
}
else
{
obj* x_672; obj* x_675; obj* x_677; obj* x_680; 
x_672 = lean::cnstr_get(x_658, 0);
lean::inc(x_672);
lean::dec(x_658);
x_675 = lean::cnstr_get(x_672, 0);
lean::inc(x_675);
x_677 = lean::cnstr_get(x_672, 1);
lean::inc(x_677);
lean::dec(x_672);
x_680 = lean::cnstr_get(x_202, 2);
lean::inc(x_680);
if (lean::obj_tag(x_680) == 0)
{
obj* x_684; 
lean::dec(x_332);
lean::dec(x_624);
if (lean::is_scalar(x_216)) {
 x_684 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_684 = x_216;
}
lean::cnstr_set(x_684, 0, x_675);
lean::cnstr_set(x_684, 1, x_677);
x_654 = x_684;
goto lbl_655;
}
else
{
obj* x_685; obj* x_688; obj* x_692; 
x_685 = lean::cnstr_get(x_680, 0);
lean::inc(x_685);
lean::dec(x_680);
x_688 = lean::cnstr_get(x_685, 0);
lean::inc(x_688);
lean::dec(x_685);
lean::inc(x_1);
x_692 = l_lean_elaborator_to__pexpr___main(x_688, x_1, x_677);
if (lean::obj_tag(x_692) == 0)
{
obj* x_703; obj* x_706; 
lean::dec(x_332);
lean::dec(x_625);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_649);
lean::dec(x_675);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
x_703 = lean::cnstr_get(x_692, 0);
lean::inc(x_703);
lean::dec(x_692);
if (lean::is_scalar(x_624)) {
 x_706 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_706 = x_624;
 lean::cnstr_set_tag(x_624, 0);
}
lean::cnstr_set(x_706, 0, x_703);
return x_706;
}
else
{
obj* x_708; obj* x_711; obj* x_713; obj* x_716; obj* x_717; obj* x_718; obj* x_719; 
lean::dec(x_624);
x_708 = lean::cnstr_get(x_692, 0);
lean::inc(x_708);
lean::dec(x_692);
x_711 = lean::cnstr_get(x_708, 0);
lean::inc(x_711);
x_713 = lean::cnstr_get(x_708, 1);
lean::inc(x_713);
lean::dec(x_708);
x_716 = lean::box(0);
if (lean::is_scalar(x_332)) {
 x_717 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_717 = x_332;
}
lean::cnstr_set(x_717, 0, x_711);
lean::cnstr_set(x_717, 1, x_716);
x_718 = l_list_append___rarg(x_675, x_717);
if (lean::is_scalar(x_216)) {
 x_719 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_719 = x_216;
}
lean::cnstr_set(x_719, 0, x_718);
lean::cnstr_set(x_719, 1, x_713);
x_654 = x_719;
goto lbl_655;
}
}
}
lbl_655:
{
obj* x_720; obj* x_722; obj* x_725; obj* x_726; obj* x_728; obj* x_729; obj* x_730; obj* x_731; uint8 x_732; obj* x_733; obj* x_734; obj* x_737; obj* x_738; obj* x_739; obj* x_740; obj* x_741; obj* x_742; obj* x_743; obj* x_744; obj* x_745; obj* x_746; obj* x_747; 
x_720 = lean::cnstr_get(x_654, 0);
lean::inc(x_720);
x_722 = lean::cnstr_get(x_654, 1);
lean::inc(x_722);
lean::dec(x_654);
x_725 = lean::box(0);
x_726 = lean::mk_nat_obj(0u);
lean::inc(x_649);
x_728 = l_list_length__aux___main___rarg(x_649, x_726);
x_729 = l_lean_elaborator_to__pexpr___main___closed__25;
x_730 = l_lean_kvmap_set__nat(x_725, x_729, x_728);
x_731 = l_lean_elaborator_to__pexpr___main___closed__26;
x_732 = lean::unbox(x_625);
x_733 = l_lean_kvmap_set__bool(x_730, x_731, x_732);
x_734 = lean::cnstr_get(x_202, 1);
lean::inc(x_734);
lean::dec(x_202);
x_737 = l_lean_elaborator_to__pexpr___main___closed__27;
x_738 = l_option_map___rarg(x_737, x_734);
x_739 = l_lean_elaborator_to__pexpr___main___closed__28;
x_740 = l_option_map___rarg(x_739, x_738);
x_741 = l_option_get__or__else___main___rarg(x_740, x_725);
x_742 = l_lean_elaborator_to__pexpr___main___closed__29;
x_743 = l_lean_kvmap_set__name(x_733, x_742, x_741);
x_744 = l_list_append___rarg(x_649, x_720);
x_745 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_744);
x_746 = lean_expr_mk_mdata(x_743, x_745);
if (lean::is_scalar(x_210)) {
 x_747 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_747 = x_210;
}
lean::cnstr_set(x_747, 0, x_746);
lean::cnstr_set(x_747, 1, x_722);
x_14 = x_747;
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
obj* x_750; 
lean::inc(x_1);
lean::inc(x_9);
x_750 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_9, x_1, x_2);
if (lean::obj_tag(x_750) == 0)
{
obj* x_755; obj* x_757; obj* x_758; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_755 = lean::cnstr_get(x_750, 0);
if (lean::is_exclusive(x_750)) {
 lean::cnstr_set(x_750, 0, lean::box(0));
 x_757 = x_750;
} else {
 lean::inc(x_755);
 lean::dec(x_750);
 x_757 = lean::box(0);
}
if (lean::is_scalar(x_757)) {
 x_758 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_758 = x_757;
}
lean::cnstr_set(x_758, 0, x_755);
return x_758;
}
else
{
obj* x_759; obj* x_762; obj* x_764; obj* x_766; obj* x_767; obj* x_768; 
x_759 = lean::cnstr_get(x_750, 0);
lean::inc(x_759);
lean::dec(x_750);
x_762 = lean::cnstr_get(x_759, 0);
x_764 = lean::cnstr_get(x_759, 1);
if (lean::is_exclusive(x_759)) {
 lean::cnstr_set(x_759, 0, lean::box(0));
 lean::cnstr_set(x_759, 1, lean::box(0));
 x_766 = x_759;
} else {
 lean::inc(x_762);
 lean::inc(x_764);
 lean::dec(x_759);
 x_766 = lean::box(0);
}
x_767 = l_list_reverse___rarg(x_762);
if (lean::is_scalar(x_766)) {
 x_768 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_768 = x_766;
}
lean::cnstr_set(x_768, 0, x_767);
lean::cnstr_set(x_768, 1, x_764);
x_16 = x_768;
goto lbl_17;
}
}
}
else
{
obj* x_771; obj* x_772; obj* x_776; obj* x_777; obj* x_778; obj* x_779; obj* x_780; obj* x_781; 
lean::dec(x_9);
lean::dec(x_7);
x_771 = l_lean_parser_string__lit_has__view;
x_772 = lean::cnstr_get(x_771, 0);
lean::inc(x_772);
lean::dec(x_771);
lean::inc(x_0);
x_776 = lean::apply_1(x_772, x_0);
x_777 = l_lean_parser_string__lit_view_value(x_776);
x_778 = l_lean_elaborator_to__pexpr___main___closed__31;
x_779 = l_option_get__or__else___main___rarg(x_777, x_778);
x_780 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_780, 0, x_779);
x_781 = lean_expr_mk_lit(x_780);
if (x_21 == 0)
{
obj* x_782; 
x_782 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_782) == 0)
{
obj* x_784; obj* x_785; 
lean::dec(x_1);
x_784 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_784, 0, x_781);
lean::cnstr_set(x_784, 1, x_2);
x_785 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_785, 0, x_784);
return x_785;
}
else
{
obj* x_786; obj* x_789; obj* x_792; obj* x_795; obj* x_796; obj* x_797; obj* x_799; obj* x_800; obj* x_801; obj* x_804; obj* x_805; obj* x_806; obj* x_807; obj* x_808; 
x_786 = lean::cnstr_get(x_782, 0);
lean::inc(x_786);
lean::dec(x_782);
x_789 = lean::cnstr_get(x_1, 0);
lean::inc(x_789);
lean::dec(x_1);
x_792 = lean::cnstr_get(x_789, 2);
lean::inc(x_792);
lean::dec(x_789);
x_795 = l_lean_file__map_to__position(x_792, x_786);
x_796 = lean::box(0);
x_797 = lean::cnstr_get(x_795, 1);
lean::inc(x_797);
x_799 = l_lean_elaborator_to__pexpr___main___closed__3;
x_800 = l_lean_kvmap_set__nat(x_796, x_799, x_797);
x_801 = lean::cnstr_get(x_795, 0);
lean::inc(x_801);
lean::dec(x_795);
x_804 = l_lean_elaborator_to__pexpr___main___closed__4;
x_805 = l_lean_kvmap_set__nat(x_800, x_804, x_801);
x_806 = lean_expr_mk_mdata(x_805, x_781);
x_807 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_807, 0, x_806);
lean::cnstr_set(x_807, 1, x_2);
x_808 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_808, 0, x_807);
return x_808;
}
}
else
{
obj* x_811; obj* x_812; 
lean::dec(x_1);
lean::dec(x_0);
x_811 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_811, 0, x_781);
lean::cnstr_set(x_811, 1, x_2);
x_812 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_812, 0, x_811);
return x_812;
}
}
}
else
{
obj* x_815; obj* x_816; obj* x_820; obj* x_821; obj* x_822; obj* x_823; 
lean::dec(x_9);
lean::dec(x_7);
x_815 = l_lean_parser_number_has__view;
x_816 = lean::cnstr_get(x_815, 0);
lean::inc(x_816);
lean::dec(x_815);
lean::inc(x_0);
x_820 = lean::apply_1(x_816, x_0);
x_821 = l_lean_parser_number_view_to__nat___main(x_820);
x_822 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_822, 0, x_821);
x_823 = lean_expr_mk_lit(x_822);
if (x_21 == 0)
{
obj* x_824; 
x_824 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_824) == 0)
{
obj* x_826; obj* x_827; 
lean::dec(x_1);
x_826 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_826, 0, x_823);
lean::cnstr_set(x_826, 1, x_2);
x_827 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_827, 0, x_826);
return x_827;
}
else
{
obj* x_828; obj* x_831; obj* x_834; obj* x_837; obj* x_838; obj* x_839; obj* x_841; obj* x_842; obj* x_843; obj* x_846; obj* x_847; obj* x_848; obj* x_849; obj* x_850; 
x_828 = lean::cnstr_get(x_824, 0);
lean::inc(x_828);
lean::dec(x_824);
x_831 = lean::cnstr_get(x_1, 0);
lean::inc(x_831);
lean::dec(x_1);
x_834 = lean::cnstr_get(x_831, 2);
lean::inc(x_834);
lean::dec(x_831);
x_837 = l_lean_file__map_to__position(x_834, x_828);
x_838 = lean::box(0);
x_839 = lean::cnstr_get(x_837, 1);
lean::inc(x_839);
x_841 = l_lean_elaborator_to__pexpr___main___closed__3;
x_842 = l_lean_kvmap_set__nat(x_838, x_841, x_839);
x_843 = lean::cnstr_get(x_837, 0);
lean::inc(x_843);
lean::dec(x_837);
x_846 = l_lean_elaborator_to__pexpr___main___closed__4;
x_847 = l_lean_kvmap_set__nat(x_842, x_846, x_843);
x_848 = lean_expr_mk_mdata(x_847, x_823);
x_849 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_849, 0, x_848);
lean::cnstr_set(x_849, 1, x_2);
x_850 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_850, 0, x_849);
return x_850;
}
}
else
{
obj* x_853; obj* x_854; 
lean::dec(x_1);
lean::dec(x_0);
x_853 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_853, 0, x_823);
lean::cnstr_set(x_853, 1, x_2);
x_854 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_854, 0, x_853);
return x_854;
}
}
}
else
{
obj* x_856; obj* x_857; obj* x_861; obj* x_862; obj* x_866; 
lean::dec(x_9);
x_856 = l_lean_parser_term_borrowed_has__view;
x_857 = lean::cnstr_get(x_856, 0);
lean::inc(x_857);
lean::dec(x_856);
lean::inc(x_0);
x_861 = lean::apply_1(x_857, x_0);
x_862 = lean::cnstr_get(x_861, 1);
lean::inc(x_862);
lean::dec(x_861);
lean::inc(x_1);
x_866 = l_lean_elaborator_to__pexpr___main(x_862, x_1, x_2);
if (lean::obj_tag(x_866) == 0)
{
obj* x_870; obj* x_872; obj* x_873; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_870 = lean::cnstr_get(x_866, 0);
if (lean::is_exclusive(x_866)) {
 lean::cnstr_set(x_866, 0, lean::box(0));
 x_872 = x_866;
} else {
 lean::inc(x_870);
 lean::dec(x_866);
 x_872 = lean::box(0);
}
if (lean::is_scalar(x_872)) {
 x_873 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_873 = x_872;
}
lean::cnstr_set(x_873, 0, x_870);
return x_873;
}
else
{
obj* x_874; obj* x_877; obj* x_879; obj* x_881; obj* x_882; obj* x_883; obj* x_884; 
x_874 = lean::cnstr_get(x_866, 0);
lean::inc(x_874);
lean::dec(x_866);
x_877 = lean::cnstr_get(x_874, 0);
x_879 = lean::cnstr_get(x_874, 1);
if (lean::is_exclusive(x_874)) {
 lean::cnstr_set(x_874, 0, lean::box(0));
 lean::cnstr_set(x_874, 1, lean::box(0));
 x_881 = x_874;
} else {
 lean::inc(x_877);
 lean::inc(x_879);
 lean::dec(x_874);
 x_881 = lean::box(0);
}
x_882 = l_lean_elaborator_to__pexpr___main___closed__32;
x_883 = l_lean_elaborator_expr_mk__annotation(x_882, x_877);
if (lean::is_scalar(x_881)) {
 x_884 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_884 = x_881;
}
lean::cnstr_set(x_884, 0, x_883);
lean::cnstr_set(x_884, 1, x_879);
x_14 = x_884;
goto lbl_15;
}
}
}
else
{
obj* x_886; obj* x_887; obj* x_891; obj* x_892; obj* x_896; 
lean::dec(x_9);
x_886 = l_lean_parser_term_inaccessible_has__view;
x_887 = lean::cnstr_get(x_886, 0);
lean::inc(x_887);
lean::dec(x_886);
lean::inc(x_0);
x_891 = lean::apply_1(x_887, x_0);
x_892 = lean::cnstr_get(x_891, 1);
lean::inc(x_892);
lean::dec(x_891);
lean::inc(x_1);
x_896 = l_lean_elaborator_to__pexpr___main(x_892, x_1, x_2);
if (lean::obj_tag(x_896) == 0)
{
obj* x_900; obj* x_902; obj* x_903; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_900 = lean::cnstr_get(x_896, 0);
if (lean::is_exclusive(x_896)) {
 lean::cnstr_set(x_896, 0, lean::box(0));
 x_902 = x_896;
} else {
 lean::inc(x_900);
 lean::dec(x_896);
 x_902 = lean::box(0);
}
if (lean::is_scalar(x_902)) {
 x_903 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_903 = x_902;
}
lean::cnstr_set(x_903, 0, x_900);
return x_903;
}
else
{
obj* x_904; obj* x_907; obj* x_909; obj* x_911; obj* x_912; obj* x_913; obj* x_914; 
x_904 = lean::cnstr_get(x_896, 0);
lean::inc(x_904);
lean::dec(x_896);
x_907 = lean::cnstr_get(x_904, 0);
x_909 = lean::cnstr_get(x_904, 1);
if (lean::is_exclusive(x_904)) {
 lean::cnstr_set(x_904, 0, lean::box(0));
 lean::cnstr_set(x_904, 1, lean::box(0));
 x_911 = x_904;
} else {
 lean::inc(x_907);
 lean::inc(x_909);
 lean::dec(x_904);
 x_911 = lean::box(0);
}
x_912 = l_lean_elaborator_to__pexpr___main___closed__33;
x_913 = l_lean_elaborator_expr_mk__annotation(x_912, x_907);
if (lean::is_scalar(x_911)) {
 x_914 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_914 = x_911;
}
lean::cnstr_set(x_914, 0, x_913);
lean::cnstr_set(x_914, 1, x_909);
x_14 = x_914;
goto lbl_15;
}
}
}
else
{
obj* x_916; obj* x_917; obj* x_921; obj* x_922; obj* x_924; obj* x_925; obj* x_928; obj* x_931; 
lean::dec(x_9);
x_916 = l_lean_parser_term_explicit_has__view;
x_917 = lean::cnstr_get(x_916, 0);
lean::inc(x_917);
lean::dec(x_916);
lean::inc(x_0);
x_921 = lean::apply_1(x_917, x_0);
x_922 = lean::cnstr_get(x_921, 0);
lean::inc(x_922);
x_924 = l_lean_parser_ident__univs_has__view;
x_925 = lean::cnstr_get(x_924, 1);
lean::inc(x_925);
lean::dec(x_924);
x_928 = lean::cnstr_get(x_921, 1);
lean::inc(x_928);
lean::dec(x_921);
x_931 = lean::apply_1(x_925, x_928);
if (lean::obj_tag(x_922) == 0)
{
obj* x_934; 
lean::dec(x_922);
lean::inc(x_1);
x_934 = l_lean_elaborator_to__pexpr___main(x_931, x_1, x_2);
if (lean::obj_tag(x_934) == 0)
{
obj* x_938; obj* x_940; obj* x_941; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_938 = lean::cnstr_get(x_934, 0);
if (lean::is_exclusive(x_934)) {
 lean::cnstr_set(x_934, 0, lean::box(0));
 x_940 = x_934;
} else {
 lean::inc(x_938);
 lean::dec(x_934);
 x_940 = lean::box(0);
}
if (lean::is_scalar(x_940)) {
 x_941 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_941 = x_940;
}
lean::cnstr_set(x_941, 0, x_938);
return x_941;
}
else
{
obj* x_942; obj* x_945; obj* x_947; obj* x_949; obj* x_950; obj* x_951; obj* x_952; 
x_942 = lean::cnstr_get(x_934, 0);
lean::inc(x_942);
lean::dec(x_934);
x_945 = lean::cnstr_get(x_942, 0);
x_947 = lean::cnstr_get(x_942, 1);
if (lean::is_exclusive(x_942)) {
 lean::cnstr_set(x_942, 0, lean::box(0));
 lean::cnstr_set(x_942, 1, lean::box(0));
 x_949 = x_942;
} else {
 lean::inc(x_945);
 lean::inc(x_947);
 lean::dec(x_942);
 x_949 = lean::box(0);
}
x_950 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
x_951 = l_lean_elaborator_expr_mk__annotation(x_950, x_945);
if (lean::is_scalar(x_949)) {
 x_952 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_952 = x_949;
}
lean::cnstr_set(x_952, 0, x_951);
lean::cnstr_set(x_952, 1, x_947);
x_14 = x_952;
goto lbl_15;
}
}
else
{
obj* x_955; 
lean::dec(x_922);
lean::inc(x_1);
x_955 = l_lean_elaborator_to__pexpr___main(x_931, x_1, x_2);
if (lean::obj_tag(x_955) == 0)
{
obj* x_959; obj* x_961; obj* x_962; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_959 = lean::cnstr_get(x_955, 0);
if (lean::is_exclusive(x_955)) {
 lean::cnstr_set(x_955, 0, lean::box(0));
 x_961 = x_955;
} else {
 lean::inc(x_959);
 lean::dec(x_955);
 x_961 = lean::box(0);
}
if (lean::is_scalar(x_961)) {
 x_962 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_962 = x_961;
}
lean::cnstr_set(x_962, 0, x_959);
return x_962;
}
else
{
obj* x_963; obj* x_966; obj* x_968; obj* x_970; obj* x_971; obj* x_972; obj* x_973; 
x_963 = lean::cnstr_get(x_955, 0);
lean::inc(x_963);
lean::dec(x_955);
x_966 = lean::cnstr_get(x_963, 0);
x_968 = lean::cnstr_get(x_963, 1);
if (lean::is_exclusive(x_963)) {
 lean::cnstr_set(x_963, 0, lean::box(0));
 lean::cnstr_set(x_963, 1, lean::box(0));
 x_970 = x_963;
} else {
 lean::inc(x_966);
 lean::inc(x_968);
 lean::dec(x_963);
 x_970 = lean::box(0);
}
x_971 = l_lean_elaborator_to__pexpr___main___closed__34;
x_972 = l_lean_elaborator_expr_mk__annotation(x_971, x_966);
if (lean::is_scalar(x_970)) {
 x_973 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_973 = x_970;
}
lean::cnstr_set(x_973, 0, x_972);
lean::cnstr_set(x_973, 1, x_968);
x_14 = x_973;
goto lbl_15;
}
}
}
}
else
{
obj* x_975; obj* x_976; obj* x_980; obj* x_981; obj* x_983; 
lean::dec(x_9);
x_975 = l_lean_parser_term_projection_has__view;
x_976 = lean::cnstr_get(x_975, 0);
lean::inc(x_976);
lean::dec(x_975);
lean::inc(x_0);
x_980 = lean::apply_1(x_976, x_0);
x_981 = lean::cnstr_get(x_980, 2);
lean::inc(x_981);
x_983 = lean::cnstr_get(x_980, 0);
lean::inc(x_983);
lean::dec(x_980);
if (lean::obj_tag(x_981) == 0)
{
obj* x_986; obj* x_990; 
x_986 = lean::cnstr_get(x_981, 0);
lean::inc(x_986);
lean::dec(x_981);
lean::inc(x_1);
x_990 = l_lean_elaborator_to__pexpr___main(x_983, x_1, x_2);
if (lean::obj_tag(x_990) == 0)
{
obj* x_995; obj* x_997; obj* x_998; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_986);
x_995 = lean::cnstr_get(x_990, 0);
if (lean::is_exclusive(x_990)) {
 lean::cnstr_set(x_990, 0, lean::box(0));
 x_997 = x_990;
} else {
 lean::inc(x_995);
 lean::dec(x_990);
 x_997 = lean::box(0);
}
if (lean::is_scalar(x_997)) {
 x_998 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_998 = x_997;
}
lean::cnstr_set(x_998, 0, x_995);
return x_998;
}
else
{
obj* x_999; obj* x_1002; obj* x_1004; obj* x_1006; obj* x_1007; obj* x_1010; obj* x_1011; obj* x_1012; obj* x_1013; obj* x_1014; obj* x_1015; 
x_999 = lean::cnstr_get(x_990, 0);
lean::inc(x_999);
lean::dec(x_990);
x_1002 = lean::cnstr_get(x_999, 0);
x_1004 = lean::cnstr_get(x_999, 1);
if (lean::is_exclusive(x_999)) {
 lean::cnstr_set(x_999, 0, lean::box(0));
 lean::cnstr_set(x_999, 1, lean::box(0));
 x_1006 = x_999;
} else {
 lean::inc(x_1002);
 lean::inc(x_1004);
 lean::dec(x_999);
 x_1006 = lean::box(0);
}
x_1007 = lean::cnstr_get(x_986, 2);
lean::inc(x_1007);
lean::dec(x_986);
x_1010 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1010, 0, x_1007);
x_1011 = lean::box(0);
x_1012 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1013 = l_lean_kvmap_insert__core___main(x_1011, x_1012, x_1010);
x_1014 = lean_expr_mk_mdata(x_1013, x_1002);
if (lean::is_scalar(x_1006)) {
 x_1015 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1015 = x_1006;
}
lean::cnstr_set(x_1015, 0, x_1014);
lean::cnstr_set(x_1015, 1, x_1004);
x_14 = x_1015;
goto lbl_15;
}
}
else
{
obj* x_1016; obj* x_1020; 
x_1016 = lean::cnstr_get(x_981, 0);
lean::inc(x_1016);
lean::dec(x_981);
lean::inc(x_1);
x_1020 = l_lean_elaborator_to__pexpr___main(x_983, x_1, x_2);
if (lean::obj_tag(x_1020) == 0)
{
obj* x_1025; obj* x_1027; obj* x_1028; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1016);
x_1025 = lean::cnstr_get(x_1020, 0);
if (lean::is_exclusive(x_1020)) {
 lean::cnstr_set(x_1020, 0, lean::box(0));
 x_1027 = x_1020;
} else {
 lean::inc(x_1025);
 lean::dec(x_1020);
 x_1027 = lean::box(0);
}
if (lean::is_scalar(x_1027)) {
 x_1028 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1028 = x_1027;
}
lean::cnstr_set(x_1028, 0, x_1025);
return x_1028;
}
else
{
obj* x_1029; obj* x_1032; obj* x_1034; obj* x_1036; obj* x_1037; obj* x_1038; obj* x_1039; obj* x_1040; obj* x_1041; obj* x_1042; obj* x_1043; 
x_1029 = lean::cnstr_get(x_1020, 0);
lean::inc(x_1029);
lean::dec(x_1020);
x_1032 = lean::cnstr_get(x_1029, 0);
x_1034 = lean::cnstr_get(x_1029, 1);
if (lean::is_exclusive(x_1029)) {
 lean::cnstr_set(x_1029, 0, lean::box(0));
 lean::cnstr_set(x_1029, 1, lean::box(0));
 x_1036 = x_1029;
} else {
 lean::inc(x_1032);
 lean::inc(x_1034);
 lean::dec(x_1029);
 x_1036 = lean::box(0);
}
x_1037 = l_lean_parser_number_view_to__nat___main(x_1016);
x_1038 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1038, 0, x_1037);
x_1039 = lean::box(0);
x_1040 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1041 = l_lean_kvmap_insert__core___main(x_1039, x_1040, x_1038);
x_1042 = lean_expr_mk_mdata(x_1041, x_1032);
if (lean::is_scalar(x_1036)) {
 x_1043 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1043 = x_1036;
}
lean::cnstr_set(x_1043, 0, x_1042);
lean::cnstr_set(x_1043, 1, x_1034);
x_14 = x_1043;
goto lbl_15;
}
}
}
}
else
{
obj* x_1045; obj* x_1046; obj* x_1050; obj* x_1051; 
lean::dec(x_9);
x_1045 = l_lean_parser_term_let_has__view;
x_1046 = lean::cnstr_get(x_1045, 0);
lean::inc(x_1046);
lean::dec(x_1045);
lean::inc(x_0);
x_1050 = lean::apply_1(x_1046, x_0);
x_1051 = lean::cnstr_get(x_1050, 1);
lean::inc(x_1051);
if (lean::obj_tag(x_1051) == 0)
{
obj* x_1053; obj* x_1056; obj* x_1058; obj* x_1060; 
x_1053 = lean::cnstr_get(x_1051, 0);
lean::inc(x_1053);
lean::dec(x_1051);
x_1056 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1056);
x_1058 = lean::cnstr_get(x_1053, 1);
lean::inc(x_1058);
x_1060 = lean::cnstr_get(x_1053, 2);
lean::inc(x_1060);
lean::dec(x_1053);
if (lean::obj_tag(x_1058) == 0)
{
if (lean::obj_tag(x_1060) == 0)
{
obj* x_1065; obj* x_1068; 
lean::dec(x_1050);
lean::dec(x_1056);
x_1065 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_0);
x_1068 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1065, x_1, x_2);
if (lean::obj_tag(x_1068) == 0)
{
obj* x_1072; obj* x_1074; obj* x_1075; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1072 = lean::cnstr_get(x_1068, 0);
if (lean::is_exclusive(x_1068)) {
 lean::cnstr_set(x_1068, 0, lean::box(0));
 x_1074 = x_1068;
} else {
 lean::inc(x_1072);
 lean::dec(x_1068);
 x_1074 = lean::box(0);
}
if (lean::is_scalar(x_1074)) {
 x_1075 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1075 = x_1074;
}
lean::cnstr_set(x_1075, 0, x_1072);
return x_1075;
}
else
{
obj* x_1076; 
x_1076 = lean::cnstr_get(x_1068, 0);
lean::inc(x_1076);
lean::dec(x_1068);
x_14 = x_1076;
goto lbl_15;
}
}
else
{
obj* x_1079; obj* x_1082; obj* x_1086; 
x_1079 = lean::cnstr_get(x_1060, 0);
lean::inc(x_1079);
lean::dec(x_1060);
x_1082 = lean::cnstr_get(x_1079, 1);
lean::inc(x_1082);
lean::dec(x_1079);
lean::inc(x_1);
x_1086 = l_lean_elaborator_to__pexpr___main(x_1082, x_1, x_2);
if (lean::obj_tag(x_1086) == 0)
{
obj* x_1092; obj* x_1094; obj* x_1095; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1050);
lean::dec(x_1056);
x_1092 = lean::cnstr_get(x_1086, 0);
if (lean::is_exclusive(x_1086)) {
 lean::cnstr_set(x_1086, 0, lean::box(0));
 x_1094 = x_1086;
} else {
 lean::inc(x_1092);
 lean::dec(x_1086);
 x_1094 = lean::box(0);
}
if (lean::is_scalar(x_1094)) {
 x_1095 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1095 = x_1094;
}
lean::cnstr_set(x_1095, 0, x_1092);
return x_1095;
}
else
{
obj* x_1096; obj* x_1098; obj* x_1099; obj* x_1101; obj* x_1103; obj* x_1104; obj* x_1107; 
x_1096 = lean::cnstr_get(x_1086, 0);
if (lean::is_exclusive(x_1086)) {
 lean::cnstr_set(x_1086, 0, lean::box(0));
 x_1098 = x_1086;
} else {
 lean::inc(x_1096);
 lean::dec(x_1086);
 x_1098 = lean::box(0);
}
x_1099 = lean::cnstr_get(x_1096, 0);
x_1101 = lean::cnstr_get(x_1096, 1);
if (lean::is_exclusive(x_1096)) {
 lean::cnstr_set(x_1096, 0, lean::box(0));
 lean::cnstr_set(x_1096, 1, lean::box(0));
 x_1103 = x_1096;
} else {
 lean::inc(x_1099);
 lean::inc(x_1101);
 lean::dec(x_1096);
 x_1103 = lean::box(0);
}
x_1104 = lean::cnstr_get(x_1050, 3);
lean::inc(x_1104);
lean::inc(x_1);
x_1107 = l_lean_elaborator_to__pexpr___main(x_1104, x_1, x_1101);
if (lean::obj_tag(x_1107) == 0)
{
obj* x_1115; obj* x_1118; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1099);
lean::dec(x_1103);
lean::dec(x_1050);
lean::dec(x_1056);
x_1115 = lean::cnstr_get(x_1107, 0);
lean::inc(x_1115);
lean::dec(x_1107);
if (lean::is_scalar(x_1098)) {
 x_1118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1118 = x_1098;
 lean::cnstr_set_tag(x_1098, 0);
}
lean::cnstr_set(x_1118, 0, x_1115);
return x_1118;
}
else
{
obj* x_1119; obj* x_1122; obj* x_1124; obj* x_1127; obj* x_1131; 
x_1119 = lean::cnstr_get(x_1107, 0);
lean::inc(x_1119);
lean::dec(x_1107);
x_1122 = lean::cnstr_get(x_1119, 0);
lean::inc(x_1122);
x_1124 = lean::cnstr_get(x_1119, 1);
lean::inc(x_1124);
lean::dec(x_1119);
x_1127 = lean::cnstr_get(x_1050, 5);
lean::inc(x_1127);
lean::dec(x_1050);
lean::inc(x_1);
x_1131 = l_lean_elaborator_to__pexpr___main(x_1127, x_1, x_1124);
if (lean::obj_tag(x_1131) == 0)
{
obj* x_1139; obj* x_1142; 
lean::dec(x_1122);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1099);
lean::dec(x_1103);
lean::dec(x_1056);
x_1139 = lean::cnstr_get(x_1131, 0);
lean::inc(x_1139);
lean::dec(x_1131);
if (lean::is_scalar(x_1098)) {
 x_1142 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1142 = x_1098;
 lean::cnstr_set_tag(x_1098, 0);
}
lean::cnstr_set(x_1142, 0, x_1139);
return x_1142;
}
else
{
obj* x_1144; obj* x_1147; obj* x_1149; obj* x_1152; obj* x_1153; obj* x_1154; 
lean::dec(x_1098);
x_1144 = lean::cnstr_get(x_1131, 0);
lean::inc(x_1144);
lean::dec(x_1131);
x_1147 = lean::cnstr_get(x_1144, 0);
lean::inc(x_1147);
x_1149 = lean::cnstr_get(x_1144, 1);
lean::inc(x_1149);
lean::dec(x_1144);
x_1152 = l_lean_elaborator_mangle__ident(x_1056);
x_1153 = lean_expr_mk_let(x_1152, x_1099, x_1122, x_1147);
if (lean::is_scalar(x_1103)) {
 x_1154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1154 = x_1103;
}
lean::cnstr_set(x_1154, 0, x_1153);
lean::cnstr_set(x_1154, 1, x_1149);
x_14 = x_1154;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1159; obj* x_1162; 
lean::dec(x_1060);
lean::dec(x_1058);
lean::dec(x_1050);
lean::dec(x_1056);
x_1159 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_0);
x_1162 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1159, x_1, x_2);
if (lean::obj_tag(x_1162) == 0)
{
obj* x_1166; obj* x_1168; obj* x_1169; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1166 = lean::cnstr_get(x_1162, 0);
if (lean::is_exclusive(x_1162)) {
 lean::cnstr_set(x_1162, 0, lean::box(0));
 x_1168 = x_1162;
} else {
 lean::inc(x_1166);
 lean::dec(x_1162);
 x_1168 = lean::box(0);
}
if (lean::is_scalar(x_1168)) {
 x_1169 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1169 = x_1168;
}
lean::cnstr_set(x_1169, 0, x_1166);
return x_1169;
}
else
{
obj* x_1170; 
x_1170 = lean::cnstr_get(x_1162, 0);
lean::inc(x_1170);
lean::dec(x_1162);
x_14 = x_1170;
goto lbl_15;
}
}
}
else
{
obj* x_1175; obj* x_1178; 
lean::dec(x_1050);
lean::dec(x_1051);
x_1175 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_0);
x_1178 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1175, x_1, x_2);
if (lean::obj_tag(x_1178) == 0)
{
obj* x_1182; obj* x_1184; obj* x_1185; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1182 = lean::cnstr_get(x_1178, 0);
if (lean::is_exclusive(x_1178)) {
 lean::cnstr_set(x_1178, 0, lean::box(0));
 x_1184 = x_1178;
} else {
 lean::inc(x_1182);
 lean::dec(x_1178);
 x_1184 = lean::box(0);
}
if (lean::is_scalar(x_1184)) {
 x_1185 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1185 = x_1184;
}
lean::cnstr_set(x_1185, 0, x_1182);
return x_1185;
}
else
{
obj* x_1186; 
x_1186 = lean::cnstr_get(x_1178, 0);
lean::inc(x_1186);
lean::dec(x_1178);
x_14 = x_1186;
goto lbl_15;
}
}
}
}
else
{
obj* x_1190; obj* x_1191; obj* x_1195; obj* x_1196; obj* x_1199; 
lean::dec(x_9);
x_1190 = l_lean_parser_term_show_has__view;
x_1191 = lean::cnstr_get(x_1190, 0);
lean::inc(x_1191);
lean::dec(x_1190);
lean::inc(x_0);
x_1195 = lean::apply_1(x_1191, x_0);
x_1196 = lean::cnstr_get(x_1195, 1);
lean::inc(x_1196);
lean::inc(x_1);
x_1199 = l_lean_elaborator_to__pexpr___main(x_1196, x_1, x_2);
if (lean::obj_tag(x_1199) == 0)
{
obj* x_1204; obj* x_1206; obj* x_1207; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1195);
x_1204 = lean::cnstr_get(x_1199, 0);
if (lean::is_exclusive(x_1199)) {
 lean::cnstr_set(x_1199, 0, lean::box(0));
 x_1206 = x_1199;
} else {
 lean::inc(x_1204);
 lean::dec(x_1199);
 x_1206 = lean::box(0);
}
if (lean::is_scalar(x_1206)) {
 x_1207 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1207 = x_1206;
}
lean::cnstr_set(x_1207, 0, x_1204);
return x_1207;
}
else
{
obj* x_1208; obj* x_1210; obj* x_1211; obj* x_1213; obj* x_1215; obj* x_1216; obj* x_1219; obj* x_1223; 
x_1208 = lean::cnstr_get(x_1199, 0);
if (lean::is_exclusive(x_1199)) {
 lean::cnstr_set(x_1199, 0, lean::box(0));
 x_1210 = x_1199;
} else {
 lean::inc(x_1208);
 lean::dec(x_1199);
 x_1210 = lean::box(0);
}
x_1211 = lean::cnstr_get(x_1208, 0);
x_1213 = lean::cnstr_get(x_1208, 1);
if (lean::is_exclusive(x_1208)) {
 lean::cnstr_set(x_1208, 0, lean::box(0));
 lean::cnstr_set(x_1208, 1, lean::box(0));
 x_1215 = x_1208;
} else {
 lean::inc(x_1211);
 lean::inc(x_1213);
 lean::dec(x_1208);
 x_1215 = lean::box(0);
}
x_1216 = lean::cnstr_get(x_1195, 3);
lean::inc(x_1216);
lean::dec(x_1195);
x_1219 = lean::cnstr_get(x_1216, 1);
lean::inc(x_1219);
lean::dec(x_1216);
lean::inc(x_1);
x_1223 = l_lean_elaborator_to__pexpr___main(x_1219, x_1, x_1213);
if (lean::obj_tag(x_1223) == 0)
{
obj* x_1229; obj* x_1232; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1215);
lean::dec(x_1211);
x_1229 = lean::cnstr_get(x_1223, 0);
lean::inc(x_1229);
lean::dec(x_1223);
if (lean::is_scalar(x_1210)) {
 x_1232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1232 = x_1210;
 lean::cnstr_set_tag(x_1210, 0);
}
lean::cnstr_set(x_1232, 0, x_1229);
return x_1232;
}
else
{
obj* x_1234; obj* x_1237; obj* x_1239; obj* x_1242; uint8 x_1243; obj* x_1244; obj* x_1245; obj* x_1246; obj* x_1247; obj* x_1248; obj* x_1249; 
lean::dec(x_1210);
x_1234 = lean::cnstr_get(x_1223, 0);
lean::inc(x_1234);
lean::dec(x_1223);
x_1237 = lean::cnstr_get(x_1234, 0);
lean::inc(x_1237);
x_1239 = lean::cnstr_get(x_1234, 1);
lean::inc(x_1239);
lean::dec(x_1234);
x_1242 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1243 = 0;
x_1244 = l_lean_elaborator_to__pexpr___main___closed__38;
x_1245 = lean_expr_mk_lambda(x_1242, x_1243, x_1211, x_1244);
x_1246 = lean_expr_mk_app(x_1245, x_1237);
x_1247 = l_lean_elaborator_to__pexpr___main___closed__39;
x_1248 = l_lean_elaborator_expr_mk__annotation(x_1247, x_1246);
if (lean::is_scalar(x_1215)) {
 x_1249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1249 = x_1215;
}
lean::cnstr_set(x_1249, 0, x_1248);
lean::cnstr_set(x_1249, 1, x_1239);
x_14 = x_1249;
goto lbl_15;
}
}
}
}
else
{
obj* x_1251; obj* x_1252; obj* x_1256; obj* x_1257; obj* x_1259; obj* x_1262; 
lean::dec(x_9);
x_1251 = l_lean_parser_term_have_has__view;
x_1252 = lean::cnstr_get(x_1251, 0);
lean::inc(x_1252);
lean::dec(x_1251);
lean::inc(x_0);
x_1256 = lean::apply_1(x_1252, x_0);
x_1259 = lean::cnstr_get(x_1256, 2);
lean::inc(x_1259);
lean::inc(x_1);
x_1262 = l_lean_elaborator_to__pexpr___main(x_1259, x_1, x_2);
if (lean::obj_tag(x_1262) == 0)
{
obj* x_1267; obj* x_1269; obj* x_1270; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1256);
x_1267 = lean::cnstr_get(x_1262, 0);
if (lean::is_exclusive(x_1262)) {
 lean::cnstr_set(x_1262, 0, lean::box(0));
 x_1269 = x_1262;
} else {
 lean::inc(x_1267);
 lean::dec(x_1262);
 x_1269 = lean::box(0);
}
if (lean::is_scalar(x_1269)) {
 x_1270 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1270 = x_1269;
}
lean::cnstr_set(x_1270, 0, x_1267);
return x_1270;
}
else
{
obj* x_1271; obj* x_1273; obj* x_1274; obj* x_1276; obj* x_1278; obj* x_1279; obj* x_1282; 
x_1271 = lean::cnstr_get(x_1262, 0);
if (lean::is_exclusive(x_1262)) {
 lean::cnstr_set(x_1262, 0, lean::box(0));
 x_1273 = x_1262;
} else {
 lean::inc(x_1271);
 lean::dec(x_1262);
 x_1273 = lean::box(0);
}
x_1274 = lean::cnstr_get(x_1271, 0);
x_1276 = lean::cnstr_get(x_1271, 1);
if (lean::is_exclusive(x_1271)) {
 lean::cnstr_set(x_1271, 0, lean::box(0));
 lean::cnstr_set(x_1271, 1, lean::box(0));
 x_1278 = x_1271;
} else {
 lean::inc(x_1274);
 lean::inc(x_1276);
 lean::dec(x_1271);
 x_1278 = lean::box(0);
}
x_1279 = lean::cnstr_get(x_1256, 5);
lean::inc(x_1279);
lean::inc(x_1);
x_1282 = l_lean_elaborator_to__pexpr___main(x_1279, x_1, x_1276);
if (lean::obj_tag(x_1282) == 0)
{
obj* x_1289; obj* x_1292; 
lean::dec(x_1274);
lean::dec(x_1278);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1256);
x_1289 = lean::cnstr_get(x_1282, 0);
lean::inc(x_1289);
lean::dec(x_1282);
if (lean::is_scalar(x_1273)) {
 x_1292 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1292 = x_1273;
 lean::cnstr_set_tag(x_1273, 0);
}
lean::cnstr_set(x_1292, 0, x_1289);
return x_1292;
}
else
{
obj* x_1294; obj* x_1297; obj* x_1299; obj* x_1302; obj* x_1304; obj* x_1305; obj* x_1306; obj* x_1307; obj* x_1308; obj* x_1309; uint8 x_1310; obj* x_1311; obj* x_1312; 
lean::dec(x_1273);
x_1294 = lean::cnstr_get(x_1282, 0);
lean::inc(x_1294);
lean::dec(x_1282);
x_1297 = lean::cnstr_get(x_1294, 0);
lean::inc(x_1297);
x_1299 = lean::cnstr_get(x_1294, 1);
lean::inc(x_1299);
lean::dec(x_1294);
x_1302 = lean::cnstr_get(x_1256, 1);
lean::inc(x_1302);
x_1304 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1305 = l_option_map___rarg(x_1304, x_1302);
x_1306 = l_lean_elaborator_to__pexpr___main___closed__28;
x_1307 = l_option_map___rarg(x_1306, x_1305);
x_1308 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1309 = l_option_get__or__else___main___rarg(x_1307, x_1308);
x_1310 = 0;
x_1311 = lean_expr_mk_lambda(x_1309, x_1310, x_1274, x_1297);
if (lean::is_scalar(x_1278)) {
 x_1312 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1312 = x_1278;
}
lean::cnstr_set(x_1312, 0, x_1311);
lean::cnstr_set(x_1312, 1, x_1299);
x_1257 = x_1312;
goto lbl_1258;
}
}
lbl_1258:
{
obj* x_1313; obj* x_1315; obj* x_1317; obj* x_1318; 
x_1313 = lean::cnstr_get(x_1257, 0);
x_1315 = lean::cnstr_get(x_1257, 1);
if (lean::is_exclusive(x_1257)) {
 lean::cnstr_set(x_1257, 0, lean::box(0));
 lean::cnstr_set(x_1257, 1, lean::box(0));
 x_1317 = x_1257;
} else {
 lean::inc(x_1313);
 lean::inc(x_1315);
 lean::dec(x_1257);
 x_1317 = lean::box(0);
}
x_1318 = lean::cnstr_get(x_1256, 3);
lean::inc(x_1318);
lean::dec(x_1256);
if (lean::obj_tag(x_1318) == 0)
{
obj* x_1321; obj* x_1324; obj* x_1328; 
x_1321 = lean::cnstr_get(x_1318, 0);
lean::inc(x_1321);
lean::dec(x_1318);
x_1324 = lean::cnstr_get(x_1321, 1);
lean::inc(x_1324);
lean::dec(x_1321);
lean::inc(x_1);
x_1328 = l_lean_elaborator_to__pexpr___main(x_1324, x_1, x_1315);
if (lean::obj_tag(x_1328) == 0)
{
obj* x_1334; obj* x_1336; obj* x_1337; 
lean::dec(x_1313);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1317);
x_1334 = lean::cnstr_get(x_1328, 0);
if (lean::is_exclusive(x_1328)) {
 lean::cnstr_set(x_1328, 0, lean::box(0));
 x_1336 = x_1328;
} else {
 lean::inc(x_1334);
 lean::dec(x_1328);
 x_1336 = lean::box(0);
}
if (lean::is_scalar(x_1336)) {
 x_1337 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1337 = x_1336;
}
lean::cnstr_set(x_1337, 0, x_1334);
return x_1337;
}
else
{
obj* x_1338; obj* x_1341; obj* x_1343; obj* x_1346; obj* x_1347; obj* x_1348; obj* x_1349; 
x_1338 = lean::cnstr_get(x_1328, 0);
lean::inc(x_1338);
lean::dec(x_1328);
x_1341 = lean::cnstr_get(x_1338, 0);
lean::inc(x_1341);
x_1343 = lean::cnstr_get(x_1338, 1);
lean::inc(x_1343);
lean::dec(x_1338);
x_1346 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1347 = l_lean_elaborator_expr_mk__annotation(x_1346, x_1313);
x_1348 = lean_expr_mk_app(x_1347, x_1341);
if (lean::is_scalar(x_1317)) {
 x_1349 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1349 = x_1317;
}
lean::cnstr_set(x_1349, 0, x_1348);
lean::cnstr_set(x_1349, 1, x_1343);
x_14 = x_1349;
goto lbl_15;
}
}
else
{
obj* x_1350; obj* x_1353; obj* x_1356; obj* x_1360; 
x_1350 = lean::cnstr_get(x_1318, 0);
lean::inc(x_1350);
lean::dec(x_1318);
x_1353 = lean::cnstr_get(x_1350, 1);
lean::inc(x_1353);
lean::dec(x_1350);
x_1356 = lean::cnstr_get(x_1353, 1);
lean::inc(x_1356);
lean::dec(x_1353);
lean::inc(x_1);
x_1360 = l_lean_elaborator_to__pexpr___main(x_1356, x_1, x_1315);
if (lean::obj_tag(x_1360) == 0)
{
obj* x_1366; obj* x_1368; obj* x_1369; 
lean::dec(x_1313);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1317);
x_1366 = lean::cnstr_get(x_1360, 0);
if (lean::is_exclusive(x_1360)) {
 lean::cnstr_set(x_1360, 0, lean::box(0));
 x_1368 = x_1360;
} else {
 lean::inc(x_1366);
 lean::dec(x_1360);
 x_1368 = lean::box(0);
}
if (lean::is_scalar(x_1368)) {
 x_1369 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1369 = x_1368;
}
lean::cnstr_set(x_1369, 0, x_1366);
return x_1369;
}
else
{
obj* x_1370; obj* x_1373; obj* x_1375; obj* x_1378; obj* x_1379; obj* x_1380; obj* x_1381; 
x_1370 = lean::cnstr_get(x_1360, 0);
lean::inc(x_1370);
lean::dec(x_1360);
x_1373 = lean::cnstr_get(x_1370, 0);
lean::inc(x_1373);
x_1375 = lean::cnstr_get(x_1370, 1);
lean::inc(x_1375);
lean::dec(x_1370);
x_1378 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1379 = l_lean_elaborator_expr_mk__annotation(x_1378, x_1313);
x_1380 = lean_expr_mk_app(x_1379, x_1373);
if (lean::is_scalar(x_1317)) {
 x_1381 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1381 = x_1317;
}
lean::cnstr_set(x_1381, 0, x_1380);
lean::cnstr_set(x_1381, 1, x_1375);
x_14 = x_1381;
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
obj* x_1384; 
x_1384 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1384) == 0)
{
obj* x_1386; obj* x_1387; obj* x_1388; 
lean::dec(x_1);
x_1386 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1387 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1387, 0, x_1386);
lean::cnstr_set(x_1387, 1, x_2);
x_1388 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1388, 0, x_1387);
return x_1388;
}
else
{
obj* x_1389; obj* x_1392; obj* x_1395; obj* x_1398; obj* x_1399; obj* x_1400; obj* x_1402; obj* x_1403; obj* x_1404; obj* x_1407; obj* x_1408; obj* x_1409; obj* x_1410; obj* x_1411; obj* x_1412; 
x_1389 = lean::cnstr_get(x_1384, 0);
lean::inc(x_1389);
lean::dec(x_1384);
x_1392 = lean::cnstr_get(x_1, 0);
lean::inc(x_1392);
lean::dec(x_1);
x_1395 = lean::cnstr_get(x_1392, 2);
lean::inc(x_1395);
lean::dec(x_1392);
x_1398 = l_lean_file__map_to__position(x_1395, x_1389);
x_1399 = lean::box(0);
x_1400 = lean::cnstr_get(x_1398, 1);
lean::inc(x_1400);
x_1402 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1403 = l_lean_kvmap_set__nat(x_1399, x_1402, x_1400);
x_1404 = lean::cnstr_get(x_1398, 0);
lean::inc(x_1404);
lean::dec(x_1398);
x_1407 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1408 = l_lean_kvmap_set__nat(x_1403, x_1407, x_1404);
x_1409 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1410 = lean_expr_mk_mdata(x_1408, x_1409);
x_1411 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1411, 0, x_1410);
lean::cnstr_set(x_1411, 1, x_2);
x_1412 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1412, 0, x_1411);
return x_1412;
}
}
else
{
obj* x_1415; obj* x_1416; obj* x_1417; 
lean::dec(x_1);
lean::dec(x_0);
x_1415 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1416 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1416, 0, x_1415);
lean::cnstr_set(x_1416, 1, x_2);
x_1417 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1417, 0, x_1416);
return x_1417;
}
}
}
else
{
obj* x_1419; obj* x_1420; obj* x_1424; obj* x_1425; obj* x_1428; obj* x_1429; obj* x_1430; obj* x_1432; 
lean::dec(x_9);
x_1419 = l_lean_parser_term_anonymous__constructor_has__view;
x_1420 = lean::cnstr_get(x_1419, 0);
lean::inc(x_1420);
lean::dec(x_1419);
lean::inc(x_0);
x_1424 = lean::apply_1(x_1420, x_0);
x_1425 = lean::cnstr_get(x_1424, 1);
lean::inc(x_1425);
lean::dec(x_1424);
x_1428 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_1425);
x_1429 = l_lean_expander_get__opt__type___main___closed__1;
x_1430 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_1429, x_1428);
lean::inc(x_1);
x_1432 = l_lean_elaborator_to__pexpr___main(x_1430, x_1, x_2);
if (lean::obj_tag(x_1432) == 0)
{
obj* x_1436; obj* x_1438; obj* x_1439; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1436 = lean::cnstr_get(x_1432, 0);
if (lean::is_exclusive(x_1432)) {
 lean::cnstr_set(x_1432, 0, lean::box(0));
 x_1438 = x_1432;
} else {
 lean::inc(x_1436);
 lean::dec(x_1432);
 x_1438 = lean::box(0);
}
if (lean::is_scalar(x_1438)) {
 x_1439 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1439 = x_1438;
}
lean::cnstr_set(x_1439, 0, x_1436);
return x_1439;
}
else
{
obj* x_1440; obj* x_1443; obj* x_1445; obj* x_1447; obj* x_1448; obj* x_1449; obj* x_1450; 
x_1440 = lean::cnstr_get(x_1432, 0);
lean::inc(x_1440);
lean::dec(x_1432);
x_1443 = lean::cnstr_get(x_1440, 0);
x_1445 = lean::cnstr_get(x_1440, 1);
if (lean::is_exclusive(x_1440)) {
 lean::cnstr_set(x_1440, 0, lean::box(0));
 lean::cnstr_set(x_1440, 1, lean::box(0));
 x_1447 = x_1440;
} else {
 lean::inc(x_1443);
 lean::inc(x_1445);
 lean::dec(x_1440);
 x_1447 = lean::box(0);
}
x_1448 = l_lean_elaborator_to__pexpr___main___closed__43;
x_1449 = l_lean_elaborator_expr_mk__annotation(x_1448, x_1443);
if (lean::is_scalar(x_1447)) {
 x_1450 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1450 = x_1447;
}
lean::cnstr_set(x_1450, 0, x_1449);
lean::cnstr_set(x_1450, 1, x_1445);
x_14 = x_1450;
goto lbl_15;
}
}
}
else
{
obj* x_1452; obj* x_1453; obj* x_1457; obj* x_1458; obj* x_1459; obj* x_1462; obj* x_1464; 
lean::dec(x_9);
x_1452 = l_lean_parser_term_sort__app_has__view;
x_1453 = lean::cnstr_get(x_1452, 0);
lean::inc(x_1453);
lean::dec(x_1452);
lean::inc(x_0);
x_1457 = lean::apply_1(x_1453, x_0);
x_1458 = l_lean_parser_term_sort_has__view;
x_1459 = lean::cnstr_get(x_1458, 0);
lean::inc(x_1459);
lean::dec(x_1458);
x_1462 = lean::cnstr_get(x_1457, 0);
lean::inc(x_1462);
x_1464 = lean::apply_1(x_1459, x_1462);
if (lean::obj_tag(x_1464) == 0)
{
obj* x_1466; obj* x_1470; 
lean::dec(x_1464);
x_1466 = lean::cnstr_get(x_1457, 1);
lean::inc(x_1466);
lean::dec(x_1457);
lean::inc(x_1);
x_1470 = l_lean_elaborator_to__level___main(x_1466, x_1, x_2);
if (lean::obj_tag(x_1470) == 0)
{
obj* x_1474; obj* x_1476; obj* x_1477; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1474 = lean::cnstr_get(x_1470, 0);
if (lean::is_exclusive(x_1470)) {
 lean::cnstr_set(x_1470, 0, lean::box(0));
 x_1476 = x_1470;
} else {
 lean::inc(x_1474);
 lean::dec(x_1470);
 x_1476 = lean::box(0);
}
if (lean::is_scalar(x_1476)) {
 x_1477 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1477 = x_1476;
}
lean::cnstr_set(x_1477, 0, x_1474);
return x_1477;
}
else
{
obj* x_1478; obj* x_1481; obj* x_1483; obj* x_1485; obj* x_1486; obj* x_1487; 
x_1478 = lean::cnstr_get(x_1470, 0);
lean::inc(x_1478);
lean::dec(x_1470);
x_1481 = lean::cnstr_get(x_1478, 0);
x_1483 = lean::cnstr_get(x_1478, 1);
if (lean::is_exclusive(x_1478)) {
 lean::cnstr_set(x_1478, 0, lean::box(0));
 lean::cnstr_set(x_1478, 1, lean::box(0));
 x_1485 = x_1478;
} else {
 lean::inc(x_1481);
 lean::inc(x_1483);
 lean::dec(x_1478);
 x_1485 = lean::box(0);
}
x_1486 = lean_expr_mk_sort(x_1481);
if (lean::is_scalar(x_1485)) {
 x_1487 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1487 = x_1485;
}
lean::cnstr_set(x_1487, 0, x_1486);
lean::cnstr_set(x_1487, 1, x_1483);
x_14 = x_1487;
goto lbl_15;
}
}
else
{
obj* x_1489; obj* x_1493; 
lean::dec(x_1464);
x_1489 = lean::cnstr_get(x_1457, 1);
lean::inc(x_1489);
lean::dec(x_1457);
lean::inc(x_1);
x_1493 = l_lean_elaborator_to__level___main(x_1489, x_1, x_2);
if (lean::obj_tag(x_1493) == 0)
{
obj* x_1497; obj* x_1499; obj* x_1500; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1497 = lean::cnstr_get(x_1493, 0);
if (lean::is_exclusive(x_1493)) {
 lean::cnstr_set(x_1493, 0, lean::box(0));
 x_1499 = x_1493;
} else {
 lean::inc(x_1497);
 lean::dec(x_1493);
 x_1499 = lean::box(0);
}
if (lean::is_scalar(x_1499)) {
 x_1500 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1500 = x_1499;
}
lean::cnstr_set(x_1500, 0, x_1497);
return x_1500;
}
else
{
obj* x_1501; obj* x_1504; obj* x_1506; obj* x_1508; obj* x_1509; obj* x_1510; obj* x_1511; 
x_1501 = lean::cnstr_get(x_1493, 0);
lean::inc(x_1501);
lean::dec(x_1493);
x_1504 = lean::cnstr_get(x_1501, 0);
x_1506 = lean::cnstr_get(x_1501, 1);
if (lean::is_exclusive(x_1501)) {
 lean::cnstr_set(x_1501, 0, lean::box(0));
 lean::cnstr_set(x_1501, 1, lean::box(0));
 x_1508 = x_1501;
} else {
 lean::inc(x_1504);
 lean::inc(x_1506);
 lean::dec(x_1501);
 x_1508 = lean::box(0);
}
x_1509 = level_mk_succ(x_1504);
x_1510 = lean_expr_mk_sort(x_1509);
if (lean::is_scalar(x_1508)) {
 x_1511 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1511 = x_1508;
}
lean::cnstr_set(x_1511, 0, x_1510);
lean::cnstr_set(x_1511, 1, x_1506);
x_14 = x_1511;
goto lbl_15;
}
}
}
}
else
{
obj* x_1514; obj* x_1515; obj* x_1519; 
lean::dec(x_9);
lean::dec(x_7);
x_1514 = l_lean_parser_term_sort_has__view;
x_1515 = lean::cnstr_get(x_1514, 0);
lean::inc(x_1515);
lean::dec(x_1514);
lean::inc(x_0);
x_1519 = lean::apply_1(x_1515, x_0);
if (lean::obj_tag(x_1519) == 0)
{
lean::dec(x_1519);
if (x_21 == 0)
{
obj* x_1521; 
x_1521 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1521) == 0)
{
obj* x_1523; obj* x_1524; obj* x_1525; 
lean::dec(x_1);
x_1523 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1524 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1524, 0, x_1523);
lean::cnstr_set(x_1524, 1, x_2);
x_1525 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1525, 0, x_1524);
return x_1525;
}
else
{
obj* x_1526; obj* x_1529; obj* x_1532; obj* x_1535; obj* x_1536; obj* x_1537; obj* x_1539; obj* x_1540; obj* x_1541; obj* x_1544; obj* x_1545; obj* x_1546; obj* x_1547; obj* x_1548; obj* x_1549; 
x_1526 = lean::cnstr_get(x_1521, 0);
lean::inc(x_1526);
lean::dec(x_1521);
x_1529 = lean::cnstr_get(x_1, 0);
lean::inc(x_1529);
lean::dec(x_1);
x_1532 = lean::cnstr_get(x_1529, 2);
lean::inc(x_1532);
lean::dec(x_1529);
x_1535 = l_lean_file__map_to__position(x_1532, x_1526);
x_1536 = lean::box(0);
x_1537 = lean::cnstr_get(x_1535, 1);
lean::inc(x_1537);
x_1539 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1540 = l_lean_kvmap_set__nat(x_1536, x_1539, x_1537);
x_1541 = lean::cnstr_get(x_1535, 0);
lean::inc(x_1541);
lean::dec(x_1535);
x_1544 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1545 = l_lean_kvmap_set__nat(x_1540, x_1544, x_1541);
x_1546 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1547 = lean_expr_mk_mdata(x_1545, x_1546);
x_1548 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1548, 0, x_1547);
lean::cnstr_set(x_1548, 1, x_2);
x_1549 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1549, 0, x_1548);
return x_1549;
}
}
else
{
obj* x_1552; obj* x_1553; obj* x_1554; 
lean::dec(x_1);
lean::dec(x_0);
x_1552 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1553 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1553, 0, x_1552);
lean::cnstr_set(x_1553, 1, x_2);
x_1554 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1554, 0, x_1553);
return x_1554;
}
}
else
{
lean::dec(x_1519);
if (x_21 == 0)
{
obj* x_1556; 
x_1556 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1556) == 0)
{
obj* x_1558; obj* x_1559; obj* x_1560; 
lean::dec(x_1);
x_1558 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1559 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1559, 0, x_1558);
lean::cnstr_set(x_1559, 1, x_2);
x_1560 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1560, 0, x_1559);
return x_1560;
}
else
{
obj* x_1561; obj* x_1564; obj* x_1567; obj* x_1570; obj* x_1571; obj* x_1572; obj* x_1574; obj* x_1575; obj* x_1576; obj* x_1579; obj* x_1580; obj* x_1581; obj* x_1582; obj* x_1583; obj* x_1584; 
x_1561 = lean::cnstr_get(x_1556, 0);
lean::inc(x_1561);
lean::dec(x_1556);
x_1564 = lean::cnstr_get(x_1, 0);
lean::inc(x_1564);
lean::dec(x_1);
x_1567 = lean::cnstr_get(x_1564, 2);
lean::inc(x_1567);
lean::dec(x_1564);
x_1570 = l_lean_file__map_to__position(x_1567, x_1561);
x_1571 = lean::box(0);
x_1572 = lean::cnstr_get(x_1570, 1);
lean::inc(x_1572);
x_1574 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1575 = l_lean_kvmap_set__nat(x_1571, x_1574, x_1572);
x_1576 = lean::cnstr_get(x_1570, 0);
lean::inc(x_1576);
lean::dec(x_1570);
x_1579 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1580 = l_lean_kvmap_set__nat(x_1575, x_1579, x_1576);
x_1581 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1582 = lean_expr_mk_mdata(x_1580, x_1581);
x_1583 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1583, 0, x_1582);
lean::cnstr_set(x_1583, 1, x_2);
x_1584 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1584, 0, x_1583);
return x_1584;
}
}
else
{
obj* x_1587; obj* x_1588; obj* x_1589; 
lean::dec(x_1);
lean::dec(x_0);
x_1587 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1588 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1588, 0, x_1587);
lean::cnstr_set(x_1588, 1, x_2);
x_1589 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1589, 0, x_1588);
return x_1589;
}
}
}
}
else
{
obj* x_1591; obj* x_1592; obj* x_1596; obj* x_1597; 
lean::dec(x_9);
x_1591 = l_lean_parser_term_pi_has__view;
x_1592 = lean::cnstr_get(x_1591, 0);
lean::inc(x_1592);
lean::dec(x_1591);
lean::inc(x_0);
x_1596 = lean::apply_1(x_1592, x_0);
x_1597 = lean::cnstr_get(x_1596, 1);
lean::inc(x_1597);
if (lean::obj_tag(x_1597) == 0)
{
obj* x_1601; obj* x_1604; 
lean::dec(x_1596);
lean::dec(x_1597);
x_1601 = l_lean_elaborator_to__pexpr___main___closed__45;
lean::inc(x_1);
lean::inc(x_0);
x_1604 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1601, x_1, x_2);
if (lean::obj_tag(x_1604) == 0)
{
obj* x_1608; obj* x_1610; obj* x_1611; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1608 = lean::cnstr_get(x_1604, 0);
if (lean::is_exclusive(x_1604)) {
 lean::cnstr_set(x_1604, 0, lean::box(0));
 x_1610 = x_1604;
} else {
 lean::inc(x_1608);
 lean::dec(x_1604);
 x_1610 = lean::box(0);
}
if (lean::is_scalar(x_1610)) {
 x_1611 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1611 = x_1610;
}
lean::cnstr_set(x_1611, 0, x_1608);
return x_1611;
}
else
{
obj* x_1612; 
x_1612 = lean::cnstr_get(x_1604, 0);
lean::inc(x_1612);
lean::dec(x_1604);
x_14 = x_1612;
goto lbl_15;
}
}
else
{
obj* x_1615; obj* x_1618; obj* x_1619; obj* x_1621; obj* x_1623; obj* x_1624; obj* x_1626; obj* x_1630; 
x_1615 = lean::cnstr_get(x_1597, 0);
lean::inc(x_1615);
lean::dec(x_1597);
x_1618 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1615);
x_1619 = lean::cnstr_get(x_1618, 0);
x_1621 = lean::cnstr_get(x_1618, 1);
if (lean::is_exclusive(x_1618)) {
 lean::cnstr_set(x_1618, 0, lean::box(0));
 lean::cnstr_set(x_1618, 1, lean::box(0));
 x_1623 = x_1618;
} else {
 lean::inc(x_1619);
 lean::inc(x_1621);
 lean::dec(x_1618);
 x_1623 = lean::box(0);
}
x_1624 = lean::cnstr_get(x_1621, 0);
lean::inc(x_1624);
x_1626 = lean::cnstr_get(x_1621, 1);
lean::inc(x_1626);
lean::dec(x_1621);
lean::inc(x_1);
x_1630 = l_lean_elaborator_to__pexpr___main(x_1626, x_1, x_2);
if (lean::obj_tag(x_1630) == 0)
{
obj* x_1638; obj* x_1640; obj* x_1641; 
lean::dec(x_1596);
lean::dec(x_7);
lean::dec(x_1624);
lean::dec(x_1619);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1623);
x_1638 = lean::cnstr_get(x_1630, 0);
if (lean::is_exclusive(x_1630)) {
 lean::cnstr_set(x_1630, 0, lean::box(0));
 x_1640 = x_1630;
} else {
 lean::inc(x_1638);
 lean::dec(x_1630);
 x_1640 = lean::box(0);
}
if (lean::is_scalar(x_1640)) {
 x_1641 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1641 = x_1640;
}
lean::cnstr_set(x_1641, 0, x_1638);
return x_1641;
}
else
{
obj* x_1642; obj* x_1644; obj* x_1645; obj* x_1647; obj* x_1650; obj* x_1654; 
x_1642 = lean::cnstr_get(x_1630, 0);
if (lean::is_exclusive(x_1630)) {
 lean::cnstr_set(x_1630, 0, lean::box(0));
 x_1644 = x_1630;
} else {
 lean::inc(x_1642);
 lean::dec(x_1630);
 x_1644 = lean::box(0);
}
x_1645 = lean::cnstr_get(x_1642, 0);
lean::inc(x_1645);
x_1647 = lean::cnstr_get(x_1642, 1);
lean::inc(x_1647);
lean::dec(x_1642);
x_1650 = lean::cnstr_get(x_1596, 3);
lean::inc(x_1650);
lean::dec(x_1596);
lean::inc(x_1);
x_1654 = l_lean_elaborator_to__pexpr___main(x_1650, x_1, x_1647);
if (lean::obj_tag(x_1654) == 0)
{
obj* x_1662; obj* x_1665; 
lean::dec(x_7);
lean::dec(x_1624);
lean::dec(x_1619);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1623);
lean::dec(x_1645);
x_1662 = lean::cnstr_get(x_1654, 0);
lean::inc(x_1662);
lean::dec(x_1654);
if (lean::is_scalar(x_1644)) {
 x_1665 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1665 = x_1644;
 lean::cnstr_set_tag(x_1644, 0);
}
lean::cnstr_set(x_1665, 0, x_1662);
return x_1665;
}
else
{
obj* x_1667; obj* x_1670; obj* x_1672; obj* x_1675; uint8 x_1676; obj* x_1677; obj* x_1678; 
lean::dec(x_1644);
x_1667 = lean::cnstr_get(x_1654, 0);
lean::inc(x_1667);
lean::dec(x_1654);
x_1670 = lean::cnstr_get(x_1667, 0);
lean::inc(x_1670);
x_1672 = lean::cnstr_get(x_1667, 1);
lean::inc(x_1672);
lean::dec(x_1667);
x_1675 = l_lean_elaborator_mangle__ident(x_1624);
x_1676 = lean::unbox(x_1619);
x_1677 = lean_expr_mk_pi(x_1675, x_1676, x_1645, x_1670);
if (lean::is_scalar(x_1623)) {
 x_1678 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1678 = x_1623;
}
lean::cnstr_set(x_1678, 0, x_1677);
lean::cnstr_set(x_1678, 1, x_1672);
x_14 = x_1678;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1680; obj* x_1681; obj* x_1685; obj* x_1686; 
lean::dec(x_9);
x_1680 = l_lean_parser_term_lambda_has__view;
x_1681 = lean::cnstr_get(x_1680, 0);
lean::inc(x_1681);
lean::dec(x_1680);
lean::inc(x_0);
x_1685 = lean::apply_1(x_1681, x_0);
x_1686 = lean::cnstr_get(x_1685, 1);
lean::inc(x_1686);
if (lean::obj_tag(x_1686) == 0)
{
obj* x_1690; obj* x_1693; 
lean::dec(x_1686);
lean::dec(x_1685);
x_1690 = l_lean_elaborator_to__pexpr___main___closed__46;
lean::inc(x_1);
lean::inc(x_0);
x_1693 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1690, x_1, x_2);
if (lean::obj_tag(x_1693) == 0)
{
obj* x_1697; obj* x_1699; obj* x_1700; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1697 = lean::cnstr_get(x_1693, 0);
if (lean::is_exclusive(x_1693)) {
 lean::cnstr_set(x_1693, 0, lean::box(0));
 x_1699 = x_1693;
} else {
 lean::inc(x_1697);
 lean::dec(x_1693);
 x_1699 = lean::box(0);
}
if (lean::is_scalar(x_1699)) {
 x_1700 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1700 = x_1699;
}
lean::cnstr_set(x_1700, 0, x_1697);
return x_1700;
}
else
{
obj* x_1701; 
x_1701 = lean::cnstr_get(x_1693, 0);
lean::inc(x_1701);
lean::dec(x_1693);
x_14 = x_1701;
goto lbl_15;
}
}
else
{
obj* x_1704; obj* x_1707; obj* x_1708; obj* x_1710; obj* x_1712; obj* x_1713; obj* x_1715; obj* x_1719; 
x_1704 = lean::cnstr_get(x_1686, 0);
lean::inc(x_1704);
lean::dec(x_1686);
x_1707 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1704);
x_1708 = lean::cnstr_get(x_1707, 0);
x_1710 = lean::cnstr_get(x_1707, 1);
if (lean::is_exclusive(x_1707)) {
 lean::cnstr_set(x_1707, 0, lean::box(0));
 lean::cnstr_set(x_1707, 1, lean::box(0));
 x_1712 = x_1707;
} else {
 lean::inc(x_1708);
 lean::inc(x_1710);
 lean::dec(x_1707);
 x_1712 = lean::box(0);
}
x_1713 = lean::cnstr_get(x_1710, 0);
lean::inc(x_1713);
x_1715 = lean::cnstr_get(x_1710, 1);
lean::inc(x_1715);
lean::dec(x_1710);
lean::inc(x_1);
x_1719 = l_lean_elaborator_to__pexpr___main(x_1715, x_1, x_2);
if (lean::obj_tag(x_1719) == 0)
{
obj* x_1727; obj* x_1729; obj* x_1730; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1708);
lean::dec(x_1713);
lean::dec(x_1685);
lean::dec(x_1712);
x_1727 = lean::cnstr_get(x_1719, 0);
if (lean::is_exclusive(x_1719)) {
 lean::cnstr_set(x_1719, 0, lean::box(0));
 x_1729 = x_1719;
} else {
 lean::inc(x_1727);
 lean::dec(x_1719);
 x_1729 = lean::box(0);
}
if (lean::is_scalar(x_1729)) {
 x_1730 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1730 = x_1729;
}
lean::cnstr_set(x_1730, 0, x_1727);
return x_1730;
}
else
{
obj* x_1731; obj* x_1733; obj* x_1734; obj* x_1736; obj* x_1739; obj* x_1743; 
x_1731 = lean::cnstr_get(x_1719, 0);
if (lean::is_exclusive(x_1719)) {
 lean::cnstr_set(x_1719, 0, lean::box(0));
 x_1733 = x_1719;
} else {
 lean::inc(x_1731);
 lean::dec(x_1719);
 x_1733 = lean::box(0);
}
x_1734 = lean::cnstr_get(x_1731, 0);
lean::inc(x_1734);
x_1736 = lean::cnstr_get(x_1731, 1);
lean::inc(x_1736);
lean::dec(x_1731);
x_1739 = lean::cnstr_get(x_1685, 3);
lean::inc(x_1739);
lean::dec(x_1685);
lean::inc(x_1);
x_1743 = l_lean_elaborator_to__pexpr___main(x_1739, x_1, x_1736);
if (lean::obj_tag(x_1743) == 0)
{
obj* x_1751; obj* x_1754; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1708);
lean::dec(x_1713);
lean::dec(x_1712);
lean::dec(x_1734);
x_1751 = lean::cnstr_get(x_1743, 0);
lean::inc(x_1751);
lean::dec(x_1743);
if (lean::is_scalar(x_1733)) {
 x_1754 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1754 = x_1733;
 lean::cnstr_set_tag(x_1733, 0);
}
lean::cnstr_set(x_1754, 0, x_1751);
return x_1754;
}
else
{
obj* x_1756; obj* x_1759; obj* x_1761; obj* x_1764; uint8 x_1765; obj* x_1766; obj* x_1767; 
lean::dec(x_1733);
x_1756 = lean::cnstr_get(x_1743, 0);
lean::inc(x_1756);
lean::dec(x_1743);
x_1759 = lean::cnstr_get(x_1756, 0);
lean::inc(x_1759);
x_1761 = lean::cnstr_get(x_1756, 1);
lean::inc(x_1761);
lean::dec(x_1756);
x_1764 = l_lean_elaborator_mangle__ident(x_1713);
x_1765 = lean::unbox(x_1708);
x_1766 = lean_expr_mk_lambda(x_1764, x_1765, x_1734, x_1759);
if (lean::is_scalar(x_1712)) {
 x_1767 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1767 = x_1712;
}
lean::cnstr_set(x_1767, 0, x_1766);
lean::cnstr_set(x_1767, 1, x_1761);
x_14 = x_1767;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1769; obj* x_1770; obj* x_1774; obj* x_1775; obj* x_1778; 
lean::dec(x_9);
x_1769 = l_lean_parser_term_app_has__view;
x_1770 = lean::cnstr_get(x_1769, 0);
lean::inc(x_1770);
lean::dec(x_1769);
lean::inc(x_0);
x_1774 = lean::apply_1(x_1770, x_0);
x_1775 = lean::cnstr_get(x_1774, 0);
lean::inc(x_1775);
lean::inc(x_1);
x_1778 = l_lean_elaborator_to__pexpr___main(x_1775, x_1, x_2);
if (lean::obj_tag(x_1778) == 0)
{
obj* x_1783; obj* x_1785; obj* x_1786; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1774);
x_1783 = lean::cnstr_get(x_1778, 0);
if (lean::is_exclusive(x_1778)) {
 lean::cnstr_set(x_1778, 0, lean::box(0));
 x_1785 = x_1778;
} else {
 lean::inc(x_1783);
 lean::dec(x_1778);
 x_1785 = lean::box(0);
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
obj* x_1787; obj* x_1789; obj* x_1790; obj* x_1792; obj* x_1794; obj* x_1795; obj* x_1799; 
x_1787 = lean::cnstr_get(x_1778, 0);
if (lean::is_exclusive(x_1778)) {
 lean::cnstr_set(x_1778, 0, lean::box(0));
 x_1789 = x_1778;
} else {
 lean::inc(x_1787);
 lean::dec(x_1778);
 x_1789 = lean::box(0);
}
x_1790 = lean::cnstr_get(x_1787, 0);
x_1792 = lean::cnstr_get(x_1787, 1);
if (lean::is_exclusive(x_1787)) {
 lean::cnstr_set(x_1787, 0, lean::box(0));
 lean::cnstr_set(x_1787, 1, lean::box(0));
 x_1794 = x_1787;
} else {
 lean::inc(x_1790);
 lean::inc(x_1792);
 lean::dec(x_1787);
 x_1794 = lean::box(0);
}
x_1795 = lean::cnstr_get(x_1774, 1);
lean::inc(x_1795);
lean::dec(x_1774);
lean::inc(x_1);
x_1799 = l_lean_elaborator_to__pexpr___main(x_1795, x_1, x_1792);
if (lean::obj_tag(x_1799) == 0)
{
obj* x_1805; obj* x_1808; 
lean::dec(x_1794);
lean::dec(x_1790);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1805 = lean::cnstr_get(x_1799, 0);
lean::inc(x_1805);
lean::dec(x_1799);
if (lean::is_scalar(x_1789)) {
 x_1808 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1808 = x_1789;
 lean::cnstr_set_tag(x_1789, 0);
}
lean::cnstr_set(x_1808, 0, x_1805);
return x_1808;
}
else
{
obj* x_1810; obj* x_1813; obj* x_1815; obj* x_1818; obj* x_1819; 
lean::dec(x_1789);
x_1810 = lean::cnstr_get(x_1799, 0);
lean::inc(x_1810);
lean::dec(x_1799);
x_1813 = lean::cnstr_get(x_1810, 0);
lean::inc(x_1813);
x_1815 = lean::cnstr_get(x_1810, 1);
lean::inc(x_1815);
lean::dec(x_1810);
x_1818 = lean_expr_mk_app(x_1790, x_1813);
if (lean::is_scalar(x_1794)) {
 x_1819 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1819 = x_1794;
}
lean::cnstr_set(x_1819, 0, x_1818);
lean::cnstr_set(x_1819, 1, x_1815);
x_14 = x_1819;
goto lbl_15;
}
}
}
}
else
{
obj* x_1821; obj* x_1822; obj* x_1826; obj* x_1827; obj* x_1829; 
lean::dec(x_9);
x_1821 = l_lean_parser_ident__univs_has__view;
x_1822 = lean::cnstr_get(x_1821, 0);
lean::inc(x_1822);
lean::dec(x_1821);
lean::inc(x_0);
x_1826 = lean::apply_1(x_1822, x_0);
x_1827 = lean::cnstr_get(x_1826, 0);
lean::inc(x_1827);
x_1829 = lean::cnstr_get(x_1826, 1);
lean::inc(x_1829);
lean::dec(x_1826);
if (lean::obj_tag(x_1829) == 0)
{
obj* x_1833; obj* x_1834; obj* x_1835; obj* x_1836; obj* x_1839; obj* x_1840; obj* x_1841; obj* x_1842; obj* x_1843; obj* x_1844; uint8 x_1845; 
lean::inc(x_1827);
x_1833 = l_lean_elaborator_mangle__ident(x_1827);
x_1834 = lean::box(0);
x_1835 = lean_expr_mk_const(x_1833, x_1834);
x_1836 = lean::cnstr_get(x_1827, 3);
lean::inc(x_1836);
lean::dec(x_1827);
x_1839 = lean::mk_nat_obj(0u);
x_1840 = l_list_enum__from___main___rarg(x_1839, x_1836);
x_1841 = l_lean_elaborator_to__pexpr___main___closed__47;
x_1842 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(x_1841, x_1840);
x_1843 = lean_expr_mk_mdata(x_1842, x_1835);
x_1844 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1845 = lean_name_dec_eq(x_7, x_1844);
lean::dec(x_7);
if (x_1845 == 0)
{
obj* x_1847; 
x_1847 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1847) == 0)
{
obj* x_1849; obj* x_1850; 
lean::dec(x_1);
x_1849 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1849, 0, x_1843);
lean::cnstr_set(x_1849, 1, x_2);
x_1850 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1850, 0, x_1849);
return x_1850;
}
else
{
obj* x_1851; obj* x_1854; obj* x_1857; obj* x_1860; obj* x_1861; obj* x_1863; obj* x_1864; obj* x_1865; obj* x_1868; obj* x_1869; obj* x_1870; obj* x_1871; obj* x_1872; 
x_1851 = lean::cnstr_get(x_1847, 0);
lean::inc(x_1851);
lean::dec(x_1847);
x_1854 = lean::cnstr_get(x_1, 0);
lean::inc(x_1854);
lean::dec(x_1);
x_1857 = lean::cnstr_get(x_1854, 2);
lean::inc(x_1857);
lean::dec(x_1854);
x_1860 = l_lean_file__map_to__position(x_1857, x_1851);
x_1861 = lean::cnstr_get(x_1860, 1);
lean::inc(x_1861);
x_1863 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1864 = l_lean_kvmap_set__nat(x_1834, x_1863, x_1861);
x_1865 = lean::cnstr_get(x_1860, 0);
lean::inc(x_1865);
lean::dec(x_1860);
x_1868 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1869 = l_lean_kvmap_set__nat(x_1864, x_1868, x_1865);
x_1870 = lean_expr_mk_mdata(x_1869, x_1843);
x_1871 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1871, 0, x_1870);
lean::cnstr_set(x_1871, 1, x_2);
x_1872 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1872, 0, x_1871);
return x_1872;
}
}
else
{
obj* x_1875; obj* x_1876; 
lean::dec(x_1);
lean::dec(x_0);
x_1875 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1875, 0, x_1843);
lean::cnstr_set(x_1875, 1, x_2);
x_1876 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1876, 0, x_1875);
return x_1876;
}
}
else
{
obj* x_1877; obj* x_1880; obj* x_1884; 
x_1877 = lean::cnstr_get(x_1829, 0);
lean::inc(x_1877);
lean::dec(x_1829);
x_1880 = lean::cnstr_get(x_1877, 1);
lean::inc(x_1880);
lean::dec(x_1877);
lean::inc(x_1);
x_1884 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_1880, x_1, x_2);
if (lean::obj_tag(x_1884) == 0)
{
obj* x_1889; obj* x_1891; obj* x_1892; 
lean::dec(x_1827);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1889 = lean::cnstr_get(x_1884, 0);
if (lean::is_exclusive(x_1884)) {
 lean::cnstr_set(x_1884, 0, lean::box(0));
 x_1891 = x_1884;
} else {
 lean::inc(x_1889);
 lean::dec(x_1884);
 x_1891 = lean::box(0);
}
if (lean::is_scalar(x_1891)) {
 x_1892 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1892 = x_1891;
}
lean::cnstr_set(x_1892, 0, x_1889);
return x_1892;
}
else
{
obj* x_1893; obj* x_1896; obj* x_1898; obj* x_1900; obj* x_1902; obj* x_1903; obj* x_1904; obj* x_1907; obj* x_1908; obj* x_1909; obj* x_1910; obj* x_1911; obj* x_1912; 
x_1893 = lean::cnstr_get(x_1884, 0);
lean::inc(x_1893);
lean::dec(x_1884);
x_1896 = lean::cnstr_get(x_1893, 0);
x_1898 = lean::cnstr_get(x_1893, 1);
if (lean::is_exclusive(x_1893)) {
 lean::cnstr_set(x_1893, 0, lean::box(0));
 lean::cnstr_set(x_1893, 1, lean::box(0));
 x_1900 = x_1893;
} else {
 lean::inc(x_1896);
 lean::inc(x_1898);
 lean::dec(x_1893);
 x_1900 = lean::box(0);
}
lean::inc(x_1827);
x_1902 = l_lean_elaborator_mangle__ident(x_1827);
x_1903 = lean_expr_mk_const(x_1902, x_1896);
x_1904 = lean::cnstr_get(x_1827, 3);
lean::inc(x_1904);
lean::dec(x_1827);
x_1907 = lean::mk_nat_obj(0u);
x_1908 = l_list_enum__from___main___rarg(x_1907, x_1904);
x_1909 = l_lean_elaborator_to__pexpr___main___closed__47;
x_1910 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(x_1909, x_1908);
x_1911 = lean_expr_mk_mdata(x_1910, x_1903);
if (lean::is_scalar(x_1900)) {
 x_1912 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1912 = x_1900;
}
lean::cnstr_set(x_1912, 0, x_1911);
lean::cnstr_set(x_1912, 1, x_1898);
x_14 = x_1912;
goto lbl_15;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_1916; obj* x_1918; obj* x_1919; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1916 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 x_1918 = x_12;
} else {
 lean::inc(x_1916);
 lean::dec(x_12);
 x_1918 = lean::box(0);
}
if (lean::is_scalar(x_1918)) {
 x_1919 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1919 = x_1918;
}
lean::cnstr_set(x_1919, 0, x_1916);
return x_1919;
}
else
{
obj* x_1920; obj* x_1922; obj* x_1923; obj* x_1925; obj* x_1927; obj* x_1928; uint8 x_1929; 
x_1920 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 x_1922 = x_12;
} else {
 lean::inc(x_1920);
 lean::dec(x_12);
 x_1922 = lean::box(0);
}
x_1923 = lean::cnstr_get(x_1920, 0);
x_1925 = lean::cnstr_get(x_1920, 1);
if (lean::is_exclusive(x_1920)) {
 lean::cnstr_set(x_1920, 0, lean::box(0));
 lean::cnstr_set(x_1920, 1, lean::box(0));
 x_1927 = x_1920;
} else {
 lean::inc(x_1923);
 lean::inc(x_1925);
 lean::dec(x_1920);
 x_1927 = lean::box(0);
}
x_1928 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1929 = lean_name_dec_eq(x_7, x_1928);
lean::dec(x_7);
if (x_1929 == 0)
{
obj* x_1931; 
x_1931 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1931) == 0)
{
obj* x_1933; obj* x_1934; 
lean::dec(x_1);
if (lean::is_scalar(x_1927)) {
 x_1933 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1933 = x_1927;
}
lean::cnstr_set(x_1933, 0, x_1923);
lean::cnstr_set(x_1933, 1, x_1925);
if (lean::is_scalar(x_1922)) {
 x_1934 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1934 = x_1922;
}
lean::cnstr_set(x_1934, 0, x_1933);
return x_1934;
}
else
{
obj* x_1935; obj* x_1938; obj* x_1941; obj* x_1944; obj* x_1945; obj* x_1946; obj* x_1948; obj* x_1949; obj* x_1950; obj* x_1953; obj* x_1954; obj* x_1955; obj* x_1956; obj* x_1957; 
x_1935 = lean::cnstr_get(x_1931, 0);
lean::inc(x_1935);
lean::dec(x_1931);
x_1938 = lean::cnstr_get(x_1, 0);
lean::inc(x_1938);
lean::dec(x_1);
x_1941 = lean::cnstr_get(x_1938, 2);
lean::inc(x_1941);
lean::dec(x_1938);
x_1944 = l_lean_file__map_to__position(x_1941, x_1935);
x_1945 = lean::box(0);
x_1946 = lean::cnstr_get(x_1944, 1);
lean::inc(x_1946);
x_1948 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1949 = l_lean_kvmap_set__nat(x_1945, x_1948, x_1946);
x_1950 = lean::cnstr_get(x_1944, 0);
lean::inc(x_1950);
lean::dec(x_1944);
x_1953 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1954 = l_lean_kvmap_set__nat(x_1949, x_1953, x_1950);
x_1955 = lean_expr_mk_mdata(x_1954, x_1923);
if (lean::is_scalar(x_1927)) {
 x_1956 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1956 = x_1927;
}
lean::cnstr_set(x_1956, 0, x_1955);
lean::cnstr_set(x_1956, 1, x_1925);
if (lean::is_scalar(x_1922)) {
 x_1957 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1957 = x_1922;
}
lean::cnstr_set(x_1957, 0, x_1956);
return x_1957;
}
}
else
{
obj* x_1960; obj* x_1961; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_1927)) {
 x_1960 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1960 = x_1927;
}
lean::cnstr_set(x_1960, 0, x_1923);
lean::cnstr_set(x_1960, 1, x_1925);
if (lean::is_scalar(x_1922)) {
 x_1961 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1961 = x_1922;
}
lean::cnstr_set(x_1961, 0, x_1960);
return x_1961;
}
}
}
lbl_15:
{
obj* x_1962; obj* x_1964; obj* x_1966; obj* x_1967; uint8 x_1968; 
x_1962 = lean::cnstr_get(x_14, 0);
x_1964 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_set(x_14, 1, lean::box(0));
 x_1966 = x_14;
} else {
 lean::inc(x_1962);
 lean::inc(x_1964);
 lean::dec(x_14);
 x_1966 = lean::box(0);
}
x_1967 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1968 = lean_name_dec_eq(x_7, x_1967);
lean::dec(x_7);
if (x_1968 == 0)
{
obj* x_1970; 
x_1970 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1970) == 0)
{
obj* x_1972; obj* x_1973; 
lean::dec(x_1);
if (lean::is_scalar(x_1966)) {
 x_1972 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1972 = x_1966;
}
lean::cnstr_set(x_1972, 0, x_1962);
lean::cnstr_set(x_1972, 1, x_1964);
x_1973 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1973, 0, x_1972);
return x_1973;
}
else
{
obj* x_1974; obj* x_1977; obj* x_1980; obj* x_1983; obj* x_1984; obj* x_1985; obj* x_1987; obj* x_1988; obj* x_1989; obj* x_1992; obj* x_1993; obj* x_1994; obj* x_1995; obj* x_1996; 
x_1974 = lean::cnstr_get(x_1970, 0);
lean::inc(x_1974);
lean::dec(x_1970);
x_1977 = lean::cnstr_get(x_1, 0);
lean::inc(x_1977);
lean::dec(x_1);
x_1980 = lean::cnstr_get(x_1977, 2);
lean::inc(x_1980);
lean::dec(x_1977);
x_1983 = l_lean_file__map_to__position(x_1980, x_1974);
x_1984 = lean::box(0);
x_1985 = lean::cnstr_get(x_1983, 1);
lean::inc(x_1985);
x_1987 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1988 = l_lean_kvmap_set__nat(x_1984, x_1987, x_1985);
x_1989 = lean::cnstr_get(x_1983, 0);
lean::inc(x_1989);
lean::dec(x_1983);
x_1992 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1993 = l_lean_kvmap_set__nat(x_1988, x_1992, x_1989);
x_1994 = lean_expr_mk_mdata(x_1993, x_1962);
if (lean::is_scalar(x_1966)) {
 x_1995 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1995 = x_1966;
}
lean::cnstr_set(x_1995, 0, x_1994);
lean::cnstr_set(x_1995, 1, x_1964);
x_1996 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1996, 0, x_1995);
return x_1996;
}
}
else
{
obj* x_1999; obj* x_2000; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_1966)) {
 x_1999 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1999 = x_1966;
}
lean::cnstr_set(x_1999, 0, x_1962);
lean::cnstr_set(x_1999, 1, x_1964);
x_2000 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2000, 0, x_1999);
return x_2000;
}
}
lbl_17:
{
obj* x_2001; obj* x_2003; obj* x_2005; 
x_2001 = lean::cnstr_get(x_16, 0);
x_2003 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_2005 = x_16;
} else {
 lean::inc(x_2001);
 lean::inc(x_2003);
 lean::dec(x_16);
 x_2005 = lean::box(0);
}
if (lean::obj_tag(x_2001) == 0)
{
obj* x_2008; obj* x_2011; 
lean::dec(x_9);
lean::dec(x_2005);
x_2008 = l_lean_elaborator_to__pexpr___main___closed__5;
lean::inc(x_1);
lean::inc(x_0);
x_2011 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2008, x_1, x_2003);
if (lean::obj_tag(x_2011) == 0)
{
obj* x_2015; obj* x_2017; obj* x_2018; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_2015 = lean::cnstr_get(x_2011, 0);
if (lean::is_exclusive(x_2011)) {
 lean::cnstr_set(x_2011, 0, lean::box(0));
 x_2017 = x_2011;
} else {
 lean::inc(x_2015);
 lean::dec(x_2011);
 x_2017 = lean::box(0);
}
if (lean::is_scalar(x_2017)) {
 x_2018 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2018 = x_2017;
}
lean::cnstr_set(x_2018, 0, x_2015);
return x_2018;
}
else
{
obj* x_2019; 
x_2019 = lean::cnstr_get(x_2011, 0);
lean::inc(x_2019);
lean::dec(x_2011);
x_14 = x_2019;
goto lbl_15;
}
}
else
{
obj* x_2022; obj* x_2024; obj* x_2027; obj* x_2028; obj* x_2029; obj* x_2030; obj* x_2031; obj* x_2032; obj* x_2033; obj* x_2034; obj* x_2035; 
x_2022 = lean::cnstr_get(x_2001, 0);
lean::inc(x_2022);
x_2024 = lean::cnstr_get(x_2001, 1);
lean::inc(x_2024);
lean::dec(x_2001);
x_2027 = lean::box(0);
x_2028 = lean::mk_nat_obj(0u);
x_2029 = l_list_length__aux___main___rarg(x_9, x_2028);
x_2030 = l_lean_elaborator_to__pexpr___main___closed__6;
x_2031 = l_lean_kvmap_set__nat(x_2027, x_2030, x_2029);
x_2032 = l_list_reverse___rarg(x_2024);
x_2033 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_2022, x_2032);
x_2034 = lean_expr_mk_mdata(x_2031, x_2033);
if (lean::is_scalar(x_2005)) {
 x_2035 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2035 = x_2005;
}
lean::cnstr_set(x_2035, 0, x_2034);
lean::cnstr_set(x_2035, 1, x_2003);
x_14 = x_2035;
goto lbl_15;
}
}
}
default:
{
obj* x_2036; 
x_2036 = lean::box(0);
x_3 = x_2036;
goto lbl_4;
}
}
lbl_4:
{
obj* x_2039; obj* x_2040; obj* x_2041; obj* x_2042; obj* x_2043; obj* x_2045; 
lean::dec(x_3);
lean::inc(x_0);
x_2039 = l_lean_parser_syntax_to__format___main(x_0);
x_2040 = lean::mk_nat_obj(80u);
x_2041 = l_lean_format_pretty(x_2039, x_2040);
x_2042 = l_lean_elaborator_to__pexpr___main___closed__1;
x_2043 = lean::string_append(x_2042, x_2041);
lean::dec(x_2041);
x_2045 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2043, x_1, x_2);
return x_2045;
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
x_24 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_10, x_1, x_2);
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
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_4, x_1, x_2);
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
x_51 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_34, x_1, x_2);
x_52 = l_rbnode_balance2__node___main___rarg(x_51, x_30, x_32, x_28);
return x_52;
}
else
{
obj* x_53; obj* x_54; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_34, x_1, x_2);
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
x_58 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_28, x_1, x_2);
x_59 = l_rbnode_balance1__node___main___rarg(x_58, x_30, x_32, x_34);
return x_59;
}
else
{
obj* x_60; obj* x_61; 
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_28, x_1, x_2);
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
return x_0;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
x_2 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(x_1, x_0);
return x_2;
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
x_24 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_10, x_1, x_2);
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
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_4, x_1, x_2);
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
x_51 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_34, x_1, x_2);
x_52 = l_rbnode_balance2__node___main___rarg(x_51, x_30, x_32, x_28);
return x_52;
}
else
{
obj* x_53; obj* x_54; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_34, x_1, x_2);
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
x_58 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_28, x_1, x_2);
x_59 = l_rbnode_balance1__node___main___rarg(x_58, x_30, x_32, x_34);
return x_59;
}
else
{
obj* x_60; obj* x_61; 
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_28, x_1, x_2);
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
return x_0;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1;
x_2 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(x_1, x_0);
return x_2;
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
x_24 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_10, x_1, x_2);
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
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_4, x_1, x_2);
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
x_51 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_34, x_1, x_2);
x_52 = l_rbnode_balance2__node___main___rarg(x_51, x_30, x_32, x_28);
return x_52;
}
else
{
obj* x_53; obj* x_54; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_34, x_1, x_2);
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
x_58 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_28, x_1, x_2);
x_59 = l_rbnode_balance1__node___main___rarg(x_58, x_30, x_32, x_34);
return x_59;
}
else
{
obj* x_60; obj* x_61; 
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_28, x_1, x_2);
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
obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
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
x_25 = l_lean_kvmap_set__nat(x_11, x_24, x_22);
x_26 = lean::cnstr_get(x_21, 0);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_lean_elaborator_to__pexpr___main___closed__4;
x_30 = l_lean_kvmap_set__nat(x_25, x_29, x_26);
x_31 = lean_expr_mk_mdata(x_30, x_13);
x_9 = x_31;
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
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_9);
x_36 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_38 = x_8;
} else {
 lean::inc(x_36);
 lean::dec(x_8);
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
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_62; obj* x_63; obj* x_65; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_80; 
x_40 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_42 = x_8;
} else {
 lean::inc(x_40);
 lean::dec(x_8);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 0);
x_45 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_set(x_40, 0, lean::box(0));
 lean::cnstr_set(x_40, 1, lean::box(0));
 x_47 = x_40;
} else {
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_4, 0);
lean::inc(x_48);
lean::dec(x_4);
x_51 = lean::cnstr_get(x_3, 8);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_3, 9);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_3, 4);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_55, 1);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_57, 0);
lean::inc(x_59);
lean::dec(x_57);
x_62 = l_list_reverse___rarg(x_59);
x_63 = lean::cnstr_get(x_55, 2);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_63, 0);
lean::inc(x_65);
lean::dec(x_63);
x_68 = l_list_reverse___rarg(x_65);
x_69 = lean::cnstr_get(x_55, 3);
lean::inc(x_69);
x_71 = l_rbtree_to__list___rarg(x_69);
x_72 = lean::cnstr_get(x_55, 6);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_3, 10);
lean::inc(x_74);
x_76 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_76, 0, x_51);
lean::cnstr_set(x_76, 1, x_53);
lean::cnstr_set(x_76, 2, x_62);
lean::cnstr_set(x_76, 3, x_68);
lean::cnstr_set(x_76, 4, x_71);
lean::cnstr_set(x_76, 5, x_72);
lean::cnstr_set(x_76, 6, x_74);
lean::cnstr_set(x_76, 7, x_43);
x_77 = lean_elaborator_elaborate_command(x_48, x_9, x_76);
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
lean::dec(x_77);
if (lean::obj_tag(x_78) == 0)
{
obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_3);
lean::dec(x_55);
x_85 = lean::cnstr_get(x_45, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_45, 1);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_45, 2);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_45, 3);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_45, 4);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_45, 5);
lean::inc(x_95);
x_97 = l_list_append___rarg(x_80, x_95);
x_98 = lean::cnstr_get(x_45, 6);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_45, 7);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_45, 8);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_45, 9);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_45, 10);
lean::inc(x_106);
lean::dec(x_45);
x_109 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_109, 0, x_85);
lean::cnstr_set(x_109, 1, x_87);
lean::cnstr_set(x_109, 2, x_89);
lean::cnstr_set(x_109, 3, x_91);
lean::cnstr_set(x_109, 4, x_93);
lean::cnstr_set(x_109, 5, x_97);
lean::cnstr_set(x_109, 6, x_98);
lean::cnstr_set(x_109, 7, x_100);
lean::cnstr_set(x_109, 8, x_102);
lean::cnstr_set(x_109, 9, x_104);
lean::cnstr_set(x_109, 10, x_106);
x_110 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_47;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_109);
if (lean::is_scalar(x_42)) {
 x_112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_112 = x_42;
}
lean::cnstr_set(x_112, 0, x_111);
return x_112;
}
else
{
obj* x_114; obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_129; obj* x_130; obj* x_131; obj* x_133; obj* x_134; obj* x_135; obj* x_137; obj* x_138; obj* x_140; obj* x_143; obj* x_145; obj* x_146; obj* x_148; obj* x_150; obj* x_153; obj* x_155; obj* x_157; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_45);
x_114 = lean::cnstr_get(x_78, 0);
lean::inc(x_114);
lean::dec(x_78);
x_117 = lean::cnstr_get(x_3, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_3, 1);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_3, 2);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_3, 3);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_55, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_114, 2);
lean::inc(x_127);
x_129 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
x_130 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(x_129, x_127);
x_131 = lean::cnstr_get(x_114, 3);
lean::inc(x_131);
x_133 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1;
x_134 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(x_133, x_131);
x_135 = lean::cnstr_get(x_114, 4);
lean::inc(x_135);
x_137 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(x_135);
x_138 = lean::cnstr_get(x_55, 4);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_55, 5);
lean::inc(x_140);
lean::dec(x_55);
x_143 = lean::cnstr_get(x_114, 5);
lean::inc(x_143);
x_145 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_145, 0, x_125);
lean::cnstr_set(x_145, 1, x_130);
lean::cnstr_set(x_145, 2, x_134);
lean::cnstr_set(x_145, 3, x_137);
lean::cnstr_set(x_145, 4, x_138);
lean::cnstr_set(x_145, 5, x_140);
lean::cnstr_set(x_145, 6, x_143);
x_146 = lean::cnstr_get(x_3, 5);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_3, 6);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_3, 7);
lean::inc(x_150);
lean::dec(x_3);
x_153 = lean::cnstr_get(x_114, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_114, 1);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_114, 6);
lean::inc(x_157);
lean::dec(x_114);
x_160 = l_list_append___rarg(x_80, x_146);
x_161 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_161, 0, x_117);
lean::cnstr_set(x_161, 1, x_119);
lean::cnstr_set(x_161, 2, x_121);
lean::cnstr_set(x_161, 3, x_123);
lean::cnstr_set(x_161, 4, x_145);
lean::cnstr_set(x_161, 5, x_160);
lean::cnstr_set(x_161, 6, x_148);
lean::cnstr_set(x_161, 7, x_150);
lean::cnstr_set(x_161, 8, x_153);
lean::cnstr_set(x_161, 9, x_155);
lean::cnstr_set(x_161, 10, x_157);
x_162 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_163 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_163 = x_47;
}
lean::cnstr_set(x_163, 0, x_162);
lean::cnstr_set(x_163, 1, x_161);
if (lean::is_scalar(x_42)) {
 x_164 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_164 = x_42;
}
lean::cnstr_set(x_164, 0, x_163);
return x_164;
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
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_list_map___main___at_lean_elaborator_names__to__pexpr___spec__1(x_0);
x_2 = l_lean_elaborator_mk__eqns___closed__1;
x_3 = l_lean_expr_mk__capp(x_2, x_1);
return x_3;
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_23 = x_13;
} else {
 lean::inc(x_21);
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
x_26 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 lean::cnstr_set(x_21, 1, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_18)) {
 lean::cnstr_set(x_18, 0, lean::box(0));
 x_25 = x_18;
} else {
 lean::inc(x_23);
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
if (lean::is_exclusive(x_18)) {
 lean::cnstr_set(x_18, 0, lean::box(0));
 x_29 = x_18;
} else {
 lean::inc(x_27);
 lean::dec(x_18);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 0);
x_32 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_set(x_27, 0, lean::box(0));
 lean::cnstr_set(x_27, 1, lean::box(0));
 x_34 = x_27;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
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
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_6 = x_3;
} else {
 lean::inc(x_4);
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_15 = x_8;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
x_16 = l_lean_elaborator_mk__eqns___closed__1;
x_17 = l_lean_expr_mk__capp(x_16, x_11);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
if (lean::is_scalar(x_10)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_10;
}
lean::cnstr_set(x_19, 0, x_18);
return x_19;
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
x_17 = x_23;
goto lbl_18;
}
else
{
obj* x_25; 
lean::dec(x_19);
x_25 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
x_17 = x_25;
goto lbl_18;
}
}
}
else
{
obj* x_26; obj* x_29; 
x_26 = lean::cnstr_get(x_4, 0);
lean::inc(x_26);
lean::dec(x_4);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_29) == 0)
{
if (lean::obj_tag(x_6) == 0)
{
x_17 = x_3;
goto lbl_18;
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_6, 0);
lean::inc(x_32);
lean::dec(x_6);
if (lean::obj_tag(x_32) == 0)
{
obj* x_36; 
lean::dec(x_32);
x_36 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
x_17 = x_36;
goto lbl_18;
}
else
{
obj* x_38; 
lean::dec(x_32);
x_38 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
x_17 = x_38;
goto lbl_18;
}
}
}
else
{
obj* x_39; obj* x_42; obj* x_45; obj* x_46; 
x_39 = lean::cnstr_get(x_29, 0);
lean::inc(x_39);
lean::dec(x_29);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
x_45 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
x_46 = l_lean_kvmap_set__string(x_3, x_45, x_42);
if (lean::obj_tag(x_6) == 0)
{
x_17 = x_46;
goto lbl_18;
}
else
{
obj* x_47; 
x_47 = lean::cnstr_get(x_6, 0);
lean::inc(x_47);
lean::dec(x_6);
if (lean::obj_tag(x_47) == 0)
{
obj* x_51; uint8 x_52; obj* x_53; 
lean::dec(x_47);
x_51 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
x_52 = 1;
x_53 = l_lean_kvmap_set__bool(x_46, x_51, x_52);
x_17 = x_53;
goto lbl_18;
}
else
{
obj* x_55; uint8 x_56; obj* x_57; 
lean::dec(x_47);
x_55 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
x_56 = 1;
x_57 = l_lean_kvmap_set__bool(x_46, x_55, x_56);
x_17 = x_57;
goto lbl_18;
}
}
}
}
lbl_18:
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
x_59 = l_lean_kvmap_set__bool(x_17, x_58, x_10);
x_60 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
x_61 = l_lean_kvmap_set__bool(x_59, x_60, x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_62; 
x_62 = l_lean_elaborator_attrs__to__pexpr(x_3, x_1, x_2);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_61);
x_64 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_set(x_62, 0, lean::box(0));
 x_66 = x_62;
} else {
 lean::inc(x_64);
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
obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_68 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_set(x_62, 0, lean::box(0));
 x_70 = x_62;
} else {
 lean::inc(x_68);
 lean::dec(x_62);
 x_70 = lean::box(0);
}
x_71 = lean::cnstr_get(x_68, 0);
x_73 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_set(x_68, 0, lean::box(0));
 lean::cnstr_set(x_68, 1, lean::box(0));
 x_75 = x_68;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_68);
 x_75 = lean::box(0);
}
x_76 = lean_expr_mk_mdata(x_61, x_71);
if (lean::is_scalar(x_75)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_75;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_73);
if (lean::is_scalar(x_70)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_70;
}
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
}
else
{
obj* x_79; obj* x_82; obj* x_85; 
x_79 = lean::cnstr_get(x_14, 0);
lean::inc(x_79);
lean::dec(x_14);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
x_85 = l_lean_elaborator_attrs__to__pexpr(x_82, x_1, x_2);
if (lean::obj_tag(x_85) == 0)
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_61);
x_87 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_set(x_85, 0, lean::box(0));
 x_89 = x_85;
} else {
 lean::inc(x_87);
 lean::dec(x_85);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
return x_90;
}
else
{
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_91 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_set(x_85, 0, lean::box(0));
 x_93 = x_85;
} else {
 lean::inc(x_91);
 lean::dec(x_85);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_91, 0);
x_96 = lean::cnstr_get(x_91, 1);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_set(x_91, 0, lean::box(0));
 lean::cnstr_set(x_91, 1, lean::box(0));
 x_98 = x_91;
} else {
 lean::inc(x_94);
 lean::inc(x_96);
 lean::dec(x_91);
 x_98 = lean::box(0);
}
x_99 = lean_expr_mk_mdata(x_61, x_94);
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_96);
if (lean::is_scalar(x_93)) {
 x_101 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_101 = x_93;
}
lean::cnstr_set(x_101, 0, x_100);
return x_101;
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
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
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
x_17 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_16, x_14);
lean::inc(x_3);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg___lambda__4), 4, 3);
lean::closure_set(x_19, 0, x_1);
lean::closure_set(x_19, 1, x_3);
lean::closure_set(x_19, 2, x_2);
x_20 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_17, x_19);
return x_20;
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_0);
 x_11 = lean::box(0);
}
x_12 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_7);
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
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
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_33 = x_24;
} else {
 lean::inc(x_31);
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
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_37 = x_24;
} else {
 lean::inc(x_35);
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
obj* x_53; obj* x_56; obj* x_58; obj* x_61; uint8 x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
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
lean::inc(x_61);
x_64 = lean_expr_local(x_61, x_61, x_38, x_62);
if (lean::is_scalar(x_11)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_11;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_56);
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_58);
if (lean::is_scalar(x_37)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_37;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
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
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_6 = x_3;
} else {
 lean::inc(x_4);
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_15 = x_8;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
x_16 = l_lean_elaborator_mk__eqns___closed__1;
x_17 = l_lean_expr_mk__capp(x_16, x_11);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
if (lean::is_scalar(x_10)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_10;
}
lean::cnstr_set(x_19, 0, x_18);
return x_19;
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_23 = x_13;
} else {
 lean::inc(x_21);
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
x_26 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 lean::cnstr_set(x_21, 1, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
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
if (lean::is_exclusive(x_17)) {
 lean::cnstr_set(x_17, 0, lean::box(0));
 x_25 = x_17;
} else {
 lean::inc(x_23);
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
if (lean::is_exclusive(x_17)) {
 lean::cnstr_set(x_17, 0, lean::box(0));
 x_29 = x_17;
} else {
 lean::inc(x_27);
 lean::dec(x_17);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 0);
x_32 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_set(x_27, 0, lean::box(0));
 lean::cnstr_set(x_27, 1, lean::box(0));
 x_34 = x_27;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
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
x_58 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_set(x_50, 0, lean::box(0));
 lean::cnstr_set(x_50, 1, lean::box(0));
 x_60 = x_50;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
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
x_77 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_set(x_72, 0, lean::box(0));
 lean::cnstr_set(x_72, 1, lean::box(0));
 x_79 = x_72;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
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
obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_17);
lean::dec(x_15);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
x_27 = l_lean_elaborator_elab__def__like___closed__1;
x_28 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_27, x_4, x_5);
return x_28;
}
else
{
obj* x_29; obj* x_33; 
x_29 = lean::cnstr_get(x_15, 0);
lean::inc(x_29);
lean::dec(x_15);
lean::inc(x_4);
x_33 = l_lean_elaborator_decl__modifiers__to__pexpr(x_1, x_4, x_5);
if (lean::obj_tag(x_33) == 0)
{
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_12);
lean::dec(x_17);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_29);
x_42 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_set(x_33, 0, lean::box(0));
 x_44 = x_33;
} else {
 lean::inc(x_42);
 lean::dec(x_33);
 x_44 = lean::box(0);
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
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_46 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_set(x_33, 0, lean::box(0));
 x_48 = x_33;
} else {
 lean::inc(x_46);
 lean::dec(x_33);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_46, 0);
x_51 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_set(x_46, 0, lean::box(0));
 lean::cnstr_set(x_46, 1, lean::box(0));
 x_53 = x_46;
} else {
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_46);
 x_53 = lean::box(0);
}
x_54 = lean::box(0);
x_55 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_55, 0, x_3);
x_56 = lean_expr_mk_lit(x_55);
if (lean::obj_tag(x_6) == 0)
{
obj* x_60; obj* x_62; 
x_60 = l_lean_expander_get__opt__type___main(x_17);
lean::inc(x_4);
x_62 = l_lean_elaborator_to__pexpr___main(x_60, x_4, x_51);
if (lean::obj_tag(x_6) == 0)
{
if (lean::obj_tag(x_62) == 0)
{
obj* x_72; obj* x_74; obj* x_75; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_29);
lean::dec(x_48);
lean::dec(x_53);
lean::dec(x_56);
x_72 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_set(x_62, 0, lean::box(0));
 x_74 = x_62;
} else {
 lean::inc(x_72);
 lean::dec(x_62);
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
obj* x_76; 
x_76 = lean::cnstr_get(x_62, 0);
lean::inc(x_76);
lean::dec(x_62);
x_57 = x_54;
x_58 = x_76;
goto lbl_59;
}
}
else
{
obj* x_79; 
x_79 = lean::cnstr_get(x_6, 0);
lean::inc(x_79);
lean::dec(x_6);
if (lean::obj_tag(x_62) == 0)
{
obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_79);
lean::dec(x_49);
lean::dec(x_29);
lean::dec(x_48);
lean::dec(x_53);
lean::dec(x_56);
x_92 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_set(x_62, 0, lean::box(0));
 x_94 = x_62;
} else {
 lean::inc(x_92);
 lean::dec(x_62);
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
obj* x_96; obj* x_99; obj* x_102; 
x_96 = lean::cnstr_get(x_62, 0);
lean::inc(x_96);
lean::dec(x_62);
x_99 = lean::cnstr_get(x_79, 1);
lean::inc(x_99);
lean::dec(x_79);
x_102 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(x_99);
x_57 = x_102;
x_58 = x_96;
goto lbl_59;
}
}
}
else
{
obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_123; obj* x_124; obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_136; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_147; obj* x_150; obj* x_151; obj* x_153; 
x_103 = lean::cnstr_get(x_6, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_51, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_51, 1);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_51, 2);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_51, 3);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_51, 4);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_113, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_113, 1);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_103, 1);
lean::inc(x_119);
lean::dec(x_103);
lean::inc(x_119);
x_123 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(x_119);
x_124 = l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(x_117, x_123);
x_125 = lean::cnstr_get(x_113, 2);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_113, 3);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_113, 4);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_113, 5);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_113, 6);
lean::inc(x_133);
lean::dec(x_113);
x_136 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_136, 0, x_115);
lean::cnstr_set(x_136, 1, x_124);
lean::cnstr_set(x_136, 2, x_125);
lean::cnstr_set(x_136, 3, x_127);
lean::cnstr_set(x_136, 4, x_129);
lean::cnstr_set(x_136, 5, x_131);
lean::cnstr_set(x_136, 6, x_133);
x_137 = lean::cnstr_get(x_51, 5);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_51, 6);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_51, 7);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_51, 8);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_51, 9);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_51, 10);
lean::inc(x_147);
lean::dec(x_51);
x_150 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_150, 0, x_105);
lean::cnstr_set(x_150, 1, x_107);
lean::cnstr_set(x_150, 2, x_109);
lean::cnstr_set(x_150, 3, x_111);
lean::cnstr_set(x_150, 4, x_136);
lean::cnstr_set(x_150, 5, x_137);
lean::cnstr_set(x_150, 6, x_139);
lean::cnstr_set(x_150, 7, x_141);
lean::cnstr_set(x_150, 8, x_143);
lean::cnstr_set(x_150, 9, x_145);
lean::cnstr_set(x_150, 10, x_147);
x_151 = l_lean_expander_get__opt__type___main(x_17);
lean::inc(x_4);
x_153 = l_lean_elaborator_to__pexpr___main(x_151, x_4, x_150);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_119);
if (lean::obj_tag(x_153) == 0)
{
obj* x_164; obj* x_166; obj* x_167; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_29);
lean::dec(x_48);
lean::dec(x_53);
lean::dec(x_56);
x_164 = lean::cnstr_get(x_153, 0);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_set(x_153, 0, lean::box(0));
 x_166 = x_153;
} else {
 lean::inc(x_164);
 lean::dec(x_153);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_164);
return x_167;
}
else
{
obj* x_168; 
x_168 = lean::cnstr_get(x_153, 0);
lean::inc(x_168);
lean::dec(x_153);
x_57 = x_54;
x_58 = x_168;
goto lbl_59;
}
}
else
{
lean::dec(x_6);
if (lean::obj_tag(x_153) == 0)
{
obj* x_182; obj* x_184; obj* x_185; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_29);
lean::dec(x_48);
lean::dec(x_53);
lean::dec(x_56);
lean::dec(x_119);
x_182 = lean::cnstr_get(x_153, 0);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_set(x_153, 0, lean::box(0));
 x_184 = x_153;
} else {
 lean::inc(x_182);
 lean::dec(x_153);
 x_184 = lean::box(0);
}
if (lean::is_scalar(x_184)) {
 x_185 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_185 = x_184;
}
lean::cnstr_set(x_185, 0, x_182);
return x_185;
}
else
{
obj* x_186; obj* x_189; 
x_186 = lean::cnstr_get(x_153, 0);
lean::inc(x_186);
lean::dec(x_153);
x_189 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(x_119);
x_57 = x_189;
x_58 = x_186;
goto lbl_59;
}
}
}
lbl_59:
{
obj* x_190; obj* x_192; obj* x_195; obj* x_196; obj* x_198; uint8 x_199; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; 
x_190 = lean::cnstr_get(x_58, 0);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_58, 1);
lean::inc(x_192);
lean::dec(x_58);
x_195 = l_lean_elaborator_names__to__pexpr(x_57);
x_196 = lean::cnstr_get(x_8, 0);
lean::inc(x_196);
x_198 = l_lean_elaborator_mangle__ident(x_196);
x_199 = 4;
lean::inc(x_190);
lean::inc(x_198);
x_202 = lean_expr_local(x_198, x_198, x_190, x_199);
x_203 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_203, 0, x_202);
lean::cnstr_set(x_203, 1, x_54);
x_204 = l_lean_elaborator_mk__eqns___closed__1;
x_205 = l_lean_expr_mk__capp(x_204, x_203);
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_211; obj* x_214; obj* x_218; 
lean::dec(x_190);
lean::dec(x_8);
lean::dec(x_53);
x_211 = lean::cnstr_get(x_12, 0);
lean::inc(x_211);
lean::dec(x_12);
x_214 = lean::cnstr_get(x_211, 1);
lean::inc(x_214);
lean::dec(x_211);
lean::inc(x_4);
x_218 = l_lean_elaborator_to__pexpr___main(x_214, x_4, x_192);
if (lean::obj_tag(x_218) == 0)
{
obj* x_227; obj* x_229; obj* x_230; 
lean::dec(x_205);
lean::dec(x_195);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_29);
lean::dec(x_48);
lean::dec(x_56);
x_227 = lean::cnstr_get(x_218, 0);
if (lean::is_exclusive(x_218)) {
 lean::cnstr_set(x_218, 0, lean::box(0));
 x_229 = x_218;
} else {
 lean::inc(x_227);
 lean::dec(x_218);
 x_229 = lean::box(0);
}
if (lean::is_scalar(x_229)) {
 x_230 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_230 = x_229;
}
lean::cnstr_set(x_230, 0, x_227);
return x_230;
}
else
{
obj* x_231; 
x_231 = lean::cnstr_get(x_218, 0);
lean::inc(x_231);
lean::dec(x_218);
x_206 = x_231;
goto lbl_207;
}
}
case 1:
{
obj* x_236; obj* x_237; 
lean::dec(x_12);
lean::dec(x_8);
x_236 = l_lean_elaborator_mk__eqns(x_190, x_54);
if (lean::is_scalar(x_53)) {
 x_237 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_237 = x_53;
}
lean::cnstr_set(x_237, 0, x_236);
lean::cnstr_set(x_237, 1, x_192);
x_206 = x_237;
goto lbl_207;
}
default:
{
obj* x_238; obj* x_242; 
x_238 = lean::cnstr_get(x_12, 0);
lean::inc(x_238);
lean::dec(x_12);
lean::inc(x_4);
x_242 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_8, x_238, x_4, x_192);
if (lean::obj_tag(x_242) == 0)
{
obj* x_253; obj* x_255; obj* x_256; 
lean::dec(x_190);
lean::dec(x_205);
lean::dec(x_195);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_49);
lean::dec(x_29);
lean::dec(x_48);
lean::dec(x_53);
lean::dec(x_56);
x_253 = lean::cnstr_get(x_242, 0);
if (lean::is_exclusive(x_242)) {
 lean::cnstr_set(x_242, 0, lean::box(0));
 x_255 = x_242;
} else {
 lean::inc(x_253);
 lean::dec(x_242);
 x_255 = lean::box(0);
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_253);
return x_256;
}
else
{
obj* x_257; obj* x_260; obj* x_262; obj* x_265; obj* x_266; 
x_257 = lean::cnstr_get(x_242, 0);
lean::inc(x_257);
lean::dec(x_242);
x_260 = lean::cnstr_get(x_257, 0);
lean::inc(x_260);
x_262 = lean::cnstr_get(x_257, 1);
lean::inc(x_262);
lean::dec(x_257);
x_265 = l_lean_elaborator_mk__eqns(x_190, x_260);
if (lean::is_scalar(x_53)) {
 x_266 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_266 = x_53;
}
lean::cnstr_set(x_266, 0, x_265);
lean::cnstr_set(x_266, 1, x_262);
x_206 = x_266;
goto lbl_207;
}
}
}
lbl_207:
{
obj* x_267; obj* x_269; obj* x_273; 
x_267 = lean::cnstr_get(x_206, 0);
lean::inc(x_267);
x_269 = lean::cnstr_get(x_206, 1);
lean::inc(x_269);
lean::dec(x_206);
lean::inc(x_4);
x_273 = l_lean_elaborator_simple__binders__to__pexpr(x_29, x_4, x_269);
if (lean::obj_tag(x_273) == 0)
{
obj* x_281; obj* x_284; 
lean::dec(x_205);
lean::dec(x_195);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_267);
lean::dec(x_49);
lean::dec(x_56);
x_281 = lean::cnstr_get(x_273, 0);
lean::inc(x_281);
lean::dec(x_273);
if (lean::is_scalar(x_48)) {
 x_284 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_284 = x_48;
 lean::cnstr_set_tag(x_48, 0);
}
lean::cnstr_set(x_284, 0, x_281);
return x_284;
}
else
{
obj* x_286; obj* x_289; obj* x_291; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
lean::dec(x_48);
x_286 = lean::cnstr_get(x_273, 0);
lean::inc(x_286);
lean::dec(x_273);
x_289 = lean::cnstr_get(x_286, 0);
lean::inc(x_289);
x_291 = lean::cnstr_get(x_286, 1);
lean::inc(x_291);
lean::dec(x_286);
x_294 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_294, 0, x_267);
lean::cnstr_set(x_294, 1, x_54);
x_295 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_295, 0, x_289);
lean::cnstr_set(x_295, 1, x_294);
x_296 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_296, 0, x_205);
lean::cnstr_set(x_296, 1, x_295);
x_297 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_297, 0, x_195);
lean::cnstr_set(x_297, 1, x_296);
x_298 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_298, 0, x_56);
lean::cnstr_set(x_298, 1, x_297);
x_299 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_299, 0, x_49);
lean::cnstr_set(x_299, 1, x_298);
x_300 = l_lean_expr_mk__capp(x_204, x_299);
x_301 = l_lean_elaborator_elab__def__like___closed__2;
x_302 = lean_expr_mk_mdata(x_301, x_300);
x_303 = l_lean_elaborator_old__elab__command(x_0, x_302, x_4, x_291);
return x_303;
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
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = l_lean_elaborator_infer__mod__to__pexpr___closed__2;
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = l_lean_elaborator_infer__mod__to__pexpr___closed__3;
return x_8;
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
x_16 = lean::cnstr_get(x_9, 3);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
if (lean::obj_tag(x_18) == 0)
{
obj* x_26; obj* x_29; 
lean::dec(x_9);
lean::dec(x_18);
lean::dec(x_20);
x_26 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_0);
x_29 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_26, x_2, x_3);
if (lean::obj_tag(x_29) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_34 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_set(x_29, 0, lean::box(0));
 x_36 = x_29;
} else {
 lean::inc(x_34);
 lean::dec(x_29);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
return x_37;
}
else
{
obj* x_38; 
x_38 = lean::cnstr_get(x_29, 0);
lean::inc(x_38);
lean::dec(x_29);
x_14 = x_38;
goto lbl_15;
}
}
else
{
obj* x_41; 
x_41 = lean::cnstr_get(x_18, 0);
lean::inc(x_41);
lean::dec(x_18);
if (lean::obj_tag(x_41) == 0)
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_45; obj* x_48; 
lean::dec(x_9);
x_45 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_0);
x_48 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_45, x_2, x_3);
if (lean::obj_tag(x_48) == 0)
{
obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_53 = lean::cnstr_get(x_48, 0);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_set(x_48, 0, lean::box(0));
 x_55 = x_48;
} else {
 lean::inc(x_53);
 lean::dec(x_48);
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
obj* x_57; 
x_57 = lean::cnstr_get(x_48, 0);
lean::inc(x_57);
lean::dec(x_48);
x_14 = x_57;
goto lbl_15;
}
}
else
{
obj* x_60; obj* x_63; obj* x_67; 
x_60 = lean::cnstr_get(x_20, 0);
lean::inc(x_60);
lean::dec(x_20);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
lean::inc(x_2);
x_67 = l_lean_elaborator_to__pexpr___main(x_63, x_2, x_3);
if (lean::obj_tag(x_67) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_73 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_set(x_67, 0, lean::box(0));
 x_75 = x_67;
} else {
 lean::inc(x_73);
 lean::dec(x_67);
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
obj* x_77; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_88; uint8 x_89; obj* x_91; obj* x_92; 
x_77 = lean::cnstr_get(x_67, 0);
lean::inc(x_77);
lean::dec(x_67);
x_80 = lean::cnstr_get(x_77, 0);
x_82 = lean::cnstr_get(x_77, 1);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_set(x_77, 0, lean::box(0));
 lean::cnstr_set(x_77, 1, lean::box(0));
 x_84 = x_77;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_77);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_9, 1);
lean::inc(x_85);
lean::dec(x_9);
x_88 = l_lean_elaborator_mangle__ident(x_85);
x_89 = 0;
lean::inc(x_88);
x_91 = lean_expr_local(x_88, x_88, x_80, x_89);
if (lean::is_scalar(x_84)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_84;
}
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_82);
x_14 = x_92;
goto lbl_15;
}
}
}
else
{
obj* x_96; obj* x_99; 
lean::dec(x_9);
lean::dec(x_41);
lean::dec(x_20);
x_96 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_0);
x_99 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_96, x_2, x_3);
if (lean::obj_tag(x_99) == 0)
{
obj* x_104; obj* x_106; obj* x_107; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_104 = lean::cnstr_get(x_99, 0);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_set(x_99, 0, lean::box(0));
 x_106 = x_99;
} else {
 lean::inc(x_104);
 lean::dec(x_99);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_104);
return x_107;
}
else
{
obj* x_108; 
x_108 = lean::cnstr_get(x_99, 0);
lean::inc(x_108);
lean::dec(x_99);
x_14 = x_108;
goto lbl_15;
}
}
}
lbl_15:
{
obj* x_111; obj* x_113; obj* x_115; obj* x_116; 
x_111 = lean::cnstr_get(x_14, 0);
x_113 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_set(x_14, 1, lean::box(0));
 x_115 = x_14;
} else {
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_14);
 x_115 = lean::box(0);
}
x_116 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_11, x_2, x_113);
if (lean::obj_tag(x_116) == 0)
{
obj* x_120; obj* x_122; obj* x_123; 
lean::dec(x_13);
lean::dec(x_111);
lean::dec(x_115);
x_120 = lean::cnstr_get(x_116, 0);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_set(x_116, 0, lean::box(0));
 x_122 = x_116;
} else {
 lean::inc(x_120);
 lean::dec(x_116);
 x_122 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_120);
return x_123;
}
else
{
obj* x_124; obj* x_126; obj* x_127; obj* x_129; obj* x_132; obj* x_133; obj* x_134; 
x_124 = lean::cnstr_get(x_116, 0);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_set(x_116, 0, lean::box(0));
 x_126 = x_116;
} else {
 lean::inc(x_124);
 lean::dec(x_116);
 x_126 = lean::box(0);
}
x_127 = lean::cnstr_get(x_124, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_124, 1);
lean::inc(x_129);
lean::dec(x_124);
if (lean::is_scalar(x_13)) {
 x_132 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_132 = x_13;
}
lean::cnstr_set(x_132, 0, x_111);
lean::cnstr_set(x_132, 1, x_127);
if (lean::is_scalar(x_115)) {
 x_133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_133 = x_115;
}
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_129);
if (lean::is_scalar(x_126)) {
 x_134 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_134 = x_126;
}
lean::cnstr_set(x_134, 0, x_133);
return x_134;
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_22 = x_16;
} else {
 lean::inc(x_20);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_26 = x_16;
} else {
 lean::inc(x_24);
 lean::dec(x_16);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
x_29 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 lean::cnstr_set(x_24, 1, lean::box(0));
 x_31 = x_24;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
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
obj* x_23; obj* x_26; 
lean::dec(x_19);
x_23 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_0);
x_26 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_23, x_2, x_3);
if (lean::obj_tag(x_26) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_set(x_26, 0, lean::box(0));
 x_33 = x_26;
} else {
 lean::inc(x_31);
 lean::dec(x_26);
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
obj* x_35; 
x_35 = lean::cnstr_get(x_26, 0);
lean::inc(x_35);
lean::dec(x_26);
x_14 = x_35;
goto lbl_15;
}
}
else
{
obj* x_38; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; 
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
lean::dec(x_19);
x_41 = 0;
x_42 = lean::box(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_38);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_3);
x_14 = x_44;
goto lbl_15;
}
}
case 1:
{
obj* x_45; obj* x_48; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; 
x_45 = lean::cnstr_get(x_9, 0);
lean::inc(x_45);
lean::dec(x_9);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
x_51 = 1;
x_52 = lean::box(x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_48);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_3);
x_14 = x_54;
goto lbl_15;
}
case 2:
{
obj* x_55; obj* x_58; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; 
x_55 = lean::cnstr_get(x_9, 0);
lean::inc(x_55);
lean::dec(x_9);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
x_61 = 2;
x_62 = lean::box(x_61);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_58);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_3);
x_14 = x_64;
goto lbl_15;
}
default:
{
obj* x_65; obj* x_68; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; 
x_65 = lean::cnstr_get(x_9, 0);
lean::inc(x_65);
lean::dec(x_9);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
lean::dec(x_65);
x_71 = 3;
x_72 = lean::box(x_71);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_68);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_3);
x_14 = x_74;
goto lbl_15;
}
}
lbl_15:
{
obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_85; obj* x_87; obj* x_90; obj* x_92; 
x_75 = lean::cnstr_get(x_14, 0);
x_77 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_set(x_14, 1, lean::box(0));
 x_79 = x_14;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::dec(x_14);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_75, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_75, 1);
lean::inc(x_82);
lean::dec(x_75);
x_85 = lean::cnstr_get(x_82, 2);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_85, 1);
lean::inc(x_87);
lean::dec(x_85);
x_90 = l_lean_expander_get__opt__type___main(x_87);
lean::inc(x_2);
x_92 = l_lean_elaborator_to__pexpr___main(x_90, x_2, x_77);
if (lean::obj_tag(x_92) == 0)
{
obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_82);
lean::dec(x_80);
lean::dec(x_79);
x_100 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_set(x_92, 0, lean::box(0));
 x_102 = x_92;
} else {
 lean::inc(x_100);
 lean::dec(x_92);
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
obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_112; 
x_104 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_set(x_92, 0, lean::box(0));
 x_106 = x_92;
} else {
 lean::inc(x_104);
 lean::dec(x_92);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_104, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_104, 1);
lean::inc(x_109);
lean::dec(x_104);
x_112 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_11, x_2, x_109);
if (lean::obj_tag(x_112) == 0)
{
obj* x_118; obj* x_121; 
lean::dec(x_13);
lean::dec(x_82);
lean::dec(x_80);
lean::dec(x_79);
lean::dec(x_107);
x_118 = lean::cnstr_get(x_112, 0);
lean::inc(x_118);
lean::dec(x_112);
if (lean::is_scalar(x_106)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_106;
 lean::cnstr_set_tag(x_106, 0);
}
lean::cnstr_set(x_121, 0, x_118);
return x_121;
}
else
{
obj* x_122; obj* x_125; obj* x_127; obj* x_130; obj* x_131; uint8 x_132; obj* x_133; obj* x_134; obj* x_136; obj* x_137; obj* x_138; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_122 = lean::cnstr_get(x_112, 0);
lean::inc(x_122);
lean::dec(x_112);
x_125 = lean::cnstr_get(x_122, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_122, 1);
lean::inc(x_127);
lean::dec(x_122);
x_130 = l_lean_elaborator_mk__eqns___closed__1;
x_131 = l_lean_elaborator_dummy;
x_132 = lean::unbox(x_80);
x_133 = lean_expr_local(x_130, x_130, x_131, x_132);
x_134 = lean::cnstr_get(x_82, 0);
lean::inc(x_134);
x_136 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(x_134);
x_137 = l_lean_elaborator_names__to__pexpr(x_136);
x_138 = lean::cnstr_get(x_82, 1);
lean::inc(x_138);
lean::dec(x_82);
x_141 = l_lean_elaborator_infer__mod__to__pexpr(x_138);
x_142 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_143 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_143 = x_13;
}
lean::cnstr_set(x_143, 0, x_107);
lean::cnstr_set(x_143, 1, x_142);
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_141);
lean::cnstr_set(x_144, 1, x_143);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_137);
lean::cnstr_set(x_145, 1, x_144);
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_133);
lean::cnstr_set(x_146, 1, x_145);
x_147 = l_lean_expr_mk__capp(x_130, x_146);
x_148 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_125);
if (lean::is_scalar(x_79)) {
 x_149 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_149 = x_79;
}
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_127);
if (lean::is_scalar(x_106)) {
 x_150 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_150 = x_106;
}
lean::cnstr_set(x_150, 0, x_149);
return x_150;
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 4);
lean::inc(x_3);
x_7 = l_lean_parser_command_declaration_has__view;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
lean::inc(x_0);
x_12 = lean::apply_1(x_8, x_0);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
switch (lean::obj_tag(x_13)) {
case 0:
{
obj* x_15; obj* x_18; obj* x_20; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_12, 0);
lean::inc(x_20);
lean::dec(x_12);
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_24; obj* x_25; 
lean::dec(x_18);
x_24 = lean::mk_nat_obj(1u);
x_25 = l_lean_elaborator_elab__def__like(x_0, x_20, x_15, x_24, x_1, x_2);
x_5 = x_25;
goto lbl_6;
}
case 1:
{
obj* x_27; obj* x_28; 
lean::dec(x_18);
x_27 = lean::mk_nat_obj(5u);
x_28 = l_lean_elaborator_elab__def__like(x_0, x_20, x_15, x_27, x_1, x_2);
x_5 = x_28;
goto lbl_6;
}
default:
{
obj* x_30; obj* x_31; 
lean::dec(x_18);
x_30 = lean::mk_nat_obj(0u);
x_31 = l_lean_elaborator_elab__def__like(x_0, x_20, x_15, x_30, x_1, x_2);
x_5 = x_31;
goto lbl_6;
}
}
}
case 1:
{
obj* x_32; obj* x_35; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_32 = lean::cnstr_get(x_13, 0);
lean::inc(x_32);
lean::dec(x_13);
x_35 = lean::cnstr_get(x_12, 0);
lean::inc(x_35);
lean::dec(x_12);
x_38 = lean::box(0);
x_39 = lean::cnstr_get(x_32, 1);
lean::inc(x_39);
x_41 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
x_42 = l_option_get__or__else___main___rarg(x_39, x_41);
x_43 = lean::cnstr_get(x_32, 2);
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
x_52 = lean::cnstr_get(x_32, 3);
lean::inc(x_52);
lean::dec(x_32);
x_55 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
x_56 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_38);
lean::cnstr_set(x_56, 2, x_42);
lean::cnstr_set(x_56, 3, x_51);
lean::cnstr_set(x_56, 4, x_52);
x_57 = lean::mk_nat_obj(3u);
x_58 = l_lean_elaborator_elab__def__like(x_0, x_35, x_56, x_57, x_1, x_2);
x_5 = x_58;
goto lbl_6;
}
case 2:
{
obj* x_59; obj* x_62; obj* x_65; obj* x_66; obj* x_68; obj* x_70; obj* x_73; obj* x_74; obj* x_75; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_59 = lean::cnstr_get(x_13, 0);
lean::inc(x_59);
lean::dec(x_13);
x_62 = lean::cnstr_get(x_12, 0);
lean::inc(x_62);
lean::dec(x_12);
x_65 = lean::box(0);
x_66 = lean::cnstr_get(x_59, 1);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_66, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_66, 1);
lean::inc(x_70);
lean::dec(x_66);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_70);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_68);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::cnstr_get(x_59, 2);
lean::inc(x_75);
lean::dec(x_59);
x_78 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
x_79 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
x_80 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_65);
lean::cnstr_set(x_80, 2, x_79);
lean::cnstr_set(x_80, 3, x_74);
lean::cnstr_set(x_80, 4, x_75);
x_81 = lean::mk_nat_obj(2u);
x_82 = l_lean_elaborator_elab__def__like(x_0, x_62, x_80, x_81, x_1, x_2);
x_5 = x_82;
goto lbl_6;
}
case 3:
{
obj* x_83; obj* x_86; obj* x_88; obj* x_91; obj* x_93; 
x_83 = lean::cnstr_get(x_13, 0);
lean::inc(x_83);
lean::dec(x_13);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_83, 2);
lean::inc(x_88);
lean::dec(x_83);
x_91 = lean::cnstr_get(x_88, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
if (lean::obj_tag(x_91) == 0)
{
obj* x_100; obj* x_101; 
lean::dec(x_12);
lean::dec(x_93);
lean::dec(x_91);
lean::dec(x_86);
x_100 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_101 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_100, x_1, x_2);
x_5 = x_101;
goto lbl_6;
}
else
{
obj* x_102; 
x_102 = lean::cnstr_get(x_91, 0);
lean::inc(x_102);
lean::dec(x_91);
if (lean::obj_tag(x_102) == 0)
{
obj* x_105; obj* x_109; 
x_105 = lean::cnstr_get(x_12, 0);
lean::inc(x_105);
lean::dec(x_12);
lean::inc(x_1);
x_109 = l_lean_elaborator_decl__modifiers__to__pexpr(x_105, x_1, x_2);
if (lean::obj_tag(x_109) == 0)
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_93);
lean::dec(x_86);
x_114 = lean::cnstr_get(x_109, 0);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_set(x_109, 0, lean::box(0));
 x_116 = x_109;
} else {
 lean::inc(x_114);
 lean::dec(x_109);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_114);
x_5 = x_117;
goto lbl_6;
}
else
{
obj* x_118; obj* x_120; obj* x_121; obj* x_123; obj* x_126; obj* x_130; 
x_118 = lean::cnstr_get(x_109, 0);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_set(x_109, 0, lean::box(0));
 x_120 = x_109;
} else {
 lean::inc(x_118);
 lean::dec(x_109);
 x_120 = lean::box(0);
}
x_121 = lean::cnstr_get(x_118, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_118, 1);
lean::inc(x_123);
lean::dec(x_118);
x_126 = lean::cnstr_get(x_93, 1);
lean::inc(x_126);
lean::dec(x_93);
lean::inc(x_1);
x_130 = l_lean_elaborator_to__pexpr___main(x_126, x_1, x_123);
if (lean::obj_tag(x_130) == 0)
{
obj* x_135; obj* x_138; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_86);
lean::dec(x_121);
x_135 = lean::cnstr_get(x_130, 0);
lean::inc(x_135);
lean::dec(x_130);
if (lean::is_scalar(x_120)) {
 x_138 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_138 = x_120;
 lean::cnstr_set_tag(x_120, 0);
}
lean::cnstr_set(x_138, 0, x_135);
x_5 = x_138;
goto lbl_6;
}
else
{
obj* x_140; obj* x_143; obj* x_145; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
lean::dec(x_120);
x_140 = lean::cnstr_get(x_130, 0);
lean::inc(x_140);
lean::dec(x_130);
x_143 = lean::cnstr_get(x_140, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_140, 1);
lean::inc(x_145);
lean::dec(x_140);
x_148 = lean::box(0);
x_149 = l_lean_elaborator_ident__univ__params__to__pexpr(x_86);
x_150 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_150, 0, x_143);
lean::cnstr_set(x_150, 1, x_148);
x_151 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_151, 0, x_149);
lean::cnstr_set(x_151, 1, x_150);
x_152 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_152, 0, x_121);
lean::cnstr_set(x_152, 1, x_151);
x_153 = l_lean_elaborator_mk__eqns___closed__1;
x_154 = l_lean_expr_mk__capp(x_153, x_152);
x_155 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3;
x_156 = lean_expr_mk_mdata(x_155, x_154);
x_157 = l_lean_elaborator_old__elab__command(x_0, x_156, x_1, x_145);
x_5 = x_157;
goto lbl_6;
}
}
}
else
{
obj* x_162; obj* x_163; 
lean::dec(x_12);
lean::dec(x_93);
lean::dec(x_86);
lean::dec(x_102);
x_162 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_163 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_162, x_1, x_2);
x_5 = x_163;
goto lbl_6;
}
}
}
case 4:
{
obj* x_164; obj* x_167; obj* x_169; obj* x_171; obj* x_173; obj* x_175; 
x_164 = lean::cnstr_get(x_13, 0);
lean::inc(x_164);
lean::dec(x_13);
x_167 = lean::cnstr_get(x_164, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_164, 2);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_164, 3);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_164, 4);
lean::inc(x_173);
x_175 = lean::cnstr_get(x_164, 6);
lean::inc(x_175);
lean::dec(x_164);
if (lean::obj_tag(x_167) == 0)
{
obj* x_178; obj* x_180; 
x_178 = lean::cnstr_get(x_173, 0);
lean::inc(x_178);
x_180 = lean::cnstr_get(x_173, 1);
lean::inc(x_180);
lean::dec(x_173);
if (lean::obj_tag(x_178) == 0)
{
obj* x_189; obj* x_190; 
lean::dec(x_175);
lean::dec(x_178);
lean::dec(x_180);
lean::dec(x_169);
lean::dec(x_171);
lean::dec(x_12);
x_189 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_190 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_189, x_1, x_2);
x_5 = x_190;
goto lbl_6;
}
else
{
obj* x_191; obj* x_194; obj* x_199; 
x_191 = lean::cnstr_get(x_178, 0);
lean::inc(x_191);
lean::dec(x_178);
x_194 = lean::cnstr_get(x_12, 0);
lean::inc(x_194);
lean::dec(x_12);
lean::inc(x_1);
lean::inc(x_194);
x_199 = l_lean_elaborator_decl__modifiers__to__pexpr(x_194, x_1, x_2);
if (lean::obj_tag(x_199) == 0)
{
obj* x_208; obj* x_210; obj* x_211; 
lean::dec(x_175);
lean::dec(x_194);
lean::dec(x_191);
lean::dec(x_180);
lean::dec(x_169);
lean::dec(x_171);
lean::dec(x_1);
lean::dec(x_0);
x_208 = lean::cnstr_get(x_199, 0);
if (lean::is_exclusive(x_199)) {
 lean::cnstr_set(x_199, 0, lean::box(0));
 x_210 = x_199;
} else {
 lean::inc(x_208);
 lean::dec(x_199);
 x_210 = lean::box(0);
}
if (lean::is_scalar(x_210)) {
 x_211 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_211 = x_210;
}
lean::cnstr_set(x_211, 0, x_208);
x_5 = x_211;
goto lbl_6;
}
else
{
obj* x_212; obj* x_214; obj* x_215; obj* x_217; obj* x_220; obj* x_221; obj* x_223; 
x_212 = lean::cnstr_get(x_199, 0);
if (lean::is_exclusive(x_199)) {
 lean::cnstr_set(x_199, 0, lean::box(0));
 x_214 = x_199;
} else {
 lean::inc(x_212);
 lean::dec(x_199);
 x_214 = lean::box(0);
}
x_215 = lean::cnstr_get(x_212, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_212, 1);
lean::inc(x_217);
lean::dec(x_212);
x_220 = lean::box(0);
x_223 = lean::cnstr_get(x_194, 1);
lean::inc(x_223);
lean::dec(x_194);
if (lean::obj_tag(x_223) == 0)
{
x_221 = x_220;
goto lbl_222;
}
else
{
obj* x_226; obj* x_229; 
x_226 = lean::cnstr_get(x_223, 0);
lean::inc(x_226);
lean::dec(x_223);
x_229 = lean::cnstr_get(x_226, 1);
lean::inc(x_229);
lean::dec(x_226);
x_221 = x_229;
goto lbl_222;
}
lbl_222:
{
obj* x_233; 
lean::inc(x_1);
x_233 = l_lean_elaborator_attrs__to__pexpr(x_221, x_1, x_217);
if (lean::obj_tag(x_233) == 0)
{
obj* x_242; obj* x_245; 
lean::dec(x_215);
lean::dec(x_175);
lean::dec(x_191);
lean::dec(x_180);
lean::dec(x_169);
lean::dec(x_171);
lean::dec(x_1);
lean::dec(x_0);
x_242 = lean::cnstr_get(x_233, 0);
lean::inc(x_242);
lean::dec(x_233);
if (lean::is_scalar(x_214)) {
 x_245 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_245 = x_214;
 lean::cnstr_set_tag(x_214, 0);
}
lean::cnstr_set(x_245, 0, x_242);
x_5 = x_245;
goto lbl_6;
}
else
{
obj* x_246; obj* x_248; obj* x_249; obj* x_251; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; 
x_246 = lean::cnstr_get(x_233, 0);
if (lean::is_exclusive(x_233)) {
 lean::cnstr_set(x_233, 0, lean::box(0));
 x_248 = x_233;
} else {
 lean::inc(x_246);
 lean::dec(x_233);
 x_248 = lean::box(0);
}
x_249 = lean::cnstr_get(x_246, 0);
lean::inc(x_249);
x_251 = lean::cnstr_get(x_246, 1);
lean::inc(x_251);
lean::dec(x_246);
x_254 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_254, 0, x_249);
lean::cnstr_set(x_254, 1, x_220);
x_255 = l_lean_elaborator_mk__eqns___closed__1;
x_256 = l_lean_expr_mk__capp(x_255, x_254);
if (lean::obj_tag(x_169) == 0)
{
obj* x_260; obj* x_262; 
x_260 = l_lean_expander_get__opt__type___main(x_180);
lean::inc(x_1);
x_262 = l_lean_elaborator_to__pexpr___main(x_260, x_1, x_251);
if (lean::obj_tag(x_169) == 0)
{
if (lean::obj_tag(x_262) == 0)
{
obj* x_271; obj* x_274; 
lean::dec(x_214);
lean::dec(x_215);
lean::dec(x_175);
lean::dec(x_191);
lean::dec(x_171);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_256);
x_271 = lean::cnstr_get(x_262, 0);
lean::inc(x_271);
lean::dec(x_262);
if (lean::is_scalar(x_248)) {
 x_274 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_274 = x_248;
 lean::cnstr_set_tag(x_248, 0);
}
lean::cnstr_set(x_274, 0, x_271);
x_5 = x_274;
goto lbl_6;
}
else
{
obj* x_276; 
lean::dec(x_248);
x_276 = lean::cnstr_get(x_262, 0);
lean::inc(x_276);
lean::dec(x_262);
x_257 = x_220;
x_258 = x_276;
goto lbl_259;
}
}
else
{
obj* x_279; 
x_279 = lean::cnstr_get(x_169, 0);
lean::inc(x_279);
lean::dec(x_169);
if (lean::obj_tag(x_262) == 0)
{
obj* x_291; obj* x_294; 
lean::dec(x_214);
lean::dec(x_215);
lean::dec(x_175);
lean::dec(x_191);
lean::dec(x_171);
lean::dec(x_279);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_256);
x_291 = lean::cnstr_get(x_262, 0);
lean::inc(x_291);
lean::dec(x_262);
if (lean::is_scalar(x_248)) {
 x_294 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_294 = x_248;
 lean::cnstr_set_tag(x_248, 0);
}
lean::cnstr_set(x_294, 0, x_291);
x_5 = x_294;
goto lbl_6;
}
else
{
obj* x_296; obj* x_299; obj* x_302; 
lean::dec(x_248);
x_296 = lean::cnstr_get(x_262, 0);
lean::inc(x_296);
lean::dec(x_262);
x_299 = lean::cnstr_get(x_279, 1);
lean::inc(x_299);
lean::dec(x_279);
x_302 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_299);
x_257 = x_302;
x_258 = x_296;
goto lbl_259;
}
}
}
else
{
obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_311; obj* x_313; obj* x_315; obj* x_317; obj* x_319; obj* x_323; obj* x_324; obj* x_325; obj* x_327; obj* x_329; obj* x_331; obj* x_333; obj* x_336; obj* x_337; obj* x_339; obj* x_341; obj* x_343; obj* x_345; obj* x_347; obj* x_350; obj* x_351; obj* x_353; 
x_303 = lean::cnstr_get(x_169, 0);
lean::inc(x_303);
x_305 = lean::cnstr_get(x_251, 0);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_251, 1);
lean::inc(x_307);
x_309 = lean::cnstr_get(x_251, 2);
lean::inc(x_309);
x_311 = lean::cnstr_get(x_251, 3);
lean::inc(x_311);
x_313 = lean::cnstr_get(x_251, 4);
lean::inc(x_313);
x_315 = lean::cnstr_get(x_313, 0);
lean::inc(x_315);
x_317 = lean::cnstr_get(x_313, 1);
lean::inc(x_317);
x_319 = lean::cnstr_get(x_303, 1);
lean::inc(x_319);
lean::dec(x_303);
lean::inc(x_319);
x_323 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(x_319);
x_324 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__5(x_317, x_323);
x_325 = lean::cnstr_get(x_313, 2);
lean::inc(x_325);
x_327 = lean::cnstr_get(x_313, 3);
lean::inc(x_327);
x_329 = lean::cnstr_get(x_313, 4);
lean::inc(x_329);
x_331 = lean::cnstr_get(x_313, 5);
lean::inc(x_331);
x_333 = lean::cnstr_get(x_313, 6);
lean::inc(x_333);
lean::dec(x_313);
x_336 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_336, 0, x_315);
lean::cnstr_set(x_336, 1, x_324);
lean::cnstr_set(x_336, 2, x_325);
lean::cnstr_set(x_336, 3, x_327);
lean::cnstr_set(x_336, 4, x_329);
lean::cnstr_set(x_336, 5, x_331);
lean::cnstr_set(x_336, 6, x_333);
x_337 = lean::cnstr_get(x_251, 5);
lean::inc(x_337);
x_339 = lean::cnstr_get(x_251, 6);
lean::inc(x_339);
x_341 = lean::cnstr_get(x_251, 7);
lean::inc(x_341);
x_343 = lean::cnstr_get(x_251, 8);
lean::inc(x_343);
x_345 = lean::cnstr_get(x_251, 9);
lean::inc(x_345);
x_347 = lean::cnstr_get(x_251, 10);
lean::inc(x_347);
lean::dec(x_251);
x_350 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_350, 0, x_305);
lean::cnstr_set(x_350, 1, x_307);
lean::cnstr_set(x_350, 2, x_309);
lean::cnstr_set(x_350, 3, x_311);
lean::cnstr_set(x_350, 4, x_336);
lean::cnstr_set(x_350, 5, x_337);
lean::cnstr_set(x_350, 6, x_339);
lean::cnstr_set(x_350, 7, x_341);
lean::cnstr_set(x_350, 8, x_343);
lean::cnstr_set(x_350, 9, x_345);
lean::cnstr_set(x_350, 10, x_347);
x_351 = l_lean_expander_get__opt__type___main(x_180);
lean::inc(x_1);
x_353 = l_lean_elaborator_to__pexpr___main(x_351, x_1, x_350);
if (lean::obj_tag(x_169) == 0)
{
lean::dec(x_319);
if (lean::obj_tag(x_353) == 0)
{
obj* x_363; obj* x_366; 
lean::dec(x_214);
lean::dec(x_215);
lean::dec(x_175);
lean::dec(x_191);
lean::dec(x_171);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_256);
x_363 = lean::cnstr_get(x_353, 0);
lean::inc(x_363);
lean::dec(x_353);
if (lean::is_scalar(x_248)) {
 x_366 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_366 = x_248;
 lean::cnstr_set_tag(x_248, 0);
}
lean::cnstr_set(x_366, 0, x_363);
x_5 = x_366;
goto lbl_6;
}
else
{
obj* x_368; 
lean::dec(x_248);
x_368 = lean::cnstr_get(x_353, 0);
lean::inc(x_368);
lean::dec(x_353);
x_257 = x_220;
x_258 = x_368;
goto lbl_259;
}
}
else
{
lean::dec(x_169);
if (lean::obj_tag(x_353) == 0)
{
obj* x_381; obj* x_384; 
lean::dec(x_214);
lean::dec(x_215);
lean::dec(x_175);
lean::dec(x_191);
lean::dec(x_171);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_256);
lean::dec(x_319);
x_381 = lean::cnstr_get(x_353, 0);
lean::inc(x_381);
lean::dec(x_353);
if (lean::is_scalar(x_248)) {
 x_384 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_384 = x_248;
 lean::cnstr_set_tag(x_248, 0);
}
lean::cnstr_set(x_384, 0, x_381);
x_5 = x_384;
goto lbl_6;
}
else
{
obj* x_386; obj* x_389; 
lean::dec(x_248);
x_386 = lean::cnstr_get(x_353, 0);
lean::inc(x_386);
lean::dec(x_353);
x_389 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(x_319);
x_257 = x_389;
x_258 = x_386;
goto lbl_259;
}
}
}
lbl_259:
{
obj* x_390; obj* x_392; obj* x_396; 
x_390 = lean::cnstr_get(x_258, 0);
lean::inc(x_390);
x_392 = lean::cnstr_get(x_258, 1);
lean::inc(x_392);
lean::dec(x_258);
lean::inc(x_1);
x_396 = l_lean_elaborator_simple__binders__to__pexpr(x_191, x_1, x_392);
if (lean::obj_tag(x_396) == 0)
{
obj* x_405; obj* x_408; 
lean::dec(x_215);
lean::dec(x_175);
lean::dec(x_171);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_256);
lean::dec(x_257);
lean::dec(x_390);
x_405 = lean::cnstr_get(x_396, 0);
lean::inc(x_405);
lean::dec(x_396);
if (lean::is_scalar(x_214)) {
 x_408 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_408 = x_214;
 lean::cnstr_set_tag(x_214, 0);
}
lean::cnstr_set(x_408, 0, x_405);
x_5 = x_408;
goto lbl_6;
}
else
{
obj* x_409; obj* x_412; obj* x_414; obj* x_420; 
x_409 = lean::cnstr_get(x_396, 0);
lean::inc(x_409);
lean::dec(x_396);
x_412 = lean::cnstr_get(x_409, 0);
lean::inc(x_412);
x_414 = lean::cnstr_get(x_409, 1);
lean::inc(x_414);
lean::dec(x_409);
lean::inc(x_1);
lean::inc(x_175);
lean::inc(x_0);
x_420 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_175, x_1, x_414);
if (lean::obj_tag(x_420) == 0)
{
obj* x_430; obj* x_433; 
lean::dec(x_215);
lean::dec(x_175);
lean::dec(x_171);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_256);
lean::dec(x_257);
lean::dec(x_412);
lean::dec(x_390);
x_430 = lean::cnstr_get(x_420, 0);
lean::inc(x_430);
lean::dec(x_420);
if (lean::is_scalar(x_214)) {
 x_433 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_433 = x_214;
 lean::cnstr_set_tag(x_214, 0);
}
lean::cnstr_set(x_433, 0, x_430);
x_5 = x_433;
goto lbl_6;
}
else
{
obj* x_435; obj* x_438; obj* x_440; obj* x_443; obj* x_444; obj* x_447; uint8 x_448; obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; 
lean::dec(x_214);
x_435 = lean::cnstr_get(x_420, 0);
lean::inc(x_435);
lean::dec(x_420);
x_438 = lean::cnstr_get(x_435, 0);
lean::inc(x_438);
x_440 = lean::cnstr_get(x_435, 1);
lean::inc(x_440);
lean::dec(x_435);
x_443 = l_lean_elaborator_names__to__pexpr(x_257);
x_444 = lean::cnstr_get(x_171, 0);
lean::inc(x_444);
lean::dec(x_171);
x_447 = l_lean_elaborator_mangle__ident(x_444);
x_448 = 0;
lean::inc(x_447);
x_450 = lean_expr_local(x_447, x_447, x_390, x_448);
x_451 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_451, 0, x_450);
lean::cnstr_set(x_451, 1, x_220);
x_452 = l_lean_expr_mk__capp(x_255, x_451);
x_453 = l_lean_expr_mk__capp(x_255, x_438);
x_454 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_454, 0, x_453);
lean::cnstr_set(x_454, 1, x_220);
x_455 = l_lean_expr_mk__capp(x_255, x_454);
x_456 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(x_175);
x_457 = l_lean_expr_mk__capp(x_255, x_456);
x_458 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_458, 0, x_457);
lean::cnstr_set(x_458, 1, x_220);
x_459 = l_lean_expr_mk__capp(x_255, x_458);
x_460 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_460, 0, x_459);
lean::cnstr_set(x_460, 1, x_220);
x_461 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_461, 0, x_455);
lean::cnstr_set(x_461, 1, x_460);
x_462 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_462, 0, x_412);
lean::cnstr_set(x_462, 1, x_461);
x_463 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_463, 0, x_452);
lean::cnstr_set(x_463, 1, x_462);
x_464 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_464, 0, x_443);
lean::cnstr_set(x_464, 1, x_463);
x_465 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_465, 0, x_256);
lean::cnstr_set(x_465, 1, x_464);
x_466 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_466, 0, x_215);
lean::cnstr_set(x_466, 1, x_465);
x_467 = l_lean_expr_mk__capp(x_255, x_466);
x_468 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
x_469 = lean_expr_mk_mdata(x_468, x_467);
x_470 = l_lean_elaborator_old__elab__command(x_0, x_469, x_1, x_440);
x_5 = x_470;
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
obj* x_477; obj* x_478; 
lean::dec(x_175);
lean::dec(x_173);
lean::dec(x_169);
lean::dec(x_167);
lean::dec(x_171);
lean::dec(x_12);
x_477 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_478 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_477, x_1, x_2);
x_5 = x_478;
goto lbl_6;
}
}
default:
{
obj* x_479; obj* x_482; obj* x_484; obj* x_486; obj* x_488; obj* x_490; obj* x_492; obj* x_494; 
x_479 = lean::cnstr_get(x_13, 0);
lean::inc(x_479);
lean::dec(x_13);
x_482 = lean::cnstr_get(x_479, 0);
lean::inc(x_482);
x_484 = lean::cnstr_get(x_479, 1);
lean::inc(x_484);
x_486 = lean::cnstr_get(x_479, 2);
lean::inc(x_486);
x_488 = lean::cnstr_get(x_479, 3);
lean::inc(x_488);
x_490 = lean::cnstr_get(x_479, 4);
lean::inc(x_490);
x_492 = lean::cnstr_get(x_479, 6);
lean::inc(x_492);
x_494 = lean::cnstr_get(x_479, 7);
lean::inc(x_494);
lean::dec(x_479);
if (lean::obj_tag(x_482) == 0)
{
obj* x_498; obj* x_500; 
lean::dec(x_482);
x_498 = lean::cnstr_get(x_488, 0);
lean::inc(x_498);
x_500 = lean::cnstr_get(x_488, 1);
lean::inc(x_500);
lean::dec(x_488);
if (lean::obj_tag(x_498) == 0)
{
obj* x_511; obj* x_512; 
lean::dec(x_492);
lean::dec(x_490);
lean::dec(x_484);
lean::dec(x_486);
lean::dec(x_494);
lean::dec(x_12);
lean::dec(x_500);
lean::dec(x_498);
x_511 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_512 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_511, x_1, x_2);
x_5 = x_512;
goto lbl_6;
}
else
{
obj* x_513; obj* x_516; obj* x_520; 
x_513 = lean::cnstr_get(x_498, 0);
lean::inc(x_513);
lean::dec(x_498);
x_516 = lean::cnstr_get(x_12, 0);
lean::inc(x_516);
lean::dec(x_12);
lean::inc(x_1);
x_520 = l_lean_elaborator_decl__modifiers__to__pexpr(x_516, x_1, x_2);
if (lean::obj_tag(x_520) == 0)
{
obj* x_530; obj* x_532; obj* x_533; 
lean::dec(x_492);
lean::dec(x_490);
lean::dec(x_484);
lean::dec(x_486);
lean::dec(x_494);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_513);
lean::dec(x_500);
x_530 = lean::cnstr_get(x_520, 0);
if (lean::is_exclusive(x_520)) {
 lean::cnstr_set(x_520, 0, lean::box(0));
 x_532 = x_520;
} else {
 lean::inc(x_530);
 lean::dec(x_520);
 x_532 = lean::box(0);
}
if (lean::is_scalar(x_532)) {
 x_533 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_533 = x_532;
}
lean::cnstr_set(x_533, 0, x_530);
x_5 = x_533;
goto lbl_6;
}
else
{
obj* x_534; obj* x_536; obj* x_537; obj* x_539; obj* x_542; obj* x_543; obj* x_544; 
x_534 = lean::cnstr_get(x_520, 0);
if (lean::is_exclusive(x_520)) {
 lean::cnstr_set(x_520, 0, lean::box(0));
 x_536 = x_520;
} else {
 lean::inc(x_534);
 lean::dec(x_520);
 x_536 = lean::box(0);
}
x_537 = lean::cnstr_get(x_534, 0);
lean::inc(x_537);
x_539 = lean::cnstr_get(x_534, 1);
lean::inc(x_539);
lean::dec(x_534);
x_542 = lean::box(0);
if (lean::obj_tag(x_484) == 0)
{
obj* x_546; obj* x_548; 
x_546 = l_lean_expander_get__opt__type___main(x_500);
lean::inc(x_1);
x_548 = l_lean_elaborator_to__pexpr___main(x_546, x_1, x_539);
if (lean::obj_tag(x_484) == 0)
{
if (lean::obj_tag(x_548) == 0)
{
obj* x_558; obj* x_560; obj* x_561; 
lean::dec(x_492);
lean::dec(x_490);
lean::dec(x_486);
lean::dec(x_494);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_513);
lean::dec(x_537);
lean::dec(x_536);
x_558 = lean::cnstr_get(x_548, 0);
if (lean::is_exclusive(x_548)) {
 lean::cnstr_set(x_548, 0, lean::box(0));
 x_560 = x_548;
} else {
 lean::inc(x_558);
 lean::dec(x_548);
 x_560 = lean::box(0);
}
if (lean::is_scalar(x_560)) {
 x_561 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_561 = x_560;
}
lean::cnstr_set(x_561, 0, x_558);
x_5 = x_561;
goto lbl_6;
}
else
{
obj* x_562; 
x_562 = lean::cnstr_get(x_548, 0);
lean::inc(x_562);
lean::dec(x_548);
x_543 = x_542;
x_544 = x_562;
goto lbl_545;
}
}
else
{
obj* x_565; 
x_565 = lean::cnstr_get(x_484, 0);
lean::inc(x_565);
lean::dec(x_484);
if (lean::obj_tag(x_548) == 0)
{
obj* x_578; obj* x_580; obj* x_581; 
lean::dec(x_492);
lean::dec(x_490);
lean::dec(x_486);
lean::dec(x_494);
lean::dec(x_565);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_513);
lean::dec(x_537);
lean::dec(x_536);
x_578 = lean::cnstr_get(x_548, 0);
if (lean::is_exclusive(x_548)) {
 lean::cnstr_set(x_548, 0, lean::box(0));
 x_580 = x_548;
} else {
 lean::inc(x_578);
 lean::dec(x_548);
 x_580 = lean::box(0);
}
if (lean::is_scalar(x_580)) {
 x_581 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_581 = x_580;
}
lean::cnstr_set(x_581, 0, x_578);
x_5 = x_581;
goto lbl_6;
}
else
{
obj* x_582; obj* x_585; obj* x_588; 
x_582 = lean::cnstr_get(x_548, 0);
lean::inc(x_582);
lean::dec(x_548);
x_585 = lean::cnstr_get(x_565, 1);
lean::inc(x_585);
lean::dec(x_565);
x_588 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(x_585);
x_543 = x_588;
x_544 = x_582;
goto lbl_545;
}
}
}
else
{
obj* x_589; obj* x_591; obj* x_593; obj* x_595; obj* x_597; obj* x_599; obj* x_601; obj* x_603; obj* x_605; obj* x_609; obj* x_610; obj* x_611; obj* x_613; obj* x_615; obj* x_617; obj* x_619; obj* x_622; obj* x_623; obj* x_625; obj* x_627; obj* x_629; obj* x_631; obj* x_633; obj* x_636; obj* x_637; obj* x_639; 
x_589 = lean::cnstr_get(x_484, 0);
lean::inc(x_589);
x_591 = lean::cnstr_get(x_539, 0);
lean::inc(x_591);
x_593 = lean::cnstr_get(x_539, 1);
lean::inc(x_593);
x_595 = lean::cnstr_get(x_539, 2);
lean::inc(x_595);
x_597 = lean::cnstr_get(x_539, 3);
lean::inc(x_597);
x_599 = lean::cnstr_get(x_539, 4);
lean::inc(x_599);
x_601 = lean::cnstr_get(x_599, 0);
lean::inc(x_601);
x_603 = lean::cnstr_get(x_599, 1);
lean::inc(x_603);
x_605 = lean::cnstr_get(x_589, 1);
lean::inc(x_605);
lean::dec(x_589);
lean::inc(x_605);
x_609 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(x_605);
x_610 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(x_603, x_609);
x_611 = lean::cnstr_get(x_599, 2);
lean::inc(x_611);
x_613 = lean::cnstr_get(x_599, 3);
lean::inc(x_613);
x_615 = lean::cnstr_get(x_599, 4);
lean::inc(x_615);
x_617 = lean::cnstr_get(x_599, 5);
lean::inc(x_617);
x_619 = lean::cnstr_get(x_599, 6);
lean::inc(x_619);
lean::dec(x_599);
x_622 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_622, 0, x_601);
lean::cnstr_set(x_622, 1, x_610);
lean::cnstr_set(x_622, 2, x_611);
lean::cnstr_set(x_622, 3, x_613);
lean::cnstr_set(x_622, 4, x_615);
lean::cnstr_set(x_622, 5, x_617);
lean::cnstr_set(x_622, 6, x_619);
x_623 = lean::cnstr_get(x_539, 5);
lean::inc(x_623);
x_625 = lean::cnstr_get(x_539, 6);
lean::inc(x_625);
x_627 = lean::cnstr_get(x_539, 7);
lean::inc(x_627);
x_629 = lean::cnstr_get(x_539, 8);
lean::inc(x_629);
x_631 = lean::cnstr_get(x_539, 9);
lean::inc(x_631);
x_633 = lean::cnstr_get(x_539, 10);
lean::inc(x_633);
lean::dec(x_539);
x_636 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_636, 0, x_591);
lean::cnstr_set(x_636, 1, x_593);
lean::cnstr_set(x_636, 2, x_595);
lean::cnstr_set(x_636, 3, x_597);
lean::cnstr_set(x_636, 4, x_622);
lean::cnstr_set(x_636, 5, x_623);
lean::cnstr_set(x_636, 6, x_625);
lean::cnstr_set(x_636, 7, x_627);
lean::cnstr_set(x_636, 8, x_629);
lean::cnstr_set(x_636, 9, x_631);
lean::cnstr_set(x_636, 10, x_633);
x_637 = l_lean_expander_get__opt__type___main(x_500);
lean::inc(x_1);
x_639 = l_lean_elaborator_to__pexpr___main(x_637, x_1, x_636);
if (lean::obj_tag(x_484) == 0)
{
lean::dec(x_605);
if (lean::obj_tag(x_639) == 0)
{
obj* x_650; obj* x_652; obj* x_653; 
lean::dec(x_492);
lean::dec(x_490);
lean::dec(x_486);
lean::dec(x_494);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_513);
lean::dec(x_537);
lean::dec(x_536);
x_650 = lean::cnstr_get(x_639, 0);
if (lean::is_exclusive(x_639)) {
 lean::cnstr_set(x_639, 0, lean::box(0));
 x_652 = x_639;
} else {
 lean::inc(x_650);
 lean::dec(x_639);
 x_652 = lean::box(0);
}
if (lean::is_scalar(x_652)) {
 x_653 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_653 = x_652;
}
lean::cnstr_set(x_653, 0, x_650);
x_5 = x_653;
goto lbl_6;
}
else
{
obj* x_654; 
x_654 = lean::cnstr_get(x_639, 0);
lean::inc(x_654);
lean::dec(x_639);
x_543 = x_542;
x_544 = x_654;
goto lbl_545;
}
}
else
{
lean::dec(x_484);
if (lean::obj_tag(x_639) == 0)
{
obj* x_668; obj* x_670; obj* x_671; 
lean::dec(x_492);
lean::dec(x_490);
lean::dec(x_486);
lean::dec(x_494);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_513);
lean::dec(x_537);
lean::dec(x_536);
lean::dec(x_605);
x_668 = lean::cnstr_get(x_639, 0);
if (lean::is_exclusive(x_639)) {
 lean::cnstr_set(x_639, 0, lean::box(0));
 x_670 = x_639;
} else {
 lean::inc(x_668);
 lean::dec(x_639);
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
obj* x_672; obj* x_675; 
x_672 = lean::cnstr_get(x_639, 0);
lean::inc(x_672);
lean::dec(x_639);
x_675 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(x_605);
x_543 = x_675;
x_544 = x_672;
goto lbl_545;
}
}
}
lbl_545:
{
obj* x_676; obj* x_678; obj* x_682; 
x_676 = lean::cnstr_get(x_544, 0);
lean::inc(x_676);
x_678 = lean::cnstr_get(x_544, 1);
lean::inc(x_678);
lean::dec(x_544);
lean::inc(x_1);
x_682 = l_lean_elaborator_simple__binders__to__pexpr(x_513, x_1, x_678);
if (lean::obj_tag(x_682) == 0)
{
obj* x_692; obj* x_695; 
lean::dec(x_492);
lean::dec(x_490);
lean::dec(x_486);
lean::dec(x_494);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_537);
lean::dec(x_543);
lean::dec(x_676);
x_692 = lean::cnstr_get(x_682, 0);
lean::inc(x_692);
lean::dec(x_682);
if (lean::is_scalar(x_536)) {
 x_695 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_695 = x_536;
 lean::cnstr_set_tag(x_536, 0);
}
lean::cnstr_set(x_695, 0, x_692);
x_5 = x_695;
goto lbl_6;
}
else
{
obj* x_696; obj* x_699; obj* x_701; obj* x_704; obj* x_705; obj* x_708; obj* x_709; uint8 x_710; obj* x_712; obj* x_713; 
x_696 = lean::cnstr_get(x_682, 0);
lean::inc(x_696);
lean::dec(x_682);
x_699 = lean::cnstr_get(x_696, 0);
lean::inc(x_699);
x_701 = lean::cnstr_get(x_696, 1);
lean::inc(x_701);
lean::dec(x_696);
x_704 = l_lean_elaborator_names__to__pexpr(x_543);
x_705 = lean::cnstr_get(x_486, 0);
lean::inc(x_705);
lean::dec(x_486);
x_708 = l_lean_elaborator_mangle__ident(x_705);
x_709 = l_lean_elaborator_dummy;
x_710 = 0;
lean::inc(x_708);
x_712 = lean_expr_local(x_708, x_708, x_709, x_710);
if (lean::obj_tag(x_490) == 0)
{
x_713 = x_542;
goto lbl_714;
}
else
{
obj* x_715; obj* x_718; 
x_715 = lean::cnstr_get(x_490, 0);
lean::inc(x_715);
lean::dec(x_490);
x_718 = lean::cnstr_get(x_715, 1);
lean::inc(x_718);
lean::dec(x_715);
x_713 = x_718;
goto lbl_714;
}
lbl_714:
{
obj* x_722; 
lean::inc(x_1);
x_722 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_713, x_1, x_701);
if (lean::obj_tag(x_722) == 0)
{
obj* x_732; obj* x_735; 
lean::dec(x_492);
lean::dec(x_494);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_537);
lean::dec(x_699);
lean::dec(x_704);
lean::dec(x_712);
lean::dec(x_676);
x_732 = lean::cnstr_get(x_722, 0);
lean::inc(x_732);
lean::dec(x_722);
if (lean::is_scalar(x_536)) {
 x_735 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_735 = x_536;
 lean::cnstr_set_tag(x_536, 0);
}
lean::cnstr_set(x_735, 0, x_732);
x_5 = x_735;
goto lbl_6;
}
else
{
obj* x_736; obj* x_739; obj* x_741; obj* x_744; obj* x_745; obj* x_748; obj* x_749; 
x_736 = lean::cnstr_get(x_722, 0);
lean::inc(x_736);
lean::dec(x_722);
x_739 = lean::cnstr_get(x_736, 0);
lean::inc(x_739);
x_741 = lean::cnstr_get(x_736, 1);
lean::inc(x_741);
lean::dec(x_736);
x_744 = l_lean_elaborator_mk__eqns___closed__1;
x_745 = l_lean_expr_mk__capp(x_744, x_739);
lean::inc(x_1);
lean::inc(x_0);
x_748 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_494, x_1, x_741);
if (lean::obj_tag(x_492) == 0)
{
obj* x_751; 
x_751 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7;
x_749 = x_751;
goto lbl_750;
}
else
{
obj* x_752; obj* x_754; obj* x_757; 
x_752 = lean::cnstr_get(x_492, 0);
lean::inc(x_752);
x_754 = lean::cnstr_get(x_752, 0);
lean::inc(x_754);
lean::dec(x_752);
x_757 = l_lean_elaborator_mangle__ident(x_754);
x_749 = x_757;
goto lbl_750;
}
lbl_750:
{
obj* x_759; 
lean::inc(x_749);
x_759 = lean_expr_local(x_749, x_749, x_709, x_710);
if (lean::obj_tag(x_492) == 0)
{
if (lean::obj_tag(x_748) == 0)
{
obj* x_769; obj* x_772; 
lean::dec(x_745);
lean::dec(x_759);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_537);
lean::dec(x_699);
lean::dec(x_704);
lean::dec(x_712);
lean::dec(x_676);
x_769 = lean::cnstr_get(x_748, 0);
lean::inc(x_769);
lean::dec(x_748);
if (lean::is_scalar(x_536)) {
 x_772 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_772 = x_536;
 lean::cnstr_set_tag(x_536, 0);
}
lean::cnstr_set(x_772, 0, x_769);
x_5 = x_772;
goto lbl_6;
}
else
{
obj* x_774; obj* x_777; obj* x_779; obj* x_782; obj* x_783; obj* x_784; obj* x_785; obj* x_786; obj* x_787; obj* x_788; obj* x_789; obj* x_790; obj* x_791; obj* x_792; obj* x_793; obj* x_794; obj* x_795; obj* x_796; 
lean::dec(x_536);
x_774 = lean::cnstr_get(x_748, 0);
lean::inc(x_774);
lean::dec(x_748);
x_777 = lean::cnstr_get(x_774, 0);
lean::inc(x_777);
x_779 = lean::cnstr_get(x_774, 1);
lean::inc(x_779);
lean::dec(x_774);
x_782 = l_lean_expr_mk__capp(x_744, x_777);
x_783 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_783, 0, x_782);
lean::cnstr_set(x_783, 1, x_542);
x_784 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5;
x_785 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_785, 0, x_784);
lean::cnstr_set(x_785, 1, x_783);
x_786 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_786, 0, x_759);
lean::cnstr_set(x_786, 1, x_785);
x_787 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_787, 0, x_676);
lean::cnstr_set(x_787, 1, x_786);
x_788 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_788, 0, x_745);
lean::cnstr_set(x_788, 1, x_787);
x_789 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_789, 0, x_699);
lean::cnstr_set(x_789, 1, x_788);
x_790 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_790, 0, x_712);
lean::cnstr_set(x_790, 1, x_789);
x_791 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_791, 0, x_704);
lean::cnstr_set(x_791, 1, x_790);
x_792 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_792, 0, x_537);
lean::cnstr_set(x_792, 1, x_791);
x_793 = l_lean_expr_mk__capp(x_744, x_792);
x_794 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
x_795 = lean_expr_mk_mdata(x_794, x_793);
x_796 = l_lean_elaborator_old__elab__command(x_0, x_795, x_1, x_779);
x_5 = x_796;
goto lbl_6;
}
}
else
{
obj* x_797; 
x_797 = lean::cnstr_get(x_492, 0);
lean::inc(x_797);
lean::dec(x_492);
if (lean::obj_tag(x_748) == 0)
{
obj* x_810; obj* x_813; 
lean::dec(x_797);
lean::dec(x_745);
lean::dec(x_759);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_537);
lean::dec(x_699);
lean::dec(x_704);
lean::dec(x_712);
lean::dec(x_676);
x_810 = lean::cnstr_get(x_748, 0);
lean::inc(x_810);
lean::dec(x_748);
if (lean::is_scalar(x_536)) {
 x_813 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_813 = x_536;
 lean::cnstr_set_tag(x_536, 0);
}
lean::cnstr_set(x_813, 0, x_810);
x_5 = x_813;
goto lbl_6;
}
else
{
obj* x_815; obj* x_818; obj* x_820; obj* x_823; obj* x_826; obj* x_827; obj* x_828; obj* x_829; obj* x_830; obj* x_831; obj* x_832; obj* x_833; obj* x_834; obj* x_835; obj* x_836; obj* x_837; obj* x_838; obj* x_839; obj* x_840; 
lean::dec(x_536);
x_815 = lean::cnstr_get(x_748, 0);
lean::inc(x_815);
lean::dec(x_748);
x_818 = lean::cnstr_get(x_815, 0);
lean::inc(x_818);
x_820 = lean::cnstr_get(x_815, 1);
lean::inc(x_820);
lean::dec(x_815);
x_823 = lean::cnstr_get(x_797, 1);
lean::inc(x_823);
lean::dec(x_797);
x_826 = l_lean_elaborator_infer__mod__to__pexpr(x_823);
x_827 = l_lean_expr_mk__capp(x_744, x_818);
x_828 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_828, 0, x_827);
lean::cnstr_set(x_828, 1, x_542);
x_829 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_829, 0, x_826);
lean::cnstr_set(x_829, 1, x_828);
x_830 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_830, 0, x_759);
lean::cnstr_set(x_830, 1, x_829);
x_831 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_831, 0, x_676);
lean::cnstr_set(x_831, 1, x_830);
x_832 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_832, 0, x_745);
lean::cnstr_set(x_832, 1, x_831);
x_833 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_833, 0, x_699);
lean::cnstr_set(x_833, 1, x_832);
x_834 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_834, 0, x_712);
lean::cnstr_set(x_834, 1, x_833);
x_835 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_835, 0, x_704);
lean::cnstr_set(x_835, 1, x_834);
x_836 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_836, 0, x_537);
lean::cnstr_set(x_836, 1, x_835);
x_837 = l_lean_expr_mk__capp(x_744, x_836);
x_838 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
x_839 = lean_expr_mk_mdata(x_838, x_837);
x_840 = l_lean_elaborator_old__elab__command(x_0, x_839, x_1, x_820);
x_5 = x_840;
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
obj* x_849; obj* x_850; 
lean::dec(x_492);
lean::dec(x_490);
lean::dec(x_484);
lean::dec(x_482);
lean::dec(x_488);
lean::dec(x_486);
lean::dec(x_494);
lean::dec(x_12);
x_849 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_850 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_849, x_1, x_2);
x_5 = x_850;
goto lbl_6;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_852; obj* x_854; obj* x_855; 
lean::dec(x_3);
x_852 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_854 = x_5;
} else {
 lean::inc(x_852);
 lean::dec(x_5);
 x_854 = lean::box(0);
}
if (lean::is_scalar(x_854)) {
 x_855 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_855 = x_854;
}
lean::cnstr_set(x_855, 0, x_852);
return x_855;
}
else
{
obj* x_856; obj* x_858; obj* x_859; obj* x_861; obj* x_862; obj* x_864; obj* x_866; obj* x_868; obj* x_870; obj* x_872; obj* x_874; obj* x_876; obj* x_878; obj* x_880; obj* x_883; obj* x_884; obj* x_885; obj* x_886; 
x_856 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_858 = x_5;
} else {
 lean::inc(x_856);
 lean::dec(x_5);
 x_858 = lean::box(0);
}
x_859 = lean::cnstr_get(x_856, 1);
if (lean::is_exclusive(x_856)) {
 lean::cnstr_release(x_856, 0);
 lean::cnstr_set(x_856, 1, lean::box(0));
 x_861 = x_856;
} else {
 lean::inc(x_859);
 lean::dec(x_856);
 x_861 = lean::box(0);
}
x_862 = lean::cnstr_get(x_859, 0);
lean::inc(x_862);
x_864 = lean::cnstr_get(x_859, 1);
lean::inc(x_864);
x_866 = lean::cnstr_get(x_859, 2);
lean::inc(x_866);
x_868 = lean::cnstr_get(x_859, 3);
lean::inc(x_868);
x_870 = lean::cnstr_get(x_859, 5);
lean::inc(x_870);
x_872 = lean::cnstr_get(x_859, 6);
lean::inc(x_872);
x_874 = lean::cnstr_get(x_859, 7);
lean::inc(x_874);
x_876 = lean::cnstr_get(x_859, 8);
lean::inc(x_876);
x_878 = lean::cnstr_get(x_859, 9);
lean::inc(x_878);
x_880 = lean::cnstr_get(x_859, 10);
lean::inc(x_880);
lean::dec(x_859);
x_883 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_883, 0, x_862);
lean::cnstr_set(x_883, 1, x_864);
lean::cnstr_set(x_883, 2, x_866);
lean::cnstr_set(x_883, 3, x_868);
lean::cnstr_set(x_883, 4, x_3);
lean::cnstr_set(x_883, 5, x_870);
lean::cnstr_set(x_883, 6, x_872);
lean::cnstr_set(x_883, 7, x_874);
lean::cnstr_set(x_883, 8, x_876);
lean::cnstr_set(x_883, 9, x_878);
lean::cnstr_set(x_883, 10, x_880);
x_884 = lean::box(0);
if (lean::is_scalar(x_861)) {
 x_885 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_885 = x_861;
}
lean::cnstr_set(x_885, 0, x_884);
lean::cnstr_set(x_885, 1, x_883);
if (lean::is_scalar(x_858)) {
 x_886 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_886 = x_858;
}
lean::cnstr_set(x_886, 0, x_885);
return x_886;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; uint8 x_28; 
x_6 = lean::cnstr_get(x_0, 0);
x_8 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_10 = x_0;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_0);
 x_10 = lean::box(0);
}
lean::inc(x_6);
x_14 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_6);
x_15 = lean::cnstr_get(x_14, 0);
x_17 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_set(x_14, 1, lean::box(0));
 x_19 = x_14;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_14);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_17, 0);
x_22 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_set(x_17, 0, lean::box(0));
 lean::cnstr_set(x_17, 1, lean::box(0));
 x_24 = x_17;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_17);
 x_24 = lean::box(0);
}
x_27 = l_lean_expander_binding__annotation__update;
x_28 = l_lean_parser_syntax_is__of__kind___main(x_27, x_22);
if (x_28 == 0)
{
uint8 x_32; obj* x_33; obj* x_34; 
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_20);
x_32 = 1;
x_33 = lean::box(x_32);
if (lean::is_scalar(x_24)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_24;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_2);
x_11 = x_34;
goto lbl_12;
}
else
{
obj* x_36; 
lean::dec(x_24);
x_36 = lean::box(0);
x_25 = x_36;
goto lbl_26;
}
lbl_12:
{
obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_11, 0);
x_39 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_set(x_11, 1, lean::box(0));
 x_41 = x_11;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_11);
 x_41 = lean::box(0);
}
x_42 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_8, x_1, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_37);
lean::dec(x_41);
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
obj* x_51; obj* x_53; obj* x_54; obj* x_56; uint8 x_59; 
x_51 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_set(x_42, 0, lean::box(0));
 x_53 = x_42;
} else {
 lean::inc(x_51);
 lean::dec(x_42);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
x_59 = lean::unbox(x_37);
if (x_59 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_6);
lean::dec(x_10);
if (lean::is_scalar(x_41)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_41;
}
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_56);
if (lean::is_scalar(x_53)) {
 x_63 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_63 = x_53;
}
lean::cnstr_set(x_63, 0, x_62);
return x_63;
}
else
{
obj* x_64; obj* x_65; obj* x_66; 
if (lean::is_scalar(x_10)) {
 x_64 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_64 = x_10;
}
lean::cnstr_set(x_64, 0, x_6);
lean::cnstr_set(x_64, 1, x_54);
if (lean::is_scalar(x_41)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_41;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_56);
if (lean::is_scalar(x_53)) {
 x_66 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_66 = x_53;
}
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
}
}
lbl_26:
{
obj* x_68; obj* x_69; obj* x_71; obj* x_75; 
lean::dec(x_25);
x_68 = l_lean_elaborator_mangle__ident(x_20);
x_69 = lean::cnstr_get(x_2, 4);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_69, 2);
lean::inc(x_71);
lean::inc(x_68);
lean::inc(x_71);
x_75 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_71, x_68);
if (lean::obj_tag(x_75) == 0)
{
obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_88; 
lean::dec(x_15);
lean::dec(x_71);
lean::dec(x_69);
x_79 = lean::box(0);
x_80 = l_lean_name_to__string___closed__1;
lean::inc(x_68);
x_82 = l_lean_name_to__string__with__sep___main(x_80, x_68);
x_83 = l_lean_parser_substring_of__string(x_82);
x_84 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_84, 0, x_79);
lean::cnstr_set(x_84, 1, x_83);
lean::cnstr_set(x_84, 2, x_68);
lean::cnstr_set(x_84, 3, x_79);
lean::cnstr_set(x_84, 4, x_79);
x_85 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
x_86 = l_string_join___closed__1;
lean::inc(x_1);
x_88 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_85, x_86, x_1, x_2);
if (lean::obj_tag(x_88) == 0)
{
obj* x_94; obj* x_96; obj* x_97; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_19);
x_94 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_set(x_88, 0, lean::box(0));
 x_96 = x_88;
} else {
 lean::inc(x_94);
 lean::dec(x_88);
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
obj* x_98; obj* x_101; uint8 x_104; obj* x_105; obj* x_106; 
x_98 = lean::cnstr_get(x_88, 0);
lean::inc(x_98);
lean::dec(x_88);
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
lean::dec(x_98);
x_104 = 0;
x_105 = lean::box(x_104);
if (lean::is_scalar(x_19)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_19;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_101);
x_11 = x_106;
goto lbl_12;
}
}
else
{
obj* x_107; obj* x_110; obj* x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_130; uint8 x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_136; obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_157; uint8 x_158; obj* x_159; obj* x_160; 
x_107 = lean::cnstr_get(x_75, 0);
lean::inc(x_107);
lean::dec(x_75);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
x_113 = lean::cnstr_get(x_2, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_2, 1);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_2, 2);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_2, 3);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_69, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_69, 1);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_110, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_110, 1);
lean::inc(x_127);
lean::dec(x_110);
x_130 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_130, 0, x_125);
lean::cnstr_set(x_130, 1, x_127);
x_131 = lean::unbox(x_15);
lean::cnstr_set_scalar(x_130, sizeof(void*)*2, x_131);
x_132 = x_130;
x_133 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(x_71, x_68, x_132);
x_134 = lean::cnstr_get(x_69, 3);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_69, 4);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_69, 5);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_69, 6);
lean::inc(x_140);
lean::dec(x_69);
x_143 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_143, 0, x_121);
lean::cnstr_set(x_143, 1, x_123);
lean::cnstr_set(x_143, 2, x_133);
lean::cnstr_set(x_143, 3, x_134);
lean::cnstr_set(x_143, 4, x_136);
lean::cnstr_set(x_143, 5, x_138);
lean::cnstr_set(x_143, 6, x_140);
x_144 = lean::cnstr_get(x_2, 5);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_2, 6);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_2, 7);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_2, 8);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_2, 9);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_2, 10);
lean::inc(x_154);
lean::dec(x_2);
x_157 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_157, 0, x_113);
lean::cnstr_set(x_157, 1, x_115);
lean::cnstr_set(x_157, 2, x_117);
lean::cnstr_set(x_157, 3, x_119);
lean::cnstr_set(x_157, 4, x_143);
lean::cnstr_set(x_157, 5, x_144);
lean::cnstr_set(x_157, 6, x_146);
lean::cnstr_set(x_157, 7, x_148);
lean::cnstr_set(x_157, 8, x_150);
lean::cnstr_set(x_157, 9, x_152);
lean::cnstr_set(x_157, 10, x_154);
x_158 = 0;
x_159 = lean::box(x_158);
if (lean::is_scalar(x_19)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_19;
}
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_157);
x_11 = x_160;
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
obj* x_3; obj* x_4; obj* x_8; obj* x_9; 
x_3 = l_lean_parser_command_variables_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
lean::inc(x_0);
x_8 = lean::apply_1(x_4, x_0);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_13; obj* x_16; 
lean::dec(x_9);
x_13 = l_lean_elaborator_variables_elaborate___closed__1;
lean::inc(x_1);
lean::inc(x_0);
x_16 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_13, x_1, x_2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_1);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_21 = x_16;
} else {
 lean::inc(x_19);
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
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_25 = x_16;
} else {
 lean::inc(x_23);
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
obj* x_40; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; 
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
x_49 = lean_expr_mk_mdata(x_48, x_43);
x_50 = l_lean_elaborator_old__elab__command(x_0, x_49, x_1, x_45);
return x_50;
}
}
}
else
{
obj* x_51; obj* x_55; 
x_51 = lean::cnstr_get(x_9, 0);
lean::inc(x_51);
lean::dec(x_9);
lean::inc(x_1);
x_55 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_51, x_1, x_2);
if (lean::obj_tag(x_55) == 0)
{
obj* x_58; obj* x_60; obj* x_61; 
lean::dec(x_1);
lean::dec(x_0);
x_58 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_set(x_55, 0, lean::box(0));
 x_60 = x_55;
} else {
 lean::inc(x_58);
 lean::dec(x_55);
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
obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_71; 
x_62 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_set(x_55, 0, lean::box(0));
 x_64 = x_55;
} else {
 lean::inc(x_62);
 lean::dec(x_55);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_62, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_62, 1);
lean::inc(x_67);
lean::dec(x_62);
lean::inc(x_1);
x_71 = l_lean_elaborator_simple__binders__to__pexpr(x_65, x_1, x_67);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; obj* x_77; 
lean::dec(x_1);
lean::dec(x_0);
x_74 = lean::cnstr_get(x_71, 0);
lean::inc(x_74);
lean::dec(x_71);
if (lean::is_scalar(x_64)) {
 x_77 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_77 = x_64;
 lean::cnstr_set_tag(x_64, 0);
}
lean::cnstr_set(x_77, 0, x_74);
return x_77;
}
else
{
obj* x_79; obj* x_82; obj* x_84; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_64);
x_79 = lean::cnstr_get(x_71, 0);
lean::inc(x_79);
lean::dec(x_71);
x_82 = lean::cnstr_get(x_79, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_79, 1);
lean::inc(x_84);
lean::dec(x_79);
x_87 = l_lean_elaborator_variables_elaborate___closed__2;
x_88 = lean_expr_mk_mdata(x_87, x_82);
x_89 = l_lean_elaborator_old__elab__command(x_0, x_88, x_1, x_84);
return x_89;
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
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_1);
x_4 = l_lean_parser_command_include_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 2);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 3);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_2, 4);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_17, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_17, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_17, 3);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_8, 1);
lean::inc(x_27);
lean::dec(x_8);
x_30 = l_list_foldl___main___at_lean_elaborator_include_elaborate___spec__2(x_25, x_27);
x_31 = lean::cnstr_get(x_17, 4);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_17, 5);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_17, 6);
lean::inc(x_35);
lean::dec(x_17);
x_38 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_38, 0, x_19);
lean::cnstr_set(x_38, 1, x_21);
lean::cnstr_set(x_38, 2, x_23);
lean::cnstr_set(x_38, 3, x_30);
lean::cnstr_set(x_38, 4, x_31);
lean::cnstr_set(x_38, 5, x_33);
lean::cnstr_set(x_38, 6, x_35);
x_39 = lean::cnstr_get(x_2, 5);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_2, 6);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_2, 7);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_2, 8);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_2, 9);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_2, 10);
lean::inc(x_49);
lean::dec(x_2);
x_52 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_52, 0, x_9);
lean::cnstr_set(x_52, 1, x_11);
lean::cnstr_set(x_52, 2, x_13);
lean::cnstr_set(x_52, 3, x_15);
lean::cnstr_set(x_52, 4, x_38);
lean::cnstr_set(x_52, 5, x_39);
lean::cnstr_set(x_52, 6, x_41);
lean::cnstr_set(x_52, 7, x_43);
lean::cnstr_set(x_52, 8, x_45);
lean::cnstr_set(x_52, 9, x_47);
lean::cnstr_set(x_52, 10, x_49);
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
return x_55;
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
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_11; 
x_3 = l_lean_parser_module_header_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
lean::inc(x_0);
x_8 = lean::apply_1(x_4, x_0);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_15; obj* x_16; 
lean::dec(x_11);
x_15 = l_lean_elaborator_module_header_elaborate___closed__1;
x_16 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_15, x_1, x_2);
return x_16;
}
else
{
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
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
obj* x_24; obj* x_25; 
lean::dec(x_11);
x_24 = l_lean_elaborator_module_header_elaborate___closed__1;
x_25 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_24, x_1, x_2);
return x_25;
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
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_49; 
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
lean::dec(x_11);
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
lean::dec(x_23);
x_30 = lean::cnstr_get(x_20, 1);
lean::inc(x_30);
lean::dec(x_20);
x_33 = l_string_trim(x_30);
x_34 = l_lean_elaborator_prec__to__nat___main(x_13);
x_35 = lean::box(0);
lean::inc(x_33);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set(x_37, 1, x_34);
lean::cnstr_set(x_37, 2, x_35);
x_38 = l_lean_parser_trie_insert___rarg(x_27, x_33, x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_25);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::cnstr_get(x_0, 1);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_0, 2);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_0, 3);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_0, 4);
lean::inc(x_46);
lean::dec(x_0);
x_49 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_49, 0, x_39);
lean::cnstr_set(x_49, 1, x_40);
lean::cnstr_set(x_49, 2, x_42);
lean::cnstr_set(x_49, 3, x_44);
lean::cnstr_set(x_49, 4, x_46);
x_0 = x_49;
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
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
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
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
lean::dec(x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_2);
x_17 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5;
x_7 = x_17;
goto lbl_8;
}
else
{
obj* x_18; obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_18 = lean::cnstr_get(x_13, 0);
lean::inc(x_18);
lean::dec(x_13);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_string_trim(x_21);
lean::inc(x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_26, 0, x_24);
x_27 = lean::mk_nat_obj(0u);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1), 8, 3);
lean::closure_set(x_28, 0, x_24);
lean::closure_set(x_28, 1, x_27);
lean::closure_set(x_28, 2, x_26);
x_9 = x_28;
goto lbl_10;
}
lbl_8:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_6);
lean::dec(x_4);
x_31 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_33 = x_7;
} else {
 lean::inc(x_31);
 lean::dec(x_7);
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
obj* x_35; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_37 = x_7;
} else {
 lean::inc(x_35);
 lean::dec(x_7);
 x_37 = lean::box(0);
}
x_38 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(x_4);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_44; 
lean::dec(x_6);
lean::dec(x_35);
x_41 = lean::cnstr_get(x_38, 0);
lean::inc(x_41);
lean::dec(x_38);
if (lean::is_scalar(x_37)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_37;
 lean::cnstr_set_tag(x_37, 0);
}
lean::cnstr_set(x_44, 0, x_41);
return x_44;
}
else
{
obj* x_45; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_38, 0);
lean::inc(x_45);
lean::dec(x_38);
if (lean::is_scalar(x_6)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_6;
}
lean::cnstr_set(x_48, 0, x_35);
lean::cnstr_set(x_48, 1, x_45);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
}
}
lbl_10:
{
obj* x_50; obj* x_52; 
x_52 = lean::cnstr_get(x_2, 1);
lean::inc(x_52);
lean::dec(x_2);
if (lean::obj_tag(x_52) == 0)
{
obj* x_55; 
x_55 = l_lean_expander_no__expansion___closed__1;
x_50 = x_55;
goto lbl_51;
}
else
{
obj* x_56; obj* x_58; 
x_56 = lean::cnstr_get(x_52, 0);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_set(x_52, 0, lean::box(0));
 x_58 = x_52;
} else {
 lean::inc(x_56);
 lean::dec(x_52);
 x_58 = lean::box(0);
}
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_61; 
lean::dec(x_58);
lean::dec(x_56);
x_61 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
x_50 = x_61;
goto lbl_51;
}
case 1:
{
obj* x_64; 
lean::dec(x_58);
lean::dec(x_56);
x_64 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2;
x_50 = x_64;
goto lbl_51;
}
default:
{
obj* x_65; obj* x_68; 
x_65 = lean::cnstr_get(x_56, 0);
lean::inc(x_65);
lean::dec(x_56);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
lean::dec(x_65);
if (lean::obj_tag(x_68) == 0)
{
obj* x_72; 
lean::dec(x_58);
x_72 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3;
x_50 = x_72;
goto lbl_51;
}
else
{
obj* x_73; obj* x_76; 
x_73 = lean::cnstr_get(x_68, 0);
lean::inc(x_73);
lean::dec(x_68);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
switch (lean::obj_tag(x_76)) {
case 0:
{
obj* x_79; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
lean::dec(x_76);
x_82 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_79);
x_83 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_83, 0, x_82);
if (lean::is_scalar(x_58)) {
 x_84 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_84 = x_58;
}
lean::cnstr_set(x_84, 0, x_83);
x_85 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
x_50 = x_85;
goto lbl_51;
}
case 2:
{
obj* x_86; obj* x_89; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_86 = lean::cnstr_get(x_76, 0);
lean::inc(x_86);
lean::dec(x_76);
x_89 = lean::cnstr_get(x_86, 2);
lean::inc(x_89);
lean::dec(x_86);
x_92 = l_lean_elaborator_prec__to__nat___main(x_89);
x_93 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_93, 0, x_92);
if (lean::is_scalar(x_58)) {
 x_94 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_94 = x_58;
}
lean::cnstr_set(x_94, 0, x_93);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
x_50 = x_95;
goto lbl_51;
}
default:
{
obj* x_98; 
lean::dec(x_76);
lean::dec(x_58);
x_98 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
x_50 = x_98;
goto lbl_51;
}
}
}
}
}
}
lbl_51:
{
if (lean::obj_tag(x_50) == 0)
{
obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_9);
x_100 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_set(x_50, 0, lean::box(0));
 x_102 = x_50;
} else {
 lean::inc(x_100);
 lean::dec(x_50);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
x_7 = x_103;
goto lbl_8;
}
else
{
obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_104 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_set(x_50, 0, lean::box(0));
 x_106 = x_50;
} else {
 lean::inc(x_104);
 lean::dec(x_50);
 x_106 = lean::box(0);
}
x_107 = l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(x_104);
x_108 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_108, 0, x_9);
lean::cnstr_set(x_108, 1, x_107);
if (lean::is_scalar(x_106)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_106;
}
lean::cnstr_set(x_109, 0, x_108);
x_7 = x_109;
goto lbl_8;
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
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_16 = x_8;
} else {
 lean::inc(x_14);
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
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_20 = x_8;
} else {
 lean::inc(x_18);
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
return x_29;
}
else
{
obj* x_30; obj* x_33; obj* x_36; 
x_30 = lean::cnstr_get(x_5, 0);
lean::inc(x_30);
lean::dec(x_5);
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
lean::dec(x_30);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_45; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_18);
lean::dec(x_20);
x_45 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5;
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_52; 
x_46 = lean::cnstr_get(x_36, 0);
lean::inc(x_46);
lean::dec(x_36);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_52 = l_string_trim(x_49);
x_21 = x_52;
goto lbl_22;
}
}
lbl_22:
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(x_18);
x_54 = l_list_join___main___rarg(x_53);
x_55 = lean::cnstr_get(x_1, 0);
lean::inc(x_55);
lean::dec(x_1);
if (lean::obj_tag(x_55) == 0)
{
obj* x_58; 
x_58 = lean::cnstr_get(x_3, 0);
lean::inc(x_58);
lean::dec(x_3);
if (lean::obj_tag(x_58) == 0)
{
obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_73; obj* x_76; obj* x_77; 
x_61 = lean::cnstr_get(x_2, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_2, 1);
lean::inc(x_63);
x_65 = lean::box(0);
x_66 = lean_name_mk_string(x_65, x_21);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1), 7, 2);
lean::closure_set(x_67, 0, x_0);
lean::closure_set(x_67, 1, x_54);
x_68 = l_lean_parser_token__map_insert___rarg(x_63, x_66, x_67);
x_69 = lean::cnstr_get(x_2, 2);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_2, 3);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_2, 4);
lean::inc(x_73);
lean::dec(x_2);
x_76 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_76, 0, x_61);
lean::cnstr_set(x_76, 1, x_68);
lean::cnstr_set(x_76, 2, x_69);
lean::cnstr_set(x_76, 3, x_71);
lean::cnstr_set(x_76, 4, x_73);
if (lean::is_scalar(x_20)) {
 x_77 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_77 = x_20;
}
lean::cnstr_set(x_77, 0, x_76);
return x_77;
}
else
{
obj* x_79; obj* x_81; obj* x_83; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_94; obj* x_97; obj* x_98; 
lean::dec(x_58);
x_79 = lean::cnstr_get(x_2, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_2, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_2, 2);
lean::inc(x_83);
x_85 = lean::box(0);
x_86 = lean_name_mk_string(x_85, x_21);
x_87 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(x_54);
x_88 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_87);
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3), 8, 2);
lean::closure_set(x_90, 0, x_0);
lean::closure_set(x_90, 1, x_89);
x_91 = l_lean_parser_token__map_insert___rarg(x_83, x_86, x_90);
x_92 = lean::cnstr_get(x_2, 3);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_2, 4);
lean::inc(x_94);
lean::dec(x_2);
x_97 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_97, 0, x_79);
lean::cnstr_set(x_97, 1, x_81);
lean::cnstr_set(x_97, 2, x_91);
lean::cnstr_set(x_97, 3, x_92);
lean::cnstr_set(x_97, 4, x_94);
if (lean::is_scalar(x_20)) {
 x_98 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_98 = x_20;
}
lean::cnstr_set(x_98, 0, x_97);
return x_98;
}
}
else
{
obj* x_100; 
lean::dec(x_55);
x_100 = lean::cnstr_get(x_3, 0);
lean::inc(x_100);
lean::dec(x_3);
if (lean::obj_tag(x_100) == 0)
{
obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_118; obj* x_119; 
x_103 = lean::cnstr_get(x_2, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_2, 1);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_2, 2);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_2, 3);
lean::inc(x_109);
x_111 = lean::box(0);
x_112 = lean_name_mk_string(x_111, x_21);
x_113 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1), 7, 2);
lean::closure_set(x_113, 0, x_0);
lean::closure_set(x_113, 1, x_54);
x_114 = l_lean_parser_token__map_insert___rarg(x_109, x_112, x_113);
x_115 = lean::cnstr_get(x_2, 4);
lean::inc(x_115);
lean::dec(x_2);
x_118 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_118, 0, x_103);
lean::cnstr_set(x_118, 1, x_105);
lean::cnstr_set(x_118, 2, x_107);
lean::cnstr_set(x_118, 3, x_114);
lean::cnstr_set(x_118, 4, x_115);
if (lean::is_scalar(x_20)) {
 x_119 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_119 = x_20;
}
lean::cnstr_set(x_119, 0, x_118);
return x_119;
}
else
{
obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_129; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
lean::dec(x_100);
x_121 = lean::cnstr_get(x_2, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_2, 1);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_2, 2);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_2, 3);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_2, 4);
lean::inc(x_129);
lean::dec(x_2);
x_132 = lean::box(0);
x_133 = lean_name_mk_string(x_132, x_21);
x_134 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(x_54);
x_135 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
x_136 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_134);
x_137 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3), 8, 2);
lean::closure_set(x_137, 0, x_0);
lean::closure_set(x_137, 1, x_136);
x_138 = l_lean_parser_token__map_insert___rarg(x_129, x_133, x_137);
x_139 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_139, 0, x_121);
lean::cnstr_set(x_139, 1, x_123);
lean::cnstr_set(x_139, 2, x_125);
lean::cnstr_set(x_139, 3, x_127);
lean::cnstr_set(x_139, 4, x_138);
if (lean::is_scalar(x_20)) {
 x_140 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_140 = x_20;
}
lean::cnstr_set(x_140, 0, x_139);
return x_140;
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
obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_24; 
x_15 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_17 = x_14;
} else {
 lean::inc(x_15);
 lean::dec(x_14);
 x_17 = lean::box(0);
}
x_18 = l_lean_parser_command_reserve__notation_has__view;
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_7);
lean::inc(x_2);
x_24 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_22, x_15, x_2, x_3);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_30; 
lean::dec(x_9);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
lean::dec(x_24);
if (lean::is_scalar(x_17)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_17;
}
lean::cnstr_set(x_30, 0, x_27);
return x_30;
}
else
{
obj* x_32; obj* x_35; obj* x_37; 
lean::dec(x_17);
x_32 = lean::cnstr_get(x_24, 0);
lean::inc(x_32);
lean::dec(x_24);
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
lean::dec(x_32);
x_0 = x_35;
x_1 = x_9;
x_3 = x_37;
goto _start;
}
}
else
{
obj* x_42; 
lean::dec(x_7);
x_42 = lean::cnstr_get(x_14, 0);
lean::inc(x_42);
lean::dec(x_14);
x_0 = x_42;
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
obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_25; obj* x_27; 
lean::dec(x_7);
x_18 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_20 = x_16;
} else {
 lean::inc(x_18);
 lean::dec(x_16);
 x_20 = lean::box(0);
}
x_21 = l_lean_parser_command_notation_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
x_25 = lean::apply_1(x_22, x_12);
lean::inc(x_2);
x_27 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_25, x_18, x_2, x_3);
if (lean::obj_tag(x_27) == 0)
{
obj* x_30; obj* x_33; 
lean::dec(x_9);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
lean::dec(x_27);
if (lean::is_scalar(x_20)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_20;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
lean::dec(x_20);
x_35 = lean::cnstr_get(x_27, 0);
lean::inc(x_35);
lean::dec(x_27);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
x_0 = x_38;
x_1 = x_9;
x_3 = x_40;
goto _start;
}
}
else
{
obj* x_44; obj* x_46; obj* x_47; obj* x_51; 
x_44 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_46 = x_16;
} else {
 lean::inc(x_44);
 lean::dec(x_16);
 x_46 = lean::box(0);
}
x_47 = lean::cnstr_get(x_7, 0);
lean::inc(x_47);
lean::dec(x_7);
lean::inc(x_12);
x_51 = l_lean_elaborator_command__parser__config_register__notation__parser(x_47, x_12, x_44);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_55; obj* x_56; obj* x_59; obj* x_61; 
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
lean::dec(x_51);
x_55 = l_lean_parser_command_notation_has__view;
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
lean::dec(x_55);
x_59 = lean::apply_1(x_56, x_12);
lean::inc(x_2);
x_61 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_59, x_52, x_2, x_3);
if (lean::obj_tag(x_61) == 0)
{
obj* x_64; obj* x_67; 
lean::dec(x_9);
lean::dec(x_2);
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
lean::dec(x_61);
if (lean::is_scalar(x_46)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_46;
 lean::cnstr_set_tag(x_46, 0);
}
lean::cnstr_set(x_67, 0, x_64);
return x_67;
}
else
{
obj* x_69; obj* x_72; obj* x_74; 
lean::dec(x_46);
x_69 = lean::cnstr_get(x_61, 0);
lean::inc(x_69);
lean::dec(x_61);
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
x_0 = x_72;
x_1 = x_9;
x_3 = x_74;
goto _start;
}
}
else
{
obj* x_80; 
lean::dec(x_12);
lean::dec(x_46);
x_80 = lean::cnstr_get(x_51, 0);
lean::inc(x_80);
lean::dec(x_51);
x_0 = x_80;
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 x_18 = x_11;
} else {
 lean::inc(x_16);
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 x_22 = x_11;
} else {
 lean::inc(x_20);
 lean::dec(x_11);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_20, 0);
x_25 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_set(x_20, 0, lean::box(0));
 lean::cnstr_set(x_20, 1, lean::box(0));
 x_27 = x_20;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
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
obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
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
x_25 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_25, 0, x_3);
lean::cnstr_set(x_25, 1, x_5);
lean::cnstr_set(x_25, 2, x_7);
lean::cnstr_set(x_25, 3, x_9);
lean::cnstr_set(x_25, 4, x_11);
lean::cnstr_set(x_25, 5, x_24);
lean::cnstr_set(x_25, 6, x_13);
lean::cnstr_set(x_25, 7, x_15);
lean::cnstr_set(x_25, 8, x_17);
lean::cnstr_set(x_25, 9, x_19);
lean::cnstr_set(x_25, 10, x_21);
x_26 = lean::box(0);
if (lean::is_scalar(x_2)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_2;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_29, 0, x_28);
return x_29;
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
obj* x_1; obj* x_3; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
lean::inc(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__3), 2, 1);
lean::closure_set(x_7, 0, x_1);
x_8 = l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___rarg___lambda__1), 2, 1);
lean::closure_set(x_13, 0, x_1);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_15, 0, x_12);
lean::closure_set(x_15, 1, x_14);
return x_15;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_lean_elaborator_yield__to__outside___rarg___closed__1;
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string(":");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = l_lean_parser_max__prec;
x_6 = l_lean_parser_number_view_of__nat(x_5);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
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
x_7 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_9 = x_3;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_set(x_5, 1, lean::box(0));
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_10, 0);
x_17 = lean::cnstr_get(x_10, 1);
x_19 = lean::cnstr_get(x_10, 2);
x_21 = lean::cnstr_get(x_10, 3);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 lean::cnstr_set(x_10, 3, lean::box(0));
 x_23 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_10);
 x_23 = lean::box(0);
}
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_25 = l_lean_elaborator_postprocess__notation__spec___closed__1;
if (lean::is_scalar(x_23)) {
 x_26 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_26 = x_23;
}
lean::cnstr_set(x_26, 0, x_15);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_19);
lean::cnstr_set(x_26, 3, x_25);
if (lean::is_scalar(x_14)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_14;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_12);
if (lean::is_scalar(x_9)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_9;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_7);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_1);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
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
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; obj* x_42; 
x_3 = l_lean_parser_command_reserve__notation_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 2);
lean::inc(x_12);
lean::dec(x_7);
x_15 = l_lean_elaborator_postprocess__notation__spec(x_12);
x_16 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_10);
lean::cnstr_set(x_16, 2, x_15);
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_17);
x_20 = lean::cnstr_get(x_2, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_2, 2);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_2, 3);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_2, 4);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_2, 5);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_2, 6);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_2, 7);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_2, 8);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_2, 9);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_2, 10);
lean::inc(x_38);
lean::dec(x_2);
x_41 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_41, 0, x_19);
lean::cnstr_set(x_41, 1, x_20);
lean::cnstr_set(x_41, 2, x_22);
lean::cnstr_set(x_41, 3, x_24);
lean::cnstr_set(x_41, 4, x_26);
lean::cnstr_set(x_41, 5, x_28);
lean::cnstr_set(x_41, 6, x_30);
lean::cnstr_set(x_41, 7, x_32);
lean::cnstr_set(x_41, 8, x_34);
lean::cnstr_set(x_41, 9, x_36);
lean::cnstr_set(x_41, 10, x_38);
x_42 = l_lean_elaborator_update__parser__config(x_1, x_41);
return x_42;
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
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_18; 
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
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_14, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_14, 3);
lean::inc(x_18);
lean::dec(x_14);
if (lean::obj_tag(x_16) == 0)
{
obj* x_26; 
lean::dec(x_18);
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_9);
lean::dec(x_4);
x_26 = lean::box(0);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; 
x_27 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_29 = x_16;
} else {
 lean::inc(x_27);
 lean::dec(x_16);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_11, 0);
lean::inc(x_30);
x_36 = lean::cnstr_get(x_30, 1);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_30, 3);
lean::inc(x_38);
if (lean::obj_tag(x_36) == 0)
{
obj* x_47; 
lean::dec(x_18);
lean::dec(x_11);
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_38);
lean::dec(x_27);
x_47 = lean::box(0);
x_7 = x_47;
goto lbl_8;
}
else
{
obj* x_48; obj* x_51; obj* x_54; obj* x_55; obj* x_58; uint8 x_59; 
x_48 = lean::cnstr_get(x_36, 0);
lean::inc(x_48);
lean::dec(x_36);
x_51 = lean::cnstr_get(x_27, 1);
lean::inc(x_51);
lean::dec(x_27);
x_54 = l_string_trim(x_51);
x_55 = lean::cnstr_get(x_48, 1);
lean::inc(x_55);
lean::dec(x_48);
x_58 = l_string_trim(x_55);
x_59 = lean::string_dec_eq(x_54, x_58);
lean::dec(x_58);
lean::dec(x_54);
if (x_59 == 0)
{
obj* x_68; 
lean::dec(x_18);
lean::dec(x_11);
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_38);
x_68 = lean::box(0);
x_7 = x_68;
goto lbl_8;
}
else
{
uint8 x_69; 
x_69 = l_lean_elaborator_match__precedence___main(x_18, x_38);
if (x_69 == 0)
{
obj* x_74; 
lean::dec(x_11);
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_9);
x_74 = lean::box(0);
x_7 = x_74;
goto lbl_8;
}
else
{
obj* x_75; 
x_75 = lean::box(0);
x_34 = x_75;
goto lbl_35;
}
}
}
lbl_33:
{
if (lean::obj_tag(x_32) == 0)
{
obj* x_78; 
lean::dec(x_29);
lean::dec(x_30);
x_78 = lean::box(0);
x_7 = x_78;
goto lbl_8;
}
else
{
obj* x_79; obj* x_82; obj* x_83; 
x_79 = lean::cnstr_get(x_32, 0);
lean::inc(x_79);
lean::dec(x_32);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_30);
lean::cnstr_set(x_82, 1, x_79);
if (lean::is_scalar(x_29)) {
 x_83 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_83 = x_29;
}
lean::cnstr_set(x_83, 0, x_82);
x_7 = x_83;
goto lbl_8;
}
}
lbl_35:
{
obj* x_85; 
lean::dec(x_34);
x_85 = lean::cnstr_get(x_9, 1);
lean::inc(x_85);
lean::dec(x_9);
if (lean::obj_tag(x_85) == 0)
{
obj* x_88; 
x_88 = lean::cnstr_get(x_11, 1);
lean::inc(x_88);
lean::dec(x_11);
if (lean::obj_tag(x_88) == 0)
{
obj* x_91; 
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_88);
x_32 = x_91;
goto lbl_33;
}
else
{
obj* x_93; 
lean::dec(x_88);
x_93 = lean::box(0);
x_32 = x_93;
goto lbl_33;
}
}
else
{
obj* x_94; obj* x_96; 
x_94 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_set(x_85, 0, lean::box(0));
 x_96 = x_85;
} else {
 lean::inc(x_94);
 lean::dec(x_85);
 x_96 = lean::box(0);
}
switch (lean::obj_tag(x_94)) {
case 0:
{
obj* x_97; obj* x_100; 
x_97 = lean::cnstr_get(x_94, 0);
lean::inc(x_97);
lean::dec(x_94);
x_100 = lean::cnstr_get(x_11, 1);
lean::inc(x_100);
lean::dec(x_11);
if (lean::obj_tag(x_100) == 0)
{
obj* x_105; 
lean::dec(x_97);
lean::dec(x_96);
x_105 = lean::box(0);
x_32 = x_105;
goto lbl_33;
}
else
{
obj* x_106; 
x_106 = lean::cnstr_get(x_100, 0);
lean::inc(x_106);
switch (lean::obj_tag(x_106)) {
case 0:
{
obj* x_108; obj* x_111; obj* x_114; uint8 x_117; 
x_108 = lean::cnstr_get(x_106, 0);
lean::inc(x_108);
lean::dec(x_106);
x_111 = lean::cnstr_get(x_97, 1);
lean::inc(x_111);
lean::dec(x_97);
x_114 = lean::cnstr_get(x_108, 1);
lean::inc(x_114);
lean::dec(x_108);
x_117 = l_lean_elaborator_match__precedence___main(x_111, x_114);
if (x_117 == 0)
{
obj* x_120; 
lean::dec(x_100);
lean::dec(x_96);
x_120 = lean::box(0);
x_32 = x_120;
goto lbl_33;
}
else
{
obj* x_121; 
if (lean::is_scalar(x_96)) {
 x_121 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_121 = x_96;
}
lean::cnstr_set(x_121, 0, x_100);
x_32 = x_121;
goto lbl_33;
}
}
default:
{
obj* x_126; 
lean::dec(x_97);
lean::dec(x_100);
lean::dec(x_106);
lean::dec(x_96);
x_126 = lean::box(0);
x_32 = x_126;
goto lbl_33;
}
}
}
}
case 1:
{
obj* x_127; obj* x_130; 
x_127 = lean::cnstr_get(x_94, 0);
lean::inc(x_127);
lean::dec(x_94);
x_130 = lean::cnstr_get(x_11, 1);
lean::inc(x_130);
lean::dec(x_11);
if (lean::obj_tag(x_130) == 0)
{
obj* x_135; 
lean::dec(x_96);
lean::dec(x_127);
x_135 = lean::box(0);
x_32 = x_135;
goto lbl_33;
}
else
{
obj* x_136; 
x_136 = lean::cnstr_get(x_130, 0);
lean::inc(x_136);
switch (lean::obj_tag(x_136)) {
case 1:
{
obj* x_138; obj* x_141; obj* x_144; uint8 x_147; 
x_138 = lean::cnstr_get(x_136, 0);
lean::inc(x_138);
lean::dec(x_136);
x_141 = lean::cnstr_get(x_127, 1);
lean::inc(x_141);
lean::dec(x_127);
x_144 = lean::cnstr_get(x_138, 1);
lean::inc(x_144);
lean::dec(x_138);
x_147 = l_lean_elaborator_match__precedence___main(x_141, x_144);
if (x_147 == 0)
{
obj* x_150; 
lean::dec(x_96);
lean::dec(x_130);
x_150 = lean::box(0);
x_32 = x_150;
goto lbl_33;
}
else
{
obj* x_151; 
if (lean::is_scalar(x_96)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_96;
}
lean::cnstr_set(x_151, 0, x_130);
x_32 = x_151;
goto lbl_33;
}
}
default:
{
obj* x_156; 
lean::dec(x_96);
lean::dec(x_127);
lean::dec(x_130);
lean::dec(x_136);
x_156 = lean::box(0);
x_32 = x_156;
goto lbl_33;
}
}
}
}
default:
{
obj* x_157; obj* x_159; obj* x_160; obj* x_162; 
x_157 = lean::cnstr_get(x_94, 0);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_set(x_94, 0, lean::box(0));
 x_159 = x_94;
} else {
 lean::inc(x_157);
 lean::dec(x_94);
 x_159 = lean::box(0);
}
x_162 = lean::cnstr_get(x_11, 1);
lean::inc(x_162);
lean::dec(x_11);
if (lean::obj_tag(x_162) == 0)
{
obj* x_168; 
lean::dec(x_157);
lean::dec(x_159);
lean::dec(x_96);
x_168 = lean::box(0);
x_32 = x_168;
goto lbl_33;
}
else
{
obj* x_169; obj* x_171; 
x_169 = lean::cnstr_get(x_162, 0);
if (lean::is_exclusive(x_162)) {
 lean::cnstr_set(x_162, 0, lean::box(0));
 x_171 = x_162;
} else {
 lean::inc(x_169);
 lean::dec(x_162);
 x_171 = lean::box(0);
}
switch (lean::obj_tag(x_169)) {
case 2:
{
obj* x_172; obj* x_175; obj* x_177; obj* x_179; 
x_172 = lean::cnstr_get(x_169, 0);
lean::inc(x_172);
lean::dec(x_169);
x_175 = lean::cnstr_get(x_157, 1);
lean::inc(x_175);
x_177 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1;
lean::inc(x_175);
x_179 = l_option_map___rarg(x_177, x_175);
if (lean::obj_tag(x_179) == 0)
{
obj* x_181; obj* x_185; 
lean::dec(x_175);
x_181 = lean::cnstr_get(x_172, 1);
lean::inc(x_181);
lean::dec(x_172);
lean::inc(x_181);
x_185 = l_option_map___rarg(x_177, x_181);
if (lean::obj_tag(x_185) == 0)
{
obj* x_188; 
lean::dec(x_181);
lean::dec(x_171);
x_188 = lean::box(0);
x_160 = x_188;
goto lbl_161;
}
else
{
obj* x_189; 
x_189 = lean::cnstr_get(x_185, 0);
lean::inc(x_189);
lean::dec(x_185);
switch (lean::obj_tag(x_189)) {
case 0:
{
obj* x_193; 
lean::dec(x_189);
if (lean::is_scalar(x_171)) {
 x_193 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_193 = x_171;
}
lean::cnstr_set(x_193, 0, x_181);
x_160 = x_193;
goto lbl_161;
}
default:
{
obj* x_197; 
lean::dec(x_189);
lean::dec(x_181);
lean::dec(x_171);
x_197 = lean::box(0);
x_160 = x_197;
goto lbl_161;
}
}
}
}
else
{
obj* x_198; 
x_198 = lean::cnstr_get(x_179, 0);
lean::inc(x_198);
lean::dec(x_179);
switch (lean::obj_tag(x_198)) {
case 0:
{
obj* x_201; obj* x_204; obj* x_207; 
x_201 = lean::cnstr_get(x_198, 0);
lean::inc(x_201);
lean::dec(x_198);
x_204 = lean::cnstr_get(x_172, 1);
lean::inc(x_204);
lean::dec(x_172);
x_207 = l_option_map___rarg(x_177, x_204);
if (lean::obj_tag(x_207) == 0)
{
obj* x_211; 
lean::dec(x_201);
lean::dec(x_171);
lean::dec(x_175);
x_211 = lean::box(0);
x_160 = x_211;
goto lbl_161;
}
else
{
obj* x_212; 
x_212 = lean::cnstr_get(x_207, 0);
lean::inc(x_212);
lean::dec(x_207);
switch (lean::obj_tag(x_212)) {
case 0:
{
obj* x_215; obj* x_218; obj* x_219; uint8 x_220; 
x_215 = lean::cnstr_get(x_212, 0);
lean::inc(x_215);
lean::dec(x_212);
x_218 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_201);
x_219 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_215);
x_220 = lean::nat_dec_eq(x_218, x_219);
lean::dec(x_219);
lean::dec(x_218);
if (x_220 == 0)
{
obj* x_225; 
lean::dec(x_171);
lean::dec(x_175);
x_225 = lean::box(0);
x_160 = x_225;
goto lbl_161;
}
else
{
obj* x_226; 
if (lean::is_scalar(x_171)) {
 x_226 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_226 = x_171;
}
lean::cnstr_set(x_226, 0, x_175);
x_160 = x_226;
goto lbl_161;
}
}
default:
{
obj* x_231; 
lean::dec(x_212);
lean::dec(x_201);
lean::dec(x_171);
lean::dec(x_175);
x_231 = lean::box(0);
x_160 = x_231;
goto lbl_161;
}
}
}
}
default:
{
obj* x_236; 
lean::dec(x_172);
lean::dec(x_198);
lean::dec(x_171);
lean::dec(x_175);
x_236 = lean::box(0);
x_160 = x_236;
goto lbl_161;
}
}
}
}
default:
{
obj* x_242; 
lean::dec(x_157);
lean::dec(x_171);
lean::dec(x_159);
lean::dec(x_169);
lean::dec(x_96);
x_242 = lean::box(0);
x_32 = x_242;
goto lbl_33;
}
}
}
lbl_161:
{
if (lean::obj_tag(x_160) == 0)
{
obj* x_246; 
lean::dec(x_157);
lean::dec(x_159);
lean::dec(x_96);
x_246 = lean::box(0);
x_32 = x_246;
goto lbl_33;
}
else
{
obj* x_247; obj* x_249; obj* x_250; obj* x_253; obj* x_254; obj* x_255; obj* x_256; 
x_247 = lean::cnstr_get(x_160, 0);
if (lean::is_exclusive(x_160)) {
 lean::cnstr_set(x_160, 0, lean::box(0));
 x_249 = x_160;
} else {
 lean::inc(x_247);
 lean::dec(x_160);
 x_249 = lean::box(0);
}
x_250 = lean::cnstr_get(x_157, 0);
lean::inc(x_250);
lean::dec(x_157);
x_253 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_253, 0, x_250);
lean::cnstr_set(x_253, 1, x_247);
if (lean::is_scalar(x_159)) {
 x_254 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_254 = x_159;
}
lean::cnstr_set(x_254, 0, x_253);
if (lean::is_scalar(x_96)) {
 x_255 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_255 = x_96;
}
lean::cnstr_set(x_255, 0, x_254);
if (lean::is_scalar(x_249)) {
 x_256 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_256 = x_249;
}
lean::cnstr_set(x_256, 0, x_255);
x_32 = x_256;
goto lbl_33;
}
}
}
}
}
}
}
lbl_8:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_259; 
lean::dec(x_6);
lean::dec(x_4);
x_259 = lean::box(0);
return x_259;
}
else
{
obj* x_260; obj* x_262; obj* x_263; 
x_260 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_262 = x_7;
} else {
 lean::inc(x_260);
 lean::dec(x_7);
 x_262 = lean::box(0);
}
x_263 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(x_4);
if (lean::obj_tag(x_263) == 0)
{
obj* x_267; 
lean::dec(x_260);
lean::dec(x_6);
lean::dec(x_262);
x_267 = lean::box(0);
return x_267;
}
else
{
obj* x_268; obj* x_271; obj* x_272; 
x_268 = lean::cnstr_get(x_263, 0);
lean::inc(x_268);
lean::dec(x_263);
if (lean::is_scalar(x_6)) {
 x_271 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_271 = x_6;
}
lean::cnstr_set(x_271, 0, x_260);
lean::cnstr_set(x_271, 1, x_268);
if (lean::is_scalar(x_262)) {
 x_272 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_272 = x_262;
}
lean::cnstr_set(x_272, 0, x_271);
return x_272;
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
obj* x_22; obj* x_25; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_4);
x_22 = lean::cnstr_get(x_0, 1);
lean::inc(x_22);
lean::dec(x_0);
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
lean::dec(x_1);
x_28 = l_lean_elaborator_match__spec___closed__1;
x_29 = l_list_zip__with___main___rarg(x_28, x_22, x_25);
x_30 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_32; 
lean::dec(x_2);
x_32 = lean::box(0);
return x_32;
}
else
{
obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_set(x_30, 0, lean::box(0));
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_2);
lean::cnstr_set(x_36, 1, x_33);
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_36);
return x_37;
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
obj* x_45; obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_24);
lean::dec(x_26);
x_45 = l_lean_parser_command_notation_has__view;
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
lean::dec(x_45);
x_49 = lean::apply_1(x_46, x_0);
x_50 = l_lean_elaborator_notation_elaborate__aux___closed__1;
x_51 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_49, x_50, x_1, x_2);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 x_54 = x_51;
} else {
 lean::inc(x_52);
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
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 x_58 = x_51;
} else {
 lean::inc(x_56);
 lean::dec(x_51);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_56, 0);
x_61 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_set(x_56, 0, lean::box(0));
 lean::cnstr_set(x_56, 1, lean::box(0));
 x_63 = x_56;
} else {
 lean::inc(x_59);
 lean::inc(x_61);
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
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
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
x_28 = lean_name_mk_numeral(x_27, x_5);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_26);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_8 = x_4;
} else {
 lean::inc(x_6);
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 x_17 = x_10;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
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
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; uint8 x_15; 
x_3 = l_lean_parser_command_notation_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_10 = lean::cnstr_get(x_7, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
lean::dec(x_10);
x_15 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_12);
if (x_15 == 0)
{
obj* x_16; 
x_16 = lean::box(0);
x_8 = x_16;
goto lbl_9;
}
else
{
obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_31; obj* x_34; obj* x_35; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_7);
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_2, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_2, 2);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_2, 3);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_2, 4);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
x_34 = lean::box(0);
x_35 = l_lean_elaborator_notation_elaborate___closed__1;
x_36 = 1;
x_37 = l_string_join___closed__1;
x_38 = l_lean_elaborator_notation_elaborate___closed__2;
x_39 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_39, 0, x_31);
lean::cnstr_set(x_39, 1, x_35);
lean::cnstr_set(x_39, 2, x_34);
lean::cnstr_set(x_39, 3, x_37);
lean::cnstr_set(x_39, 4, x_38);
lean::cnstr_set_scalar(x_39, sizeof(void*)*5, x_36);
x_40 = x_39;
x_41 = lean::cnstr_get(x_2, 5);
lean::inc(x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_41);
x_44 = lean::cnstr_get(x_2, 6);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_2, 7);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_2, 8);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_2, 9);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_2, 10);
lean::inc(x_52);
lean::dec(x_2);
x_55 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_55, 0, x_18);
lean::cnstr_set(x_55, 1, x_20);
lean::cnstr_set(x_55, 2, x_22);
lean::cnstr_set(x_55, 3, x_24);
lean::cnstr_set(x_55, 4, x_26);
lean::cnstr_set(x_55, 5, x_43);
lean::cnstr_set(x_55, 6, x_44);
lean::cnstr_set(x_55, 7, x_46);
lean::cnstr_set(x_55, 8, x_48);
lean::cnstr_set(x_55, 9, x_50);
lean::cnstr_set(x_55, 10, x_52);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_34);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
lbl_9:
{
obj* x_60; 
lean::dec(x_8);
lean::inc(x_1);
x_60 = l_lean_elaborator_notation_elaborate__aux(x_7, x_1, x_2);
if (lean::obj_tag(x_60) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_1);
x_62 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_set(x_60, 0, lean::box(0));
 x_64 = x_60;
} else {
 lean::inc(x_62);
 lean::dec(x_60);
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
obj* x_66; obj* x_68; obj* x_69; obj* x_71; obj* x_76; 
x_66 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_set(x_60, 0, lean::box(0));
 x_68 = x_60;
} else {
 lean::inc(x_66);
 lean::dec(x_60);
 x_68 = lean::box(0);
}
x_69 = lean::cnstr_get(x_66, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
lean::dec(x_66);
lean::inc(x_1);
lean::inc(x_69);
x_76 = l_lean_elaborator_register__notation__macro(x_69, x_1, x_71);
if (lean::obj_tag(x_76) == 0)
{
obj* x_79; obj* x_82; 
lean::dec(x_1);
lean::dec(x_69);
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
lean::dec(x_76);
if (lean::is_scalar(x_68)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_68;
 lean::cnstr_set_tag(x_68, 0);
}
lean::cnstr_set(x_82, 0, x_79);
return x_82;
}
else
{
obj* x_84; obj* x_87; obj* x_89; obj* x_92; 
lean::dec(x_68);
x_84 = lean::cnstr_get(x_76, 0);
lean::inc(x_84);
lean::dec(x_76);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = lean::cnstr_get(x_69, 0);
lean::inc(x_92);
lean::dec(x_69);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_119; obj* x_120; 
x_95 = lean::cnstr_get(x_89, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_89, 1);
lean::inc(x_97);
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_87);
lean::cnstr_set(x_99, 1, x_97);
x_100 = lean::cnstr_get(x_89, 2);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_89, 3);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_89, 4);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_89, 5);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_89, 6);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_89, 7);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_89, 8);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_89, 9);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_89, 10);
lean::inc(x_116);
lean::dec(x_89);
x_119 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_119, 0, x_95);
lean::cnstr_set(x_119, 1, x_99);
lean::cnstr_set(x_119, 2, x_100);
lean::cnstr_set(x_119, 3, x_102);
lean::cnstr_set(x_119, 4, x_104);
lean::cnstr_set(x_119, 5, x_106);
lean::cnstr_set(x_119, 6, x_108);
lean::cnstr_set(x_119, 7, x_110);
lean::cnstr_set(x_119, 8, x_112);
lean::cnstr_set(x_119, 9, x_114);
lean::cnstr_set(x_119, 10, x_116);
x_120 = l_lean_elaborator_update__parser__config(x_1, x_119);
return x_120;
}
else
{
obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_148; obj* x_149; obj* x_151; obj* x_153; obj* x_155; obj* x_157; obj* x_159; obj* x_162; obj* x_163; 
lean::dec(x_92);
x_122 = lean::cnstr_get(x_89, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_89, 1);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_89, 2);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_89, 3);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_89, 4);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_130, 0);
lean::inc(x_132);
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_87);
lean::cnstr_set(x_134, 1, x_132);
x_135 = lean::cnstr_get(x_130, 1);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_130, 2);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_130, 3);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_130, 4);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_130, 5);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_130, 6);
lean::inc(x_145);
lean::dec(x_130);
x_148 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_148, 0, x_134);
lean::cnstr_set(x_148, 1, x_135);
lean::cnstr_set(x_148, 2, x_137);
lean::cnstr_set(x_148, 3, x_139);
lean::cnstr_set(x_148, 4, x_141);
lean::cnstr_set(x_148, 5, x_143);
lean::cnstr_set(x_148, 6, x_145);
x_149 = lean::cnstr_get(x_89, 5);
lean::inc(x_149);
x_151 = lean::cnstr_get(x_89, 6);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_89, 7);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_89, 8);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_89, 9);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_89, 10);
lean::inc(x_159);
lean::dec(x_89);
x_162 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_162, 0, x_122);
lean::cnstr_set(x_162, 1, x_124);
lean::cnstr_set(x_162, 2, x_126);
lean::cnstr_set(x_162, 3, x_128);
lean::cnstr_set(x_162, 4, x_148);
lean::cnstr_set(x_162, 5, x_149);
lean::cnstr_set(x_162, 6, x_151);
lean::cnstr_set(x_162, 7, x_153);
lean::cnstr_set(x_162, 8, x_155);
lean::cnstr_set(x_162, 9, x_157);
lean::cnstr_set(x_162, 10, x_159);
x_163 = l_lean_elaborator_update__parser__config(x_1, x_162);
return x_163;
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
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_19; 
x_3 = l_lean_parser_command_universe_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
lean::inc(x_0);
x_8 = lean::apply_1(x_4, x_0);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = l_lean_elaborator_mangle__ident(x_9);
x_13 = lean::cnstr_get(x_2, 4);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
lean::inc(x_12);
lean::inc(x_15);
x_19 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_15, x_12);
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_1);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_2, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_2, 2);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_2, 3);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_13, 0);
lean::inc(x_30);
lean::inc(x_12);
x_33 = level_mk_param(x_12);
x_34 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_15, x_12, x_33);
x_35 = lean::cnstr_get(x_13, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_13, 3);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_13, 4);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_13, 5);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_13, 6);
lean::inc(x_43);
lean::dec(x_13);
x_46 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_46, 0, x_30);
lean::cnstr_set(x_46, 1, x_34);
lean::cnstr_set(x_46, 2, x_35);
lean::cnstr_set(x_46, 3, x_37);
lean::cnstr_set(x_46, 4, x_39);
lean::cnstr_set(x_46, 5, x_41);
lean::cnstr_set(x_46, 6, x_43);
x_47 = lean::cnstr_get(x_2, 5);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_2, 6);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_2, 7);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_2, 8);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_2, 9);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_2, 10);
lean::inc(x_57);
lean::dec(x_2);
x_60 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_60, 0, x_22);
lean::cnstr_set(x_60, 1, x_24);
lean::cnstr_set(x_60, 2, x_26);
lean::cnstr_set(x_60, 3, x_28);
lean::cnstr_set(x_60, 4, x_46);
lean::cnstr_set(x_60, 5, x_47);
lean::cnstr_set(x_60, 6, x_49);
lean::cnstr_set(x_60, 7, x_51);
lean::cnstr_set(x_60, 8, x_53);
lean::cnstr_set(x_60, 9, x_55);
lean::cnstr_set(x_60, 10, x_57);
x_61 = lean::box(0);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_60);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
return x_63;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_19);
x_67 = l_lean_name_to__string___closed__1;
x_68 = l_lean_name_to__string__with__sep___main(x_67, x_12);
x_69 = l_lean_elaborator_universe_elaborate___closed__1;
x_70 = lean::string_append(x_69, x_68);
lean::dec(x_68);
x_72 = l_lean_elaborator_universe_elaborate___closed__2;
x_73 = lean::string_append(x_70, x_72);
x_74 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_73, x_1, x_2);
return x_74;
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_0);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; 
lean::inc(x_7);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_7);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
lean::dec(x_7);
x_19 = l_lean_name_to__string___closed__1;
x_20 = l_lean_name_to__string__with__sep___main(x_19, x_16);
x_21 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_24 = l_char_has__repr___closed__1;
x_25 = lean::string_append(x_22, x_24);
lean::inc(x_1);
x_27 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_15, x_25, x_1, x_2);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_31 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_set(x_27, 0, lean::box(0));
 x_33 = x_27;
} else {
 lean::inc(x_31);
 lean::dec(x_27);
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
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; 
x_35 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_set(x_27, 0, lean::box(0));
 x_37 = x_27;
} else {
 lean::inc(x_35);
 lean::dec(x_27);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_35, 0);
x_40 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_set(x_35, 0, lean::box(0));
 lean::cnstr_set(x_35, 1, lean::box(0));
 x_42 = x_35;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_35);
 x_42 = lean::box(0);
}
x_43 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_9, x_1, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; obj* x_50; 
lean::dec(x_11);
lean::dec(x_38);
lean::dec(x_42);
x_47 = lean::cnstr_get(x_43, 0);
lean::inc(x_47);
lean::dec(x_43);
if (lean::is_scalar(x_37)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_37;
 lean::cnstr_set_tag(x_37, 0);
}
lean::cnstr_set(x_50, 0, x_47);
return x_50;
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_61; 
x_51 = lean::cnstr_get(x_43, 0);
lean::inc(x_51);
lean::dec(x_43);
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
if (lean::is_scalar(x_11)) {
 x_59 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_59 = x_11;
}
lean::cnstr_set(x_59, 0, x_38);
lean::cnstr_set(x_59, 1, x_54);
if (lean::is_scalar(x_42)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_42;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_56);
if (lean::is_scalar(x_37)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_37;
}
lean::cnstr_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
obj* x_62; obj* x_64; 
x_62 = lean::cnstr_get(x_12, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_12, 1);
lean::inc(x_64);
lean::dec(x_12);
if (lean::obj_tag(x_64) == 0)
{
obj* x_68; 
lean::dec(x_7);
x_68 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_9, x_1, x_2);
if (lean::obj_tag(x_68) == 0)
{
obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_11);
lean::dec(x_62);
x_71 = lean::cnstr_get(x_68, 0);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_set(x_68, 0, lean::box(0));
 x_73 = x_68;
} else {
 lean::inc(x_71);
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
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_75 = lean::cnstr_get(x_68, 0);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_set(x_68, 0, lean::box(0));
 x_77 = x_68;
} else {
 lean::inc(x_75);
 lean::dec(x_68);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 0);
x_80 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 lean::cnstr_set(x_75, 1, lean::box(0));
 x_82 = x_75;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_75);
 x_82 = lean::box(0);
}
x_83 = lean::box(0);
x_84 = lean_expr_mk_const(x_62, x_83);
if (lean::is_scalar(x_11)) {
 x_85 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_85 = x_11;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_78);
if (lean::is_scalar(x_82)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_82;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_80);
if (lean::is_scalar(x_77)) {
 x_87 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_87 = x_77;
}
lean::cnstr_set(x_87, 0, x_86);
return x_87;
}
}
else
{
obj* x_90; obj* x_91; obj* x_93; 
lean::dec(x_62);
lean::dec(x_64);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_7);
x_91 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
lean::inc(x_1);
x_93 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_90, x_91, x_1, x_2);
if (lean::obj_tag(x_93) == 0)
{
obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
x_97 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_set(x_93, 0, lean::box(0));
 x_99 = x_93;
} else {
 lean::inc(x_97);
 lean::dec(x_93);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_97);
return x_100;
}
else
{
obj* x_101; obj* x_103; obj* x_104; obj* x_106; obj* x_108; obj* x_109; 
x_101 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_set(x_93, 0, lean::box(0));
 x_103 = x_93;
} else {
 lean::inc(x_101);
 lean::dec(x_93);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get(x_101, 0);
x_106 = lean::cnstr_get(x_101, 1);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_set(x_101, 0, lean::box(0));
 lean::cnstr_set(x_101, 1, lean::box(0));
 x_108 = x_101;
} else {
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_101);
 x_108 = lean::box(0);
}
x_109 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_9, x_1, x_106);
if (lean::obj_tag(x_109) == 0)
{
obj* x_113; obj* x_116; 
lean::dec(x_11);
lean::dec(x_108);
lean::dec(x_104);
x_113 = lean::cnstr_get(x_109, 0);
lean::inc(x_113);
lean::dec(x_109);
if (lean::is_scalar(x_103)) {
 x_116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_116 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_116, 0, x_113);
return x_116;
}
else
{
obj* x_117; obj* x_120; obj* x_122; obj* x_125; obj* x_126; obj* x_127; 
x_117 = lean::cnstr_get(x_109, 0);
lean::inc(x_117);
lean::dec(x_109);
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
lean::dec(x_117);
if (lean::is_scalar(x_11)) {
 x_125 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_125 = x_11;
}
lean::cnstr_set(x_125, 0, x_104);
lean::cnstr_set(x_125, 1, x_120);
if (lean::is_scalar(x_108)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_108;
}
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_122);
if (lean::is_scalar(x_103)) {
 x_127 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_127 = x_103;
}
lean::cnstr_set(x_127, 0, x_126);
return x_127;
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
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_12; 
x_3 = l_lean_parser_command_attribute_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
lean::inc(x_0);
x_8 = lean::apply_1(x_4, x_0);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
lean::inc(x_1);
x_12 = l_lean_elaborator_attrs__to__pexpr(x_9, x_1, x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 x_18 = x_12;
} else {
 lean::inc(x_16);
 lean::dec(x_12);
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
obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_28; obj* x_31; 
x_20 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 x_22 = x_12;
} else {
 lean::inc(x_20);
 lean::dec(x_12);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
lean::dec(x_20);
x_28 = lean::cnstr_get(x_8, 5);
lean::inc(x_28);
lean::inc(x_1);
x_31 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_28, x_1, x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_36; obj* x_39; 
lean::dec(x_8);
lean::dec(x_23);
lean::dec(x_1);
lean::dec(x_0);
x_36 = lean::cnstr_get(x_31, 0);
lean::inc(x_36);
lean::dec(x_31);
if (lean::is_scalar(x_22)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_22;
 lean::cnstr_set_tag(x_22, 0);
}
lean::cnstr_set(x_39, 0, x_36);
return x_39;
}
else
{
obj* x_41; obj* x_44; obj* x_46; obj* x_49; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_22);
x_41 = lean::cnstr_get(x_31, 0);
lean::inc(x_41);
lean::dec(x_31);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
lean::dec(x_41);
x_49 = lean::cnstr_get(x_8, 0);
lean::inc(x_49);
lean::dec(x_8);
x_52 = l_option_is__some___main___rarg(x_49);
x_53 = l_lean_elaborator_attribute_elaborate___closed__1;
x_54 = l_lean_elaborator_attribute_elaborate___closed__2;
x_55 = l_lean_kvmap_set__bool(x_53, x_54, x_52);
x_56 = l_lean_elaborator_mk__eqns___closed__1;
x_57 = l_lean_expr_mk__capp(x_56, x_44);
x_58 = lean_expr_mk_app(x_23, x_57);
x_59 = lean_expr_mk_mdata(x_55, x_58);
x_60 = l_lean_elaborator_old__elab__command(x_0, x_59, x_1, x_46);
return x_60;
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
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_13; 
x_3 = l_lean_parser_command_check_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
lean::inc(x_0);
x_8 = lean::apply_1(x_4, x_0);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
lean::inc(x_1);
x_13 = l_lean_elaborator_to__pexpr___main(x_9, x_1, x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_1);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_18 = x_13;
} else {
 lean::inc(x_16);
 lean::dec(x_13);
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
obj* x_20; obj* x_23; obj* x_25; obj* x_28; obj* x_29; obj* x_30; 
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
lean::dec(x_13);
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
lean::dec(x_20);
x_28 = l_lean_elaborator_check_elaborate___closed__1;
x_29 = lean_expr_mk_mdata(x_28, x_23);
x_30 = l_lean_elaborator_old__elab__command(x_0, x_29, x_1, x_25);
return x_30;
}
}
}
obj* l_lean_elaborator_open_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_34; obj* x_35; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_1);
x_4 = l_lean_parser_command_open_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 2);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 3);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_2, 4);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_17, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_17, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_17, 3);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_17, 4);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_17, 5);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_8, 1);
lean::inc(x_31);
lean::dec(x_8);
x_34 = l_list_append___rarg(x_29, x_31);
x_35 = lean::cnstr_get(x_17, 6);
lean::inc(x_35);
lean::dec(x_17);
x_38 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_38, 0, x_19);
lean::cnstr_set(x_38, 1, x_21);
lean::cnstr_set(x_38, 2, x_23);
lean::cnstr_set(x_38, 3, x_25);
lean::cnstr_set(x_38, 4, x_27);
lean::cnstr_set(x_38, 5, x_34);
lean::cnstr_set(x_38, 6, x_35);
x_39 = lean::cnstr_get(x_2, 5);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_2, 6);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_2, 7);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_2, 8);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_2, 9);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_2, 10);
lean::inc(x_49);
lean::dec(x_2);
x_52 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_52, 0, x_9);
lean::cnstr_set(x_52, 1, x_11);
lean::cnstr_set(x_52, 2, x_13);
lean::cnstr_set(x_52, 3, x_15);
lean::cnstr_set(x_52, 4, x_38);
lean::cnstr_set(x_52, 5, x_39);
lean::cnstr_set(x_52, 6, x_41);
lean::cnstr_set(x_52, 7, x_43);
lean::cnstr_set(x_52, 8, x_45);
lean::cnstr_set(x_52, 9, x_47);
lean::cnstr_set(x_52, 10, x_49);
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
return x_55;
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_8 = x_4;
} else {
 lean::inc(x_6);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 x_17 = x_10;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
x_18 = l_lean_parser_command_export_has__view;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_0);
x_23 = lean::cnstr_get(x_15, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_15, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_15, 2);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_15, 3);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_22, 1);
lean::inc(x_31);
lean::dec(x_22);
x_34 = l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(x_13, x_31);
x_35 = l_list_append___rarg(x_29, x_34);
x_36 = lean::cnstr_get(x_15, 4);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_15, 5);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_15, 6);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_15, 7);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_15, 8);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_15, 9);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_15, 10);
lean::inc(x_48);
lean::dec(x_15);
x_51 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_51, 0, x_23);
lean::cnstr_set(x_51, 1, x_25);
lean::cnstr_set(x_51, 2, x_27);
lean::cnstr_set(x_51, 3, x_35);
lean::cnstr_set(x_51, 4, x_36);
lean::cnstr_set(x_51, 5, x_38);
lean::cnstr_set(x_51, 6, x_40);
lean::cnstr_set(x_51, 7, x_42);
lean::cnstr_set(x_51, 8, x_44);
lean::cnstr_set(x_51, 9, x_46);
lean::cnstr_set(x_51, 10, x_48);
x_52 = lean::box(0);
if (lean::is_scalar(x_17)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_17;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_51);
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
obj* _init_l_lean_elaborator_init__quot_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("init_quot");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = l_lean_kvmap_set__name(x_0, x_2, x_4);
x_6 = l_lean_elaborator_dummy;
x_7 = lean_expr_mk_mdata(x_5, x_6);
return x_7;
}
}
obj* l_lean_elaborator_init__quot_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_lean_elaborator_init__quot_elaborate___closed__1;
x_4 = l_lean_elaborator_old__elab__command(x_0, x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_elaborator_set__option_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_52; 
lean::dec(x_1);
x_4 = l_lean_parser_command_set__option_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 2);
lean::inc(x_11);
lean::dec(x_9);
x_14 = lean::cnstr_get(x_2, 4);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_14, 6);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_8, 2);
lean::inc(x_18);
lean::dec(x_8);
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 2);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_2, 3);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_14, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_14, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_14, 2);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_14, 3);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_14, 4);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_14, 5);
lean::inc(x_39);
lean::dec(x_14);
x_42 = lean::cnstr_get(x_2, 5);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_2, 6);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_2, 7);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_2, 8);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_2, 9);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_2, 10);
lean::inc(x_52);
lean::dec(x_2);
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_55; 
x_55 = lean::cnstr_get(x_18, 0);
lean::inc(x_55);
lean::dec(x_18);
if (lean::obj_tag(x_55) == 0)
{
uint8 x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_55);
x_59 = 1;
x_60 = l_lean_kvmap_set__bool(x_16, x_11, x_59);
x_61 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_61, 0, x_29);
lean::cnstr_set(x_61, 1, x_31);
lean::cnstr_set(x_61, 2, x_33);
lean::cnstr_set(x_61, 3, x_35);
lean::cnstr_set(x_61, 4, x_37);
lean::cnstr_set(x_61, 5, x_39);
lean::cnstr_set(x_61, 6, x_60);
x_62 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_62, 0, x_21);
lean::cnstr_set(x_62, 1, x_23);
lean::cnstr_set(x_62, 2, x_25);
lean::cnstr_set(x_62, 3, x_27);
lean::cnstr_set(x_62, 4, x_61);
lean::cnstr_set(x_62, 5, x_42);
lean::cnstr_set(x_62, 6, x_44);
lean::cnstr_set(x_62, 7, x_46);
lean::cnstr_set(x_62, 8, x_48);
lean::cnstr_set(x_62, 9, x_50);
lean::cnstr_set(x_62, 10, x_52);
x_63 = lean::box(0);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_62);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
else
{
uint8 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_55);
x_67 = 0;
x_68 = l_lean_kvmap_set__bool(x_16, x_11, x_67);
x_69 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_69, 0, x_29);
lean::cnstr_set(x_69, 1, x_31);
lean::cnstr_set(x_69, 2, x_33);
lean::cnstr_set(x_69, 3, x_35);
lean::cnstr_set(x_69, 4, x_37);
lean::cnstr_set(x_69, 5, x_39);
lean::cnstr_set(x_69, 6, x_68);
x_70 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_70, 0, x_21);
lean::cnstr_set(x_70, 1, x_23);
lean::cnstr_set(x_70, 2, x_25);
lean::cnstr_set(x_70, 3, x_27);
lean::cnstr_set(x_70, 4, x_69);
lean::cnstr_set(x_70, 5, x_42);
lean::cnstr_set(x_70, 6, x_44);
lean::cnstr_set(x_70, 7, x_46);
lean::cnstr_set(x_70, 8, x_48);
lean::cnstr_set(x_70, 9, x_50);
lean::cnstr_set(x_70, 10, x_52);
x_71 = lean::box(0);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_70);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
}
case 1:
{
obj* x_74; obj* x_77; 
x_74 = lean::cnstr_get(x_18, 0);
lean::inc(x_74);
lean::dec(x_18);
x_77 = l_lean_parser_string__lit_view_value(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_11);
x_79 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_79, 0, x_29);
lean::cnstr_set(x_79, 1, x_31);
lean::cnstr_set(x_79, 2, x_33);
lean::cnstr_set(x_79, 3, x_35);
lean::cnstr_set(x_79, 4, x_37);
lean::cnstr_set(x_79, 5, x_39);
lean::cnstr_set(x_79, 6, x_16);
x_80 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_80, 0, x_21);
lean::cnstr_set(x_80, 1, x_23);
lean::cnstr_set(x_80, 2, x_25);
lean::cnstr_set(x_80, 3, x_27);
lean::cnstr_set(x_80, 4, x_79);
lean::cnstr_set(x_80, 5, x_42);
lean::cnstr_set(x_80, 6, x_44);
lean::cnstr_set(x_80, 7, x_46);
lean::cnstr_set(x_80, 8, x_48);
lean::cnstr_set(x_80, 9, x_50);
lean::cnstr_set(x_80, 10, x_52);
x_81 = lean::box(0);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_80);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
return x_83;
}
else
{
obj* x_84; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_77, 0);
lean::inc(x_84);
lean::dec(x_77);
x_87 = l_lean_kvmap_set__string(x_16, x_11, x_84);
x_88 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_88, 0, x_29);
lean::cnstr_set(x_88, 1, x_31);
lean::cnstr_set(x_88, 2, x_33);
lean::cnstr_set(x_88, 3, x_35);
lean::cnstr_set(x_88, 4, x_37);
lean::cnstr_set(x_88, 5, x_39);
lean::cnstr_set(x_88, 6, x_87);
x_89 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_89, 0, x_21);
lean::cnstr_set(x_89, 1, x_23);
lean::cnstr_set(x_89, 2, x_25);
lean::cnstr_set(x_89, 3, x_27);
lean::cnstr_set(x_89, 4, x_88);
lean::cnstr_set(x_89, 5, x_42);
lean::cnstr_set(x_89, 6, x_44);
lean::cnstr_set(x_89, 7, x_46);
lean::cnstr_set(x_89, 8, x_48);
lean::cnstr_set(x_89, 9, x_50);
lean::cnstr_set(x_89, 10, x_52);
x_90 = lean::box(0);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
return x_92;
}
}
default:
{
obj* x_93; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_93 = lean::cnstr_get(x_18, 0);
lean::inc(x_93);
lean::dec(x_18);
x_96 = l_lean_parser_number_view_to__nat___main(x_93);
x_97 = l_lean_kvmap_set__nat(x_16, x_11, x_96);
x_98 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_98, 0, x_29);
lean::cnstr_set(x_98, 1, x_31);
lean::cnstr_set(x_98, 2, x_33);
lean::cnstr_set(x_98, 3, x_35);
lean::cnstr_set(x_98, 4, x_37);
lean::cnstr_set(x_98, 5, x_39);
lean::cnstr_set(x_98, 6, x_97);
x_99 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_99, 0, x_21);
lean::cnstr_set(x_99, 1, x_23);
lean::cnstr_set(x_99, 2, x_25);
lean::cnstr_set(x_99, 3, x_27);
lean::cnstr_set(x_99, 4, x_98);
lean::cnstr_set(x_99, 5, x_42);
lean::cnstr_set(x_99, 6, x_44);
lean::cnstr_set(x_99, 7, x_46);
lean::cnstr_set(x_99, 8, x_48);
lean::cnstr_set(x_99, 9, x_50);
lean::cnstr_set(x_99, 10, x_52);
x_100 = lean::box(0);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_99);
x_102 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
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
x_23 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_23, 0, x_11);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set(x_23, 2, x_20);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set(x_23, 4, x_1);
lean::cnstr_set_scalar(x_23, sizeof(void*)*5, x_21);
x_24 = x_23;
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_26, 0, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg___lambda__1), 2, 1);
lean::closure_set(x_27, 0, x_5);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_29, 0, x_26);
lean::closure_set(x_29, 1, x_28);
return x_29;
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
obj* x_10; obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_with__current__command___rarg), 6, 5);
lean::closure_set(x_18, 0, x_10);
lean::closure_set(x_18, 1, x_15);
lean::closure_set(x_18, 2, x_1);
lean::closure_set(x_18, 3, x_2);
lean::closure_set(x_18, 4, x_3);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___lambda__1), 4, 3);
lean::closure_set(x_19, 0, x_12);
lean::closure_set(x_19, 1, x_1);
lean::closure_set(x_19, 2, x_2);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_21, 0, x_18);
lean::closure_set(x_21, 1, x_20);
return x_21;
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
obj* x_9; obj* x_10; 
x_9 = l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1;
x_10 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_0, x_9, x_1, x_2, x_6);
return x_10;
}
else
{
obj* x_12; obj* x_15; obj* x_18; 
lean::dec(x_0);
x_12 = lean::cnstr_get(x_4, 0);
lean::inc(x_12);
lean::dec(x_4);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(x_15, x_1, x_2, x_6);
return x_18;
}
}
}
obj* l_lean_elaborator_no__kind_elaborate___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
lean::inc(x_5);
x_11 = l_lean_parser_syntax_as__node___main(x_5);
x_12 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1;
x_13 = l_option_map___rarg(x_12, x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_5);
lean::dec(x_9);
x_16 = lean::box(0);
lean::inc(x_1);
lean::inc(x_0);
x_19 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_16, x_0, x_1, x_7);
x_20 = lean::box(x_2);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 5, 4);
lean::closure_set(x_21, 0, x_20);
lean::closure_set(x_21, 1, x_3);
lean::closure_set(x_21, 2, x_0);
lean::closure_set(x_21, 3, x_1);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_23, 0, x_19);
lean::closure_set(x_23, 1, x_22);
return x_23;
}
else
{
obj* x_24; obj* x_27; uint8 x_28; 
x_24 = lean::cnstr_get(x_13, 0);
lean::inc(x_24);
lean::dec(x_13);
x_27 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2;
x_28 = lean_name_dec_eq(x_24, x_27);
if (x_28 == 0)
{
obj* x_29; uint8 x_30; 
x_29 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3;
x_30 = lean_name_dec_eq(x_24, x_29);
lean::dec(x_24);
if (x_30 == 0)
{
obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_5);
lean::dec(x_9);
x_34 = lean::box(0);
lean::inc(x_1);
lean::inc(x_0);
x_37 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_34, x_0, x_1, x_7);
x_38 = lean::box(x_2);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 5, 4);
lean::closure_set(x_39, 0, x_38);
lean::closure_set(x_39, 1, x_3);
lean::closure_set(x_39, 2, x_0);
lean::closure_set(x_39, 3, x_1);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_40, 0, x_39);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_41, 0, x_37);
lean::closure_set(x_41, 1, x_40);
return x_41;
}
else
{
lean::dec(x_3);
if (x_2 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_46 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_9;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_7);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_49, 0, x_48);
return x_49;
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_9);
x_51 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4;
x_52 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_5, x_51, x_0, x_1, x_7);
return x_52;
}
}
}
else
{
lean::dec(x_3);
lean::dec(x_24);
if (x_2 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_9);
x_56 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5;
x_57 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_5, x_56, x_0, x_1, x_7);
return x_57;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_61 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_9;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_7);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_64, 0, x_63);
return x_64;
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
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1;
x_9 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_3, x_8, x_0, x_1, x_5);
return x_9;
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
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_6 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
x_14 = l_lean_elaborator_to__pexpr___main___closed__28;
x_15 = l_option_map___rarg(x_14, x_12);
if (lean::obj_tag(x_15) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_20 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_23, 0, x_22);
return x_23;
}
else
{
obj* x_25; 
lean::dec(x_9);
x_25 = lean::box(0);
x_10 = x_25;
goto lbl_11;
}
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_15, 0);
lean::inc(x_26);
lean::dec(x_15);
if (lean::obj_tag(x_1) == 0)
{
obj* x_31; 
lean::dec(x_9);
lean::dec(x_26);
x_31 = lean::box(0);
x_10 = x_31;
goto lbl_11;
}
else
{
obj* x_32; uint8 x_34; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
x_34 = lean_name_dec_eq(x_26, x_32);
lean::dec(x_32);
lean::dec(x_26);
if (x_34 == 0)
{
obj* x_38; 
lean::dec(x_9);
x_38 = lean::box(0);
x_10 = x_38;
goto lbl_11;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_44 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_9;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_7);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_47, 0, x_46);
return x_47;
}
}
}
lbl_11:
{
obj* x_49; obj* x_50; obj* x_53; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_10);
x_49 = l_lean_parser_command_end_has__view;
x_50 = lean::cnstr_get(x_49, 1);
lean::inc(x_50);
lean::dec(x_49);
x_53 = lean::apply_1(x_50, x_5);
x_54 = l_lean_elaborator_end__scope___lambda__2___closed__1;
x_55 = lean::string_append(x_54, x_0);
lean::dec(x_0);
x_57 = l_lean_elaborator_end__scope___lambda__2___closed__2;
x_58 = lean::string_append(x_55, x_57);
x_59 = lean::box(0);
x_60 = l_option_get__or__else___main___rarg(x_1, x_59);
x_61 = l_lean_name_to__string___closed__1;
x_62 = l_lean_name_to__string__with__sep___main(x_61, x_60);
x_63 = lean::string_append(x_58, x_62);
lean::dec(x_62);
x_65 = l_char_has__repr___closed__1;
x_66 = lean::string_append(x_63, x_65);
x_67 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_53, x_66, x_2, x_3, x_7);
return x_67;
}
}
}
obj* _init_l_lean_elaborator_end__scope___lambda__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_end_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__1), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_elaborator_end__scope___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = l_lean_elaborator_current__command___rarg(x_5);
x_9 = l_lean_elaborator_end__scope___lambda__3___closed__1;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_8);
lean::closure_set(x_10, 1, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__2), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_2);
lean::closure_set(x_11, 3, x_3);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_12);
return x_13;
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
x_3 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_5 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_4 = x_1;
} else {
 lean::inc(x_2);
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
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1;
x_10 = l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg(x_9, x_0, x_1, x_2, x_6);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3), 2, 1);
lean::closure_set(x_11, 0, x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_12);
return x_13;
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
x_9 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4), 4, 3);
lean::closure_set(x_10, 0, x_9);
lean::closure_set(x_10, 1, x_0);
lean::closure_set(x_10, 2, x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_11);
return x_12;
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
obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_elaborator_to__pexpr___main___closed__28;
x_11 = l_option_map___rarg(x_10, x_7);
x_12 = l_lean_elaborator_section_elaborate___lambda__1___closed__1;
x_13 = l_lean_elaborator_end__scope(x_12, x_11, x_1, x_2, x_4);
return x_13;
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
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_section_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__1), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_elaborator_section_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = l_lean_elaborator_section_elaborate___closed__1;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_5, 0, x_3);
lean::closure_set(x_5, 1, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_section_elaborate___lambda__2), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_5);
lean::closure_set(x_8, 1, x_7);
return x_8;
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
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
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
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1;
x_10 = l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg(x_9, x_0, x_1, x_2, x_6);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3), 2, 1);
lean::closure_set(x_11, 0, x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
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
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_8);
lean::closure_set(x_10, 1, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__4), 4, 3);
lean::closure_set(x_11, 0, x_4);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_12);
return x_13;
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
obj* x_4; obj* x_7; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
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
x_15 = l_lean_elaborator_end__scope(x_14, x_13, x_1, x_2, x_4);
return x_15;
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
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_namespace_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__1), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_elaborator_namespace_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = l_lean_elaborator_namespace_elaborate___closed__1;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_5, 0, x_3);
lean::closure_set(x_5, 1, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_namespace_elaborate___lambda__2), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_5);
lean::closure_set(x_8, 1, x_7);
return x_8;
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
x_24 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_10, x_1, x_2);
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
x_26 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_4, x_1, x_2);
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
x_51 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_34, x_1, x_2);
x_52 = l_rbnode_balance2__node___main___rarg(x_51, x_30, x_32, x_28);
return x_52;
}
else
{
obj* x_53; obj* x_54; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_34, x_1, x_2);
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
x_58 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_28, x_1, x_2);
x_59 = l_rbnode_balance1__node___main___rarg(x_58, x_30, x_32, x_34);
return x_59;
}
else
{
obj* x_60; obj* x_61; 
x_60 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_28, x_1, x_2);
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
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_init__quot_elaborate___closed__1;
x_8 = l_lean_elaborator_old__elab__command(x_2, x_7, x_0, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_0 = l_lean_parser_module_header;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2), 3, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = l_lean_parser_command_notation;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4), 3, 0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_lean_parser_command_reserve__notation;
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_lean_parser_command_universe;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8), 3, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_lean_parser_no__kind;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_no__kind_elaborate), 3, 0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_lean_parser_command_section;
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_section_elaborate), 3, 0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_command_namespace;
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_namespace_elaborate), 3, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_parser_command_variables;
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10), 3, 0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_lean_parser_command_include;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12), 3, 0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_lean_parser_command_declaration;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14), 3, 0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_command_attribute;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16), 3, 0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_lean_parser_command_open;
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18), 3, 0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_lean_parser_command_export;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20), 3, 0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_lean_parser_command_check;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22), 3, 0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_lean_parser_command_init__quot;
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24), 3, 0);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_lean_parser_command_set__option;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26), 3, 0);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
x_48 = lean::box(0);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_44);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_41);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_38);
lean::cnstr_set(x_52, 1, x_51);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_35);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_32);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_29);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_26);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_23);
lean::cnstr_set(x_57, 1, x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_20);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_17);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_14);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_11);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_8);
lean::cnstr_set(x_62, 1, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_5);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_2);
lean::cnstr_set(x_64, 1, x_63);
x_65 = l_list_foldl___main___at_lean_elaborator_elaborators___spec__5(x_48, x_64);
return x_65;
}
}
obj* _init_l_lean_elaborator_elaborators() {
_start:
{
obj* x_0; 
x_0 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1;
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
if (x_15 == 0)
{
uint8 x_16; 
x_16 = 0;
return x_16;
}
else
{
uint8 x_17; 
x_17 = 1;
return x_17;
}
}
else
{
uint8 x_20; 
lean::dec(x_1);
lean::dec(x_4);
x_20 = 1;
return x_20;
}
}
else
{
uint8 x_23; 
lean::dec(x_1);
lean::dec(x_0);
x_23 = 1;
return x_23;
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
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_14 = x_2;
} else {
 lean::inc(x_12);
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
if (x_27 == 0)
{
obj* x_31; 
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_0);
x_31 = lean::box(0);
return x_31;
}
else
{
obj* x_32; obj* x_35; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
lean::dec(x_1);
x_35 = lean::cnstr_get(x_32, 2);
lean::inc(x_35);
lean::dec(x_32);
x_38 = l_lean_name_append___main(x_35, x_0);
if (lean::is_scalar(x_14)) {
 x_39 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_39 = x_14;
}
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
}
else
{
obj* x_41; obj* x_44; obj* x_47; obj* x_48; 
lean::dec(x_12);
x_41 = lean::cnstr_get(x_1, 0);
lean::inc(x_41);
lean::dec(x_1);
x_44 = lean::cnstr_get(x_41, 2);
lean::inc(x_44);
lean::dec(x_41);
x_47 = l_lean_name_append___main(x_44, x_0);
if (lean::is_scalar(x_14)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_14;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
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
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
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
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
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
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
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
obj* x_15; obj* x_16; obj* x_18; obj* x_19; uint8 x_22; obj* x_24; obj* x_25; obj* x_28; obj* x_30; obj* x_31; obj* x_34; obj* x_35; obj* x_36; obj* x_38; 
x_15 = l_lean_elaborator_resolve__context___main___closed__1;
x_16 = lean::box(0);
lean::inc(x_0);
x_18 = l_lean_name_replace__prefix___main(x_0, x_15, x_16);
x_19 = lean::cnstr_get(x_2, 8);
lean::inc(x_19);
lean::inc(x_18);
x_22 = lean_environment_contains(x_19, x_18);
lean::inc(x_0);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_match__open__spec), 2, 1);
lean::closure_set(x_24, 0, x_0);
x_25 = lean::cnstr_get(x_4, 5);
lean::inc(x_25);
lean::dec(x_4);
x_28 = l_list_filter__map___main___rarg(x_24, x_25);
lean::inc(x_2);
x_30 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(x_2, x_28);
x_31 = lean::cnstr_get(x_2, 3);
lean::inc(x_31);
lean::inc(x_2);
x_34 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(x_2, x_31);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_resolve__context___main___lambda__1), 2, 1);
lean::closure_set(x_35, 0, x_0);
x_36 = l_list_filter__map___main___rarg(x_35, x_34);
lean::inc(x_2);
x_38 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(x_2, x_36);
if (x_22 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_18);
x_40 = l_list_append___rarg(x_14, x_30);
x_41 = l_list_append___rarg(x_40, x_38);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_2);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
return x_43;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_18);
lean::cnstr_set(x_44, 1, x_14);
x_45 = l_list_append___rarg(x_44, x_30);
x_46 = l_list_append___rarg(x_45, x_38);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_2);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
}
else
{
obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_4);
x_50 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_release(x_14, 1);
 x_52 = x_14;
} else {
 lean::inc(x_50);
 lean::dec(x_14);
 x_52 = lean::box(0);
}
x_53 = l_lean_name_append___main(x_50, x_0);
x_54 = lean::box(0);
if (lean::is_scalar(x_52)) {
 x_55 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_55 = x_52;
}
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_2);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
}
else
{
obj* x_60; obj* x_63; obj* x_65; obj* x_66; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_4);
lean::dec(x_0);
x_60 = lean::cnstr_get(x_9, 0);
lean::inc(x_60);
lean::dec(x_9);
x_63 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_set(x_60, 1, lean::box(0));
 x_65 = x_60;
} else {
 lean::inc(x_63);
 lean::dec(x_60);
 x_65 = lean::box(0);
}
x_66 = lean::cnstr_get(x_63, 0);
lean::inc(x_66);
lean::dec(x_63);
x_69 = lean::box(0);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_66);
lean::cnstr_set(x_70, 1, x_69);
if (lean::is_scalar(x_65)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_65;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_2);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
return x_72;
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
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
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
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_23 = x_13;
} else {
 lean::inc(x_21);
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_21, 0);
x_26 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 lean::cnstr_set(x_21, 1, lean::box(0));
 x_28 = x_21;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_5 = x_0;
} else {
 lean::inc(x_3);
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
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
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
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_15 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_17 = x_8;
} else {
 lean::inc(x_15);
 lean::dec(x_8);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_15, 0);
x_20 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_22 = x_15;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
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
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_41 = x_0;
} else {
 lean::inc(x_39);
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
if (lean::is_exclusive(x_44)) {
 lean::cnstr_set(x_44, 0, lean::box(0));
 x_49 = x_44;
} else {
 lean::inc(x_47);
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
if (lean::is_exclusive(x_44)) {
 lean::cnstr_set(x_44, 0, lean::box(0));
 x_53 = x_44;
} else {
 lean::inc(x_51);
 lean::dec(x_44);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 0);
x_56 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 lean::cnstr_set(x_51, 1, lean::box(0));
 x_58 = x_51;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
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
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_15);
x_19 = lean::cnstr_get(x_2, 6);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_2, 7);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 8);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 9);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_2, 10);
lean::inc(x_27);
lean::dec(x_2);
x_30 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
lean::cnstr_set(x_30, 4, x_13);
lean::cnstr_set(x_30, 5, x_18);
lean::cnstr_set(x_30, 6, x_19);
lean::cnstr_set(x_30, 7, x_21);
lean::cnstr_set(x_30, 8, x_23);
lean::cnstr_set(x_30, 9, x_25);
lean::cnstr_set(x_30, 10, x_27);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_34, 0, x_33);
return x_34;
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
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; 
x_10 = l_lean_name_to__string___closed__1;
x_11 = l_lean_name_to__string__with__sep___main(x_10, x_0);
x_12 = l_lean_elaborator_run___lambda__2___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_1, x_13, x_2, x_3, x_7);
return x_15;
}
else
{
obj* x_18; obj* x_21; 
lean::dec(x_1);
lean::dec(x_0);
x_18 = lean::cnstr_get(x_5, 0);
lean::inc(x_18);
lean::dec(x_5);
x_21 = lean::apply_3(x_18, x_2, x_3, x_7);
return x_21;
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
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_4 = x_1;
} else {
 lean::inc(x_2);
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; 
lean::inc(x_0);
x_6 = l_lean_parser_syntax_to__format___main(x_0);
x_7 = lean::mk_nat_obj(80u);
x_8 = l_lean_format_pretty(x_6, x_7);
x_9 = l_lean_elaborator_run___lambda__4___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_12 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_0, x_10, x_2, x_3, x_4);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = l_lean_elaborator_elaborators;
lean::inc(x_16);
x_21 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_19, x_16);
lean::inc(x_4);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_4);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_25, 0, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__2), 5, 4);
lean::closure_set(x_26, 0, x_16);
lean::closure_set(x_26, 1, x_0);
lean::closure_set(x_26, 2, x_2);
lean::closure_set(x_26, 3, x_3);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_27, 0, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_28, 0, x_25);
lean::closure_set(x_28, 1, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__3), 2, 1);
lean::closure_set(x_29, 0, x_4);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_30, 0, x_28);
lean::closure_set(x_30, 1, x_29);
return x_30;
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
obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_lean_message__log_empty;
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_13; obj* x_16; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_10, 5);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_16, 0, x_13);
return x_16;
}
}
}
obj* _init_l_lean_elaborator_run___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("trace");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("as_messages");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = l_lean_options_mk;
x_6 = 1;
x_7 = l_lean_kvmap_set__bool(x_5, x_4, x_6);
x_8 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1;
x_9 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2;
x_10 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_9);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
lean::cnstr_set(x_10, 5, x_0);
lean::cnstr_set(x_10, 6, x_7);
return x_10;
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
uint8 x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = 0;
x_1 = l_lean_elaborator_max__commands;
x_2 = lean::box(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___boxed), 5, 2);
lean::closure_set(x_3, 0, x_2);
lean::closure_set(x_3, 1, x_1);
return x_3;
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
obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_1 = lean::box(0);
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = l_lean_expander_builtin__transformers;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_lean_elaborator_run___closed__1;
x_10 = l_lean_message__log_empty;
x_11 = l_lean_elaborator_run___closed__2;
x_12 = l_lean_elaborator_run___closed__3;
x_13 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_1);
lean::cnstr_set(x_13, 2, x_8);
lean::cnstr_set(x_13, 3, x_1);
lean::cnstr_set(x_13, 4, x_9);
lean::cnstr_set(x_13, 5, x_10);
lean::cnstr_set(x_13, 6, x_2);
lean::cnstr_set(x_13, 7, x_7);
lean::cnstr_set(x_13, 8, x_11);
lean::cnstr_set(x_13, 9, x_12);
lean::cnstr_set(x_13, 10, x_8);
x_14 = l_lean_elaborator_run___closed__4;
x_15 = l_lean_elaborator_run___closed__5;
x_16 = l_lean_elaborator_run___closed__6;
x_17 = l_lean_elaborator_max__recursion;
x_18 = l_lean_parser_rec__t_run___at_lean_elaborator_run___spec__5(x_14, x_15, x_16, x_17, x_0, x_13);
x_19 = l_lean_elaborator_run___closed__7;
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_20, 0, x_18);
lean::closure_set(x_20, 1, x_19);
return x_20;
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
