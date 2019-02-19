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
lean::inc(x_43);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_45 = x_41;
} else {
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
lean::inc(x_47);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_49 = x_41;
} else {
 lean::dec(x_41);
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
x_55 = lean::cnstr_get(x_50, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_50, 1);
lean::inc(x_57);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 1);
 x_59 = x_50;
} else {
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
obj* x_64; obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
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
lean::inc(x_78);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_80 = x_73;
} else {
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
lean::inc(x_82);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_84 = x_73;
} else {
 lean::dec(x_73);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_82, 1);
lean::inc(x_87);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 x_89 = x_82;
} else {
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
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_28 = x_21;
} else {
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
lean::inc(x_30);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_32 = x_21;
} else {
 lean::dec(x_21);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 1);
lean::inc(x_35);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_37 = x_30;
} else {
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
lean::inc(x_71);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_73 = x_66;
} else {
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
lean::inc(x_75);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_77 = x_66;
} else {
 lean::dec(x_66);
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
lean::inc(x_111);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_113 = x_106;
} else {
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
lean::inc(x_115);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_117 = x_106;
} else {
 lean::dec(x_106);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 x_122 = x_115;
} else {
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
lean::inc(x_78);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_80 = x_73;
} else {
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
lean::inc(x_82);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_84 = x_73;
} else {
 lean::dec(x_73);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_82, 1);
lean::inc(x_87);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 x_89 = x_82;
} else {
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
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_28 = x_21;
} else {
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
lean::inc(x_30);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_32 = x_21;
} else {
 lean::dec(x_21);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 1);
lean::inc(x_35);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_37 = x_30;
} else {
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
lean::inc(x_71);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_73 = x_66;
} else {
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
lean::inc(x_75);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_77 = x_66;
} else {
 lean::dec(x_66);
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
lean::inc(x_111);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_113 = x_106;
} else {
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
lean::inc(x_115);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_117 = x_106;
} else {
 lean::dec(x_106);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 x_122 = x_115;
} else {
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
lean::inc(x_78);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_80 = x_73;
} else {
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
lean::inc(x_82);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_84 = x_73;
} else {
 lean::dec(x_73);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_82, 1);
lean::inc(x_87);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 x_89 = x_82;
} else {
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
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_28 = x_21;
} else {
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
lean::inc(x_30);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_32 = x_21;
} else {
 lean::dec(x_21);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 1);
lean::inc(x_35);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_37 = x_30;
} else {
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
lean::inc(x_71);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_73 = x_66;
} else {
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
lean::inc(x_75);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_77 = x_66;
} else {
 lean::dec(x_66);
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
lean::inc(x_111);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_113 = x_106;
} else {
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
lean::inc(x_115);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_117 = x_106;
} else {
 lean::dec(x_106);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 x_122 = x_115;
} else {
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
lean::inc(x_78);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_80 = x_73;
} else {
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
lean::inc(x_82);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_84 = x_73;
} else {
 lean::dec(x_73);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_82, 1);
lean::inc(x_87);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 x_89 = x_82;
} else {
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
lean::inc(x_26);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_28 = x_21;
} else {
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
lean::inc(x_30);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_32 = x_21;
} else {
 lean::dec(x_21);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 1);
lean::inc(x_35);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_37 = x_30;
} else {
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
lean::inc(x_71);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_73 = x_66;
} else {
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
lean::inc(x_75);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_77 = x_66;
} else {
 lean::dec(x_66);
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
lean::inc(x_111);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_113 = x_106;
} else {
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
lean::inc(x_115);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_117 = x_106;
} else {
 lean::dec(x_106);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 x_122 = x_115;
} else {
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
lean::inc(x_69);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_71 = x_66;
} else {
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
lean::inc(x_73);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_75 = x_66;
} else {
 lean::dec(x_66);
 x_75 = lean::box(0);
}
x_76 = lean::cnstr_get(x_73, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_73, 1);
lean::inc(x_78);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 x_80 = x_73;
} else {
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
lean::inc(x_124);
if (lean::is_exclusive(x_122)) {
 lean::cnstr_release(x_122, 0);
 x_126 = x_122;
} else {
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
lean::inc(x_128);
if (lean::is_exclusive(x_122)) {
 lean::cnstr_release(x_122, 0);
 x_130 = x_122;
} else {
 lean::dec(x_122);
 x_130 = lean::box(0);
}
x_131 = lean::cnstr_get(x_128, 0);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_128, 1);
lean::inc(x_133);
if (lean::is_exclusive(x_128)) {
 lean::cnstr_release(x_128, 0);
 lean::cnstr_release(x_128, 1);
 x_135 = x_128;
} else {
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
lean::inc(x_206);
x_208 = lean::cnstr_get(x_205, 1);
lean::inc(x_208);
if (lean::is_exclusive(x_205)) {
 lean::cnstr_release(x_205, 0);
 lean::cnstr_release(x_205, 1);
 x_210 = x_205;
} else {
 lean::dec(x_205);
 x_210 = lean::box(0);
}
x_211 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_208);
x_212 = lean::cnstr_get(x_211, 0);
lean::inc(x_212);
x_214 = lean::cnstr_get(x_211, 1);
lean::inc(x_214);
if (lean::is_exclusive(x_211)) {
 lean::cnstr_release(x_211, 0);
 lean::cnstr_release(x_211, 1);
 x_216 = x_211;
} else {
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
lean::inc(x_227);
if (lean::is_exclusive(x_219)) {
 lean::cnstr_release(x_219, 0);
 x_229 = x_219;
} else {
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
lean::inc(x_231);
if (lean::is_exclusive(x_219)) {
 lean::cnstr_release(x_219, 0);
 x_233 = x_219;
} else {
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
lean::inc(x_328);
x_330 = lean::cnstr_get(x_214, 1);
lean::inc(x_330);
if (lean::is_exclusive(x_214)) {
 lean::cnstr_release(x_214, 0);
 lean::cnstr_release(x_214, 1);
 x_332 = x_214;
} else {
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
lean::inc(x_354);
if (lean::is_exclusive(x_344)) {
 lean::cnstr_release(x_344, 0);
 x_356 = x_344;
} else {
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
lean::inc(x_358);
if (lean::is_exclusive(x_344)) {
 lean::cnstr_release(x_344, 0);
 x_360 = x_344;
} else {
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
obj* x_456; obj* x_458; obj* x_461; obj* x_462; obj* x_464; obj* x_465; obj* x_466; obj* x_467; uint8 x_468; obj* x_470; obj* x_471; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; 
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
lean::dec(x_361);
x_470 = l_lean_kvmap_set__bool(x_466, x_467, x_468);
x_471 = lean::cnstr_get(x_202, 1);
lean::inc(x_471);
lean::dec(x_202);
x_474 = l_lean_elaborator_to__pexpr___main___closed__27;
x_475 = l_option_map___rarg(x_474, x_471);
x_476 = l_lean_elaborator_to__pexpr___main___closed__28;
x_477 = l_option_map___rarg(x_476, x_475);
x_478 = l_option_get__or__else___main___rarg(x_477, x_461);
x_479 = l_lean_elaborator_to__pexpr___main___closed__29;
x_480 = l_lean_kvmap_set__name(x_470, x_479, x_478);
x_481 = l_list_append___rarg(x_385, x_456);
x_482 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_481);
x_483 = lean_expr_mk_mdata(x_480, x_482);
if (lean::is_scalar(x_210)) {
 x_484 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_484 = x_210;
}
lean::cnstr_set(x_484, 0, x_483);
lean::cnstr_set(x_484, 1, x_458);
x_14 = x_484;
goto lbl_15;
}
}
}
}
else
{
if (lean::obj_tag(x_330) == 0)
{
obj* x_488; 
lean::dec(x_333);
lean::inc(x_1);
lean::inc(x_0);
x_488 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_206, x_1, x_2);
if (lean::obj_tag(x_488) == 0)
{
obj* x_497; obj* x_499; obj* x_500; 
lean::dec(x_332);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_212);
lean::dec(x_210);
x_497 = lean::cnstr_get(x_488, 0);
lean::inc(x_497);
if (lean::is_exclusive(x_488)) {
 lean::cnstr_release(x_488, 0);
 x_499 = x_488;
} else {
 lean::dec(x_488);
 x_499 = lean::box(0);
}
if (lean::is_scalar(x_499)) {
 x_500 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_500 = x_499;
}
lean::cnstr_set(x_500, 0, x_497);
return x_500;
}
else
{
obj* x_501; obj* x_503; obj* x_504; obj* x_506; obj* x_509; obj* x_513; 
x_501 = lean::cnstr_get(x_488, 0);
lean::inc(x_501);
if (lean::is_exclusive(x_488)) {
 lean::cnstr_release(x_488, 0);
 x_503 = x_488;
} else {
 lean::dec(x_488);
 x_503 = lean::box(0);
}
x_504 = lean::cnstr_get(x_501, 0);
lean::inc(x_504);
x_506 = lean::cnstr_get(x_501, 1);
lean::inc(x_506);
lean::dec(x_501);
lean::inc(x_1);
lean::inc(x_0);
x_513 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_212, x_1, x_506);
if (lean::obj_tag(x_513) == 0)
{
obj* x_522; obj* x_525; 
lean::dec(x_332);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
lean::dec(x_504);
x_522 = lean::cnstr_get(x_513, 0);
lean::inc(x_522);
lean::dec(x_513);
if (lean::is_scalar(x_503)) {
 x_525 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_525 = x_503;
 lean::cnstr_set_tag(x_503, 0);
}
lean::cnstr_set(x_525, 0, x_522);
return x_525;
}
else
{
obj* x_526; obj* x_529; obj* x_531; obj* x_534; 
x_526 = lean::cnstr_get(x_513, 0);
lean::inc(x_526);
lean::dec(x_513);
x_529 = lean::cnstr_get(x_526, 0);
lean::inc(x_529);
x_531 = lean::cnstr_get(x_526, 1);
lean::inc(x_531);
lean::dec(x_526);
x_534 = lean::cnstr_get(x_202, 2);
lean::inc(x_534);
if (lean::obj_tag(x_534) == 0)
{
obj* x_538; 
lean::dec(x_332);
lean::dec(x_503);
if (lean::is_scalar(x_216)) {
 x_538 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_538 = x_216;
}
lean::cnstr_set(x_538, 0, x_529);
lean::cnstr_set(x_538, 1, x_531);
x_509 = x_538;
goto lbl_510;
}
else
{
obj* x_539; obj* x_542; obj* x_546; 
x_539 = lean::cnstr_get(x_534, 0);
lean::inc(x_539);
lean::dec(x_534);
x_542 = lean::cnstr_get(x_539, 0);
lean::inc(x_542);
lean::dec(x_539);
lean::inc(x_1);
x_546 = l_lean_elaborator_to__pexpr___main(x_542, x_1, x_531);
if (lean::obj_tag(x_546) == 0)
{
obj* x_556; obj* x_559; 
lean::dec(x_332);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
lean::dec(x_504);
lean::dec(x_529);
x_556 = lean::cnstr_get(x_546, 0);
lean::inc(x_556);
lean::dec(x_546);
if (lean::is_scalar(x_503)) {
 x_559 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_559 = x_503;
 lean::cnstr_set_tag(x_503, 0);
}
lean::cnstr_set(x_559, 0, x_556);
return x_559;
}
else
{
obj* x_561; obj* x_564; obj* x_566; obj* x_569; obj* x_570; obj* x_571; obj* x_572; 
lean::dec(x_503);
x_561 = lean::cnstr_get(x_546, 0);
lean::inc(x_561);
lean::dec(x_546);
x_564 = lean::cnstr_get(x_561, 0);
lean::inc(x_564);
x_566 = lean::cnstr_get(x_561, 1);
lean::inc(x_566);
lean::dec(x_561);
x_569 = lean::box(0);
if (lean::is_scalar(x_332)) {
 x_570 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_570 = x_332;
}
lean::cnstr_set(x_570, 0, x_564);
lean::cnstr_set(x_570, 1, x_569);
x_571 = l_list_append___rarg(x_529, x_570);
if (lean::is_scalar(x_216)) {
 x_572 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_572 = x_216;
}
lean::cnstr_set(x_572, 0, x_571);
lean::cnstr_set(x_572, 1, x_566);
x_509 = x_572;
goto lbl_510;
}
}
}
lbl_510:
{
obj* x_573; obj* x_575; obj* x_578; obj* x_579; obj* x_581; obj* x_582; obj* x_583; obj* x_584; uint8 x_585; obj* x_586; obj* x_587; obj* x_590; obj* x_591; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; 
x_573 = lean::cnstr_get(x_509, 0);
lean::inc(x_573);
x_575 = lean::cnstr_get(x_509, 1);
lean::inc(x_575);
lean::dec(x_509);
x_578 = lean::box(0);
x_579 = lean::mk_nat_obj(0u);
lean::inc(x_504);
x_581 = l_list_length__aux___main___rarg(x_504, x_579);
x_582 = l_lean_elaborator_to__pexpr___main___closed__25;
x_583 = l_lean_kvmap_set__nat(x_578, x_582, x_581);
x_584 = l_lean_elaborator_to__pexpr___main___closed__26;
x_585 = 1;
x_586 = l_lean_kvmap_set__bool(x_583, x_584, x_585);
x_587 = lean::cnstr_get(x_202, 1);
lean::inc(x_587);
lean::dec(x_202);
x_590 = l_lean_elaborator_to__pexpr___main___closed__27;
x_591 = l_option_map___rarg(x_590, x_587);
x_592 = l_lean_elaborator_to__pexpr___main___closed__28;
x_593 = l_option_map___rarg(x_592, x_591);
x_594 = l_option_get__or__else___main___rarg(x_593, x_578);
x_595 = l_lean_elaborator_to__pexpr___main___closed__29;
x_596 = l_lean_kvmap_set__name(x_586, x_595, x_594);
x_597 = l_list_append___rarg(x_504, x_573);
x_598 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_597);
x_599 = lean_expr_mk_mdata(x_596, x_598);
if (lean::is_scalar(x_210)) {
 x_600 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_600 = x_210;
}
lean::cnstr_set(x_600, 0, x_599);
lean::cnstr_set(x_600, 1, x_575);
x_14 = x_600;
goto lbl_15;
}
}
}
else
{
obj* x_602; obj* x_603; obj* x_606; obj* x_607; obj* x_609; 
lean::dec(x_330);
x_602 = l_lean_parser_term_struct__inst__item_has__view;
x_603 = lean::cnstr_get(x_602, 1);
lean::inc(x_603);
lean::dec(x_602);
x_606 = lean::apply_1(x_603, x_333);
x_607 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
x_609 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_606, x_607, x_1, x_2);
if (lean::obj_tag(x_609) == 0)
{
obj* x_619; obj* x_621; obj* x_622; 
lean::dec(x_332);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_212);
lean::dec(x_210);
lean::dec(x_206);
x_619 = lean::cnstr_get(x_609, 0);
lean::inc(x_619);
if (lean::is_exclusive(x_609)) {
 lean::cnstr_release(x_609, 0);
 x_621 = x_609;
} else {
 lean::dec(x_609);
 x_621 = lean::box(0);
}
if (lean::is_scalar(x_621)) {
 x_622 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_622 = x_621;
}
lean::cnstr_set(x_622, 0, x_619);
return x_622;
}
else
{
obj* x_623; obj* x_625; obj* x_626; obj* x_628; obj* x_633; 
x_623 = lean::cnstr_get(x_609, 0);
lean::inc(x_623);
if (lean::is_exclusive(x_609)) {
 lean::cnstr_release(x_609, 0);
 x_625 = x_609;
} else {
 lean::dec(x_609);
 x_625 = lean::box(0);
}
x_626 = lean::cnstr_get(x_623, 0);
lean::inc(x_626);
x_628 = lean::cnstr_get(x_623, 1);
lean::inc(x_628);
lean::dec(x_623);
lean::inc(x_1);
lean::inc(x_0);
x_633 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_206, x_1, x_628);
if (lean::obj_tag(x_633) == 0)
{
obj* x_643; obj* x_646; 
lean::dec(x_332);
lean::dec(x_626);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_212);
lean::dec(x_210);
x_643 = lean::cnstr_get(x_633, 0);
lean::inc(x_643);
lean::dec(x_633);
if (lean::is_scalar(x_625)) {
 x_646 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_646 = x_625;
 lean::cnstr_set_tag(x_625, 0);
}
lean::cnstr_set(x_646, 0, x_643);
return x_646;
}
else
{
obj* x_647; obj* x_650; obj* x_652; obj* x_655; obj* x_659; 
x_647 = lean::cnstr_get(x_633, 0);
lean::inc(x_647);
lean::dec(x_633);
x_650 = lean::cnstr_get(x_647, 0);
lean::inc(x_650);
x_652 = lean::cnstr_get(x_647, 1);
lean::inc(x_652);
lean::dec(x_647);
lean::inc(x_1);
lean::inc(x_0);
x_659 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_212, x_1, x_652);
if (lean::obj_tag(x_659) == 0)
{
obj* x_669; obj* x_672; 
lean::dec(x_332);
lean::dec(x_626);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_650);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
x_669 = lean::cnstr_get(x_659, 0);
lean::inc(x_669);
lean::dec(x_659);
if (lean::is_scalar(x_625)) {
 x_672 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_672 = x_625;
 lean::cnstr_set_tag(x_625, 0);
}
lean::cnstr_set(x_672, 0, x_669);
return x_672;
}
else
{
obj* x_673; obj* x_676; obj* x_678; obj* x_681; 
x_673 = lean::cnstr_get(x_659, 0);
lean::inc(x_673);
lean::dec(x_659);
x_676 = lean::cnstr_get(x_673, 0);
lean::inc(x_676);
x_678 = lean::cnstr_get(x_673, 1);
lean::inc(x_678);
lean::dec(x_673);
x_681 = lean::cnstr_get(x_202, 2);
lean::inc(x_681);
if (lean::obj_tag(x_681) == 0)
{
obj* x_685; 
lean::dec(x_332);
lean::dec(x_625);
if (lean::is_scalar(x_216)) {
 x_685 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_685 = x_216;
}
lean::cnstr_set(x_685, 0, x_676);
lean::cnstr_set(x_685, 1, x_678);
x_655 = x_685;
goto lbl_656;
}
else
{
obj* x_686; obj* x_689; obj* x_693; 
x_686 = lean::cnstr_get(x_681, 0);
lean::inc(x_686);
lean::dec(x_681);
x_689 = lean::cnstr_get(x_686, 0);
lean::inc(x_689);
lean::dec(x_686);
lean::inc(x_1);
x_693 = l_lean_elaborator_to__pexpr___main(x_689, x_1, x_678);
if (lean::obj_tag(x_693) == 0)
{
obj* x_704; obj* x_707; 
lean::dec(x_332);
lean::dec(x_626);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_650);
lean::dec(x_676);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_210);
x_704 = lean::cnstr_get(x_693, 0);
lean::inc(x_704);
lean::dec(x_693);
if (lean::is_scalar(x_625)) {
 x_707 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_707 = x_625;
 lean::cnstr_set_tag(x_625, 0);
}
lean::cnstr_set(x_707, 0, x_704);
return x_707;
}
else
{
obj* x_709; obj* x_712; obj* x_714; obj* x_717; obj* x_718; obj* x_719; obj* x_720; 
lean::dec(x_625);
x_709 = lean::cnstr_get(x_693, 0);
lean::inc(x_709);
lean::dec(x_693);
x_712 = lean::cnstr_get(x_709, 0);
lean::inc(x_712);
x_714 = lean::cnstr_get(x_709, 1);
lean::inc(x_714);
lean::dec(x_709);
x_717 = lean::box(0);
if (lean::is_scalar(x_332)) {
 x_718 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_718 = x_332;
}
lean::cnstr_set(x_718, 0, x_712);
lean::cnstr_set(x_718, 1, x_717);
x_719 = l_list_append___rarg(x_676, x_718);
if (lean::is_scalar(x_216)) {
 x_720 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_720 = x_216;
}
lean::cnstr_set(x_720, 0, x_719);
lean::cnstr_set(x_720, 1, x_714);
x_655 = x_720;
goto lbl_656;
}
}
}
lbl_656:
{
obj* x_721; obj* x_723; obj* x_726; obj* x_727; obj* x_729; obj* x_730; obj* x_731; obj* x_732; uint8 x_733; obj* x_735; obj* x_736; obj* x_739; obj* x_740; obj* x_741; obj* x_742; obj* x_743; obj* x_744; obj* x_745; obj* x_746; obj* x_747; obj* x_748; obj* x_749; 
x_721 = lean::cnstr_get(x_655, 0);
lean::inc(x_721);
x_723 = lean::cnstr_get(x_655, 1);
lean::inc(x_723);
lean::dec(x_655);
x_726 = lean::box(0);
x_727 = lean::mk_nat_obj(0u);
lean::inc(x_650);
x_729 = l_list_length__aux___main___rarg(x_650, x_727);
x_730 = l_lean_elaborator_to__pexpr___main___closed__25;
x_731 = l_lean_kvmap_set__nat(x_726, x_730, x_729);
x_732 = l_lean_elaborator_to__pexpr___main___closed__26;
x_733 = lean::unbox(x_626);
lean::dec(x_626);
x_735 = l_lean_kvmap_set__bool(x_731, x_732, x_733);
x_736 = lean::cnstr_get(x_202, 1);
lean::inc(x_736);
lean::dec(x_202);
x_739 = l_lean_elaborator_to__pexpr___main___closed__27;
x_740 = l_option_map___rarg(x_739, x_736);
x_741 = l_lean_elaborator_to__pexpr___main___closed__28;
x_742 = l_option_map___rarg(x_741, x_740);
x_743 = l_option_get__or__else___main___rarg(x_742, x_726);
x_744 = l_lean_elaborator_to__pexpr___main___closed__29;
x_745 = l_lean_kvmap_set__name(x_735, x_744, x_743);
x_746 = l_list_append___rarg(x_650, x_721);
x_747 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_746);
x_748 = lean_expr_mk_mdata(x_745, x_747);
if (lean::is_scalar(x_210)) {
 x_749 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_749 = x_210;
}
lean::cnstr_set(x_749, 0, x_748);
lean::cnstr_set(x_749, 1, x_723);
x_14 = x_749;
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
obj* x_752; 
lean::inc(x_1);
lean::inc(x_9);
x_752 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_9, x_1, x_2);
if (lean::obj_tag(x_752) == 0)
{
obj* x_757; obj* x_759; obj* x_760; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_757 = lean::cnstr_get(x_752, 0);
lean::inc(x_757);
if (lean::is_exclusive(x_752)) {
 lean::cnstr_release(x_752, 0);
 x_759 = x_752;
} else {
 lean::dec(x_752);
 x_759 = lean::box(0);
}
if (lean::is_scalar(x_759)) {
 x_760 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_760 = x_759;
}
lean::cnstr_set(x_760, 0, x_757);
return x_760;
}
else
{
obj* x_761; obj* x_764; obj* x_766; obj* x_768; obj* x_769; obj* x_770; 
x_761 = lean::cnstr_get(x_752, 0);
lean::inc(x_761);
lean::dec(x_752);
x_764 = lean::cnstr_get(x_761, 0);
lean::inc(x_764);
x_766 = lean::cnstr_get(x_761, 1);
lean::inc(x_766);
if (lean::is_exclusive(x_761)) {
 lean::cnstr_release(x_761, 0);
 lean::cnstr_release(x_761, 1);
 x_768 = x_761;
} else {
 lean::dec(x_761);
 x_768 = lean::box(0);
}
x_769 = l_list_reverse___rarg(x_764);
if (lean::is_scalar(x_768)) {
 x_770 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_770 = x_768;
}
lean::cnstr_set(x_770, 0, x_769);
lean::cnstr_set(x_770, 1, x_766);
x_16 = x_770;
goto lbl_17;
}
}
}
else
{
obj* x_773; obj* x_774; obj* x_778; obj* x_779; obj* x_780; obj* x_781; obj* x_782; obj* x_783; 
lean::dec(x_9);
lean::dec(x_7);
x_773 = l_lean_parser_string__lit_has__view;
x_774 = lean::cnstr_get(x_773, 0);
lean::inc(x_774);
lean::dec(x_773);
lean::inc(x_0);
x_778 = lean::apply_1(x_774, x_0);
x_779 = l_lean_parser_string__lit_view_value(x_778);
x_780 = l_lean_elaborator_to__pexpr___main___closed__31;
x_781 = l_option_get__or__else___main___rarg(x_779, x_780);
x_782 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_782, 0, x_781);
x_783 = lean_expr_mk_lit(x_782);
if (x_21 == 0)
{
obj* x_784; 
x_784 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_784) == 0)
{
obj* x_786; obj* x_787; 
lean::dec(x_1);
x_786 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_786, 0, x_783);
lean::cnstr_set(x_786, 1, x_2);
x_787 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_787, 0, x_786);
return x_787;
}
else
{
obj* x_788; obj* x_791; obj* x_794; obj* x_797; obj* x_798; obj* x_799; obj* x_801; obj* x_802; obj* x_803; obj* x_806; obj* x_807; obj* x_808; obj* x_809; obj* x_810; 
x_788 = lean::cnstr_get(x_784, 0);
lean::inc(x_788);
lean::dec(x_784);
x_791 = lean::cnstr_get(x_1, 0);
lean::inc(x_791);
lean::dec(x_1);
x_794 = lean::cnstr_get(x_791, 2);
lean::inc(x_794);
lean::dec(x_791);
x_797 = l_lean_file__map_to__position(x_794, x_788);
x_798 = lean::box(0);
x_799 = lean::cnstr_get(x_797, 1);
lean::inc(x_799);
x_801 = l_lean_elaborator_to__pexpr___main___closed__3;
x_802 = l_lean_kvmap_set__nat(x_798, x_801, x_799);
x_803 = lean::cnstr_get(x_797, 0);
lean::inc(x_803);
lean::dec(x_797);
x_806 = l_lean_elaborator_to__pexpr___main___closed__4;
x_807 = l_lean_kvmap_set__nat(x_802, x_806, x_803);
x_808 = lean_expr_mk_mdata(x_807, x_783);
x_809 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_809, 0, x_808);
lean::cnstr_set(x_809, 1, x_2);
x_810 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_810, 0, x_809);
return x_810;
}
}
else
{
obj* x_813; obj* x_814; 
lean::dec(x_1);
lean::dec(x_0);
x_813 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_813, 0, x_783);
lean::cnstr_set(x_813, 1, x_2);
x_814 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_814, 0, x_813);
return x_814;
}
}
}
else
{
obj* x_817; obj* x_818; obj* x_822; obj* x_823; obj* x_824; obj* x_825; 
lean::dec(x_9);
lean::dec(x_7);
x_817 = l_lean_parser_number_has__view;
x_818 = lean::cnstr_get(x_817, 0);
lean::inc(x_818);
lean::dec(x_817);
lean::inc(x_0);
x_822 = lean::apply_1(x_818, x_0);
x_823 = l_lean_parser_number_view_to__nat___main(x_822);
x_824 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_824, 0, x_823);
x_825 = lean_expr_mk_lit(x_824);
if (x_21 == 0)
{
obj* x_826; 
x_826 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_826) == 0)
{
obj* x_828; obj* x_829; 
lean::dec(x_1);
x_828 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_828, 0, x_825);
lean::cnstr_set(x_828, 1, x_2);
x_829 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_829, 0, x_828);
return x_829;
}
else
{
obj* x_830; obj* x_833; obj* x_836; obj* x_839; obj* x_840; obj* x_841; obj* x_843; obj* x_844; obj* x_845; obj* x_848; obj* x_849; obj* x_850; obj* x_851; obj* x_852; 
x_830 = lean::cnstr_get(x_826, 0);
lean::inc(x_830);
lean::dec(x_826);
x_833 = lean::cnstr_get(x_1, 0);
lean::inc(x_833);
lean::dec(x_1);
x_836 = lean::cnstr_get(x_833, 2);
lean::inc(x_836);
lean::dec(x_833);
x_839 = l_lean_file__map_to__position(x_836, x_830);
x_840 = lean::box(0);
x_841 = lean::cnstr_get(x_839, 1);
lean::inc(x_841);
x_843 = l_lean_elaborator_to__pexpr___main___closed__3;
x_844 = l_lean_kvmap_set__nat(x_840, x_843, x_841);
x_845 = lean::cnstr_get(x_839, 0);
lean::inc(x_845);
lean::dec(x_839);
x_848 = l_lean_elaborator_to__pexpr___main___closed__4;
x_849 = l_lean_kvmap_set__nat(x_844, x_848, x_845);
x_850 = lean_expr_mk_mdata(x_849, x_825);
x_851 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_851, 0, x_850);
lean::cnstr_set(x_851, 1, x_2);
x_852 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_852, 0, x_851);
return x_852;
}
}
else
{
obj* x_855; obj* x_856; 
lean::dec(x_1);
lean::dec(x_0);
x_855 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_855, 0, x_825);
lean::cnstr_set(x_855, 1, x_2);
x_856 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_856, 0, x_855);
return x_856;
}
}
}
else
{
obj* x_858; obj* x_859; obj* x_863; obj* x_864; obj* x_868; 
lean::dec(x_9);
x_858 = l_lean_parser_term_borrowed_has__view;
x_859 = lean::cnstr_get(x_858, 0);
lean::inc(x_859);
lean::dec(x_858);
lean::inc(x_0);
x_863 = lean::apply_1(x_859, x_0);
x_864 = lean::cnstr_get(x_863, 1);
lean::inc(x_864);
lean::dec(x_863);
lean::inc(x_1);
x_868 = l_lean_elaborator_to__pexpr___main(x_864, x_1, x_2);
if (lean::obj_tag(x_868) == 0)
{
obj* x_872; obj* x_874; obj* x_875; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_872 = lean::cnstr_get(x_868, 0);
lean::inc(x_872);
if (lean::is_exclusive(x_868)) {
 lean::cnstr_release(x_868, 0);
 x_874 = x_868;
} else {
 lean::dec(x_868);
 x_874 = lean::box(0);
}
if (lean::is_scalar(x_874)) {
 x_875 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_875 = x_874;
}
lean::cnstr_set(x_875, 0, x_872);
return x_875;
}
else
{
obj* x_876; obj* x_879; obj* x_881; obj* x_883; obj* x_884; obj* x_885; obj* x_886; 
x_876 = lean::cnstr_get(x_868, 0);
lean::inc(x_876);
lean::dec(x_868);
x_879 = lean::cnstr_get(x_876, 0);
lean::inc(x_879);
x_881 = lean::cnstr_get(x_876, 1);
lean::inc(x_881);
if (lean::is_exclusive(x_876)) {
 lean::cnstr_release(x_876, 0);
 lean::cnstr_release(x_876, 1);
 x_883 = x_876;
} else {
 lean::dec(x_876);
 x_883 = lean::box(0);
}
x_884 = l_lean_elaborator_to__pexpr___main___closed__32;
x_885 = l_lean_elaborator_expr_mk__annotation(x_884, x_879);
if (lean::is_scalar(x_883)) {
 x_886 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_886 = x_883;
}
lean::cnstr_set(x_886, 0, x_885);
lean::cnstr_set(x_886, 1, x_881);
x_14 = x_886;
goto lbl_15;
}
}
}
else
{
obj* x_888; obj* x_889; obj* x_893; obj* x_894; obj* x_898; 
lean::dec(x_9);
x_888 = l_lean_parser_term_inaccessible_has__view;
x_889 = lean::cnstr_get(x_888, 0);
lean::inc(x_889);
lean::dec(x_888);
lean::inc(x_0);
x_893 = lean::apply_1(x_889, x_0);
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
if (lean::is_exclusive(x_898)) {
 lean::cnstr_release(x_898, 0);
 x_904 = x_898;
} else {
 lean::dec(x_898);
 x_904 = lean::box(0);
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
obj* x_906; obj* x_909; obj* x_911; obj* x_913; obj* x_914; obj* x_915; obj* x_916; 
x_906 = lean::cnstr_get(x_898, 0);
lean::inc(x_906);
lean::dec(x_898);
x_909 = lean::cnstr_get(x_906, 0);
lean::inc(x_909);
x_911 = lean::cnstr_get(x_906, 1);
lean::inc(x_911);
if (lean::is_exclusive(x_906)) {
 lean::cnstr_release(x_906, 0);
 lean::cnstr_release(x_906, 1);
 x_913 = x_906;
} else {
 lean::dec(x_906);
 x_913 = lean::box(0);
}
x_914 = l_lean_elaborator_to__pexpr___main___closed__33;
x_915 = l_lean_elaborator_expr_mk__annotation(x_914, x_909);
if (lean::is_scalar(x_913)) {
 x_916 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_916 = x_913;
}
lean::cnstr_set(x_916, 0, x_915);
lean::cnstr_set(x_916, 1, x_911);
x_14 = x_916;
goto lbl_15;
}
}
}
else
{
obj* x_918; obj* x_919; obj* x_923; obj* x_924; obj* x_926; obj* x_927; obj* x_930; obj* x_933; 
lean::dec(x_9);
x_918 = l_lean_parser_term_explicit_has__view;
x_919 = lean::cnstr_get(x_918, 0);
lean::inc(x_919);
lean::dec(x_918);
lean::inc(x_0);
x_923 = lean::apply_1(x_919, x_0);
x_924 = lean::cnstr_get(x_923, 0);
lean::inc(x_924);
x_926 = l_lean_parser_ident__univs_has__view;
x_927 = lean::cnstr_get(x_926, 1);
lean::inc(x_927);
lean::dec(x_926);
x_930 = lean::cnstr_get(x_923, 1);
lean::inc(x_930);
lean::dec(x_923);
x_933 = lean::apply_1(x_927, x_930);
if (lean::obj_tag(x_924) == 0)
{
obj* x_936; 
lean::dec(x_924);
lean::inc(x_1);
x_936 = l_lean_elaborator_to__pexpr___main(x_933, x_1, x_2);
if (lean::obj_tag(x_936) == 0)
{
obj* x_940; obj* x_942; obj* x_943; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_940 = lean::cnstr_get(x_936, 0);
lean::inc(x_940);
if (lean::is_exclusive(x_936)) {
 lean::cnstr_release(x_936, 0);
 x_942 = x_936;
} else {
 lean::dec(x_936);
 x_942 = lean::box(0);
}
if (lean::is_scalar(x_942)) {
 x_943 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_943 = x_942;
}
lean::cnstr_set(x_943, 0, x_940);
return x_943;
}
else
{
obj* x_944; obj* x_947; obj* x_949; obj* x_951; obj* x_952; obj* x_953; obj* x_954; 
x_944 = lean::cnstr_get(x_936, 0);
lean::inc(x_944);
lean::dec(x_936);
x_947 = lean::cnstr_get(x_944, 0);
lean::inc(x_947);
x_949 = lean::cnstr_get(x_944, 1);
lean::inc(x_949);
if (lean::is_exclusive(x_944)) {
 lean::cnstr_release(x_944, 0);
 lean::cnstr_release(x_944, 1);
 x_951 = x_944;
} else {
 lean::dec(x_944);
 x_951 = lean::box(0);
}
x_952 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
x_953 = l_lean_elaborator_expr_mk__annotation(x_952, x_947);
if (lean::is_scalar(x_951)) {
 x_954 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_954 = x_951;
}
lean::cnstr_set(x_954, 0, x_953);
lean::cnstr_set(x_954, 1, x_949);
x_14 = x_954;
goto lbl_15;
}
}
else
{
obj* x_957; 
lean::dec(x_924);
lean::inc(x_1);
x_957 = l_lean_elaborator_to__pexpr___main(x_933, x_1, x_2);
if (lean::obj_tag(x_957) == 0)
{
obj* x_961; obj* x_963; obj* x_964; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_961 = lean::cnstr_get(x_957, 0);
lean::inc(x_961);
if (lean::is_exclusive(x_957)) {
 lean::cnstr_release(x_957, 0);
 x_963 = x_957;
} else {
 lean::dec(x_957);
 x_963 = lean::box(0);
}
if (lean::is_scalar(x_963)) {
 x_964 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_964 = x_963;
}
lean::cnstr_set(x_964, 0, x_961);
return x_964;
}
else
{
obj* x_965; obj* x_968; obj* x_970; obj* x_972; obj* x_973; obj* x_974; obj* x_975; 
x_965 = lean::cnstr_get(x_957, 0);
lean::inc(x_965);
lean::dec(x_957);
x_968 = lean::cnstr_get(x_965, 0);
lean::inc(x_968);
x_970 = lean::cnstr_get(x_965, 1);
lean::inc(x_970);
if (lean::is_exclusive(x_965)) {
 lean::cnstr_release(x_965, 0);
 lean::cnstr_release(x_965, 1);
 x_972 = x_965;
} else {
 lean::dec(x_965);
 x_972 = lean::box(0);
}
x_973 = l_lean_elaborator_to__pexpr___main___closed__34;
x_974 = l_lean_elaborator_expr_mk__annotation(x_973, x_968);
if (lean::is_scalar(x_972)) {
 x_975 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_975 = x_972;
}
lean::cnstr_set(x_975, 0, x_974);
lean::cnstr_set(x_975, 1, x_970);
x_14 = x_975;
goto lbl_15;
}
}
}
}
else
{
obj* x_977; obj* x_978; obj* x_982; obj* x_983; obj* x_985; 
lean::dec(x_9);
x_977 = l_lean_parser_term_projection_has__view;
x_978 = lean::cnstr_get(x_977, 0);
lean::inc(x_978);
lean::dec(x_977);
lean::inc(x_0);
x_982 = lean::apply_1(x_978, x_0);
x_983 = lean::cnstr_get(x_982, 2);
lean::inc(x_983);
x_985 = lean::cnstr_get(x_982, 0);
lean::inc(x_985);
lean::dec(x_982);
if (lean::obj_tag(x_983) == 0)
{
obj* x_988; obj* x_992; 
x_988 = lean::cnstr_get(x_983, 0);
lean::inc(x_988);
lean::dec(x_983);
lean::inc(x_1);
x_992 = l_lean_elaborator_to__pexpr___main(x_985, x_1, x_2);
if (lean::obj_tag(x_992) == 0)
{
obj* x_997; obj* x_999; obj* x_1000; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_988);
x_997 = lean::cnstr_get(x_992, 0);
lean::inc(x_997);
if (lean::is_exclusive(x_992)) {
 lean::cnstr_release(x_992, 0);
 x_999 = x_992;
} else {
 lean::dec(x_992);
 x_999 = lean::box(0);
}
if (lean::is_scalar(x_999)) {
 x_1000 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1000 = x_999;
}
lean::cnstr_set(x_1000, 0, x_997);
return x_1000;
}
else
{
obj* x_1001; obj* x_1004; obj* x_1006; obj* x_1008; obj* x_1009; obj* x_1012; obj* x_1013; obj* x_1014; obj* x_1015; obj* x_1016; obj* x_1017; 
x_1001 = lean::cnstr_get(x_992, 0);
lean::inc(x_1001);
lean::dec(x_992);
x_1004 = lean::cnstr_get(x_1001, 0);
lean::inc(x_1004);
x_1006 = lean::cnstr_get(x_1001, 1);
lean::inc(x_1006);
if (lean::is_exclusive(x_1001)) {
 lean::cnstr_release(x_1001, 0);
 lean::cnstr_release(x_1001, 1);
 x_1008 = x_1001;
} else {
 lean::dec(x_1001);
 x_1008 = lean::box(0);
}
x_1009 = lean::cnstr_get(x_988, 2);
lean::inc(x_1009);
lean::dec(x_988);
x_1012 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1012, 0, x_1009);
x_1013 = lean::box(0);
x_1014 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1015 = l_lean_kvmap_insert__core___main(x_1013, x_1014, x_1012);
x_1016 = lean_expr_mk_mdata(x_1015, x_1004);
if (lean::is_scalar(x_1008)) {
 x_1017 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1017 = x_1008;
}
lean::cnstr_set(x_1017, 0, x_1016);
lean::cnstr_set(x_1017, 1, x_1006);
x_14 = x_1017;
goto lbl_15;
}
}
else
{
obj* x_1018; obj* x_1022; 
x_1018 = lean::cnstr_get(x_983, 0);
lean::inc(x_1018);
lean::dec(x_983);
lean::inc(x_1);
x_1022 = l_lean_elaborator_to__pexpr___main(x_985, x_1, x_2);
if (lean::obj_tag(x_1022) == 0)
{
obj* x_1027; obj* x_1029; obj* x_1030; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1018);
x_1027 = lean::cnstr_get(x_1022, 0);
lean::inc(x_1027);
if (lean::is_exclusive(x_1022)) {
 lean::cnstr_release(x_1022, 0);
 x_1029 = x_1022;
} else {
 lean::dec(x_1022);
 x_1029 = lean::box(0);
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
obj* x_1031; obj* x_1034; obj* x_1036; obj* x_1038; obj* x_1039; obj* x_1040; obj* x_1041; obj* x_1042; obj* x_1043; obj* x_1044; obj* x_1045; 
x_1031 = lean::cnstr_get(x_1022, 0);
lean::inc(x_1031);
lean::dec(x_1022);
x_1034 = lean::cnstr_get(x_1031, 0);
lean::inc(x_1034);
x_1036 = lean::cnstr_get(x_1031, 1);
lean::inc(x_1036);
if (lean::is_exclusive(x_1031)) {
 lean::cnstr_release(x_1031, 0);
 lean::cnstr_release(x_1031, 1);
 x_1038 = x_1031;
} else {
 lean::dec(x_1031);
 x_1038 = lean::box(0);
}
x_1039 = l_lean_parser_number_view_to__nat___main(x_1018);
x_1040 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1040, 0, x_1039);
x_1041 = lean::box(0);
x_1042 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1043 = l_lean_kvmap_insert__core___main(x_1041, x_1042, x_1040);
x_1044 = lean_expr_mk_mdata(x_1043, x_1034);
if (lean::is_scalar(x_1038)) {
 x_1045 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1045 = x_1038;
}
lean::cnstr_set(x_1045, 0, x_1044);
lean::cnstr_set(x_1045, 1, x_1036);
x_14 = x_1045;
goto lbl_15;
}
}
}
}
else
{
obj* x_1047; obj* x_1048; obj* x_1052; obj* x_1053; 
lean::dec(x_9);
x_1047 = l_lean_parser_term_let_has__view;
x_1048 = lean::cnstr_get(x_1047, 0);
lean::inc(x_1048);
lean::dec(x_1047);
lean::inc(x_0);
x_1052 = lean::apply_1(x_1048, x_0);
x_1053 = lean::cnstr_get(x_1052, 1);
lean::inc(x_1053);
if (lean::obj_tag(x_1053) == 0)
{
obj* x_1055; obj* x_1058; obj* x_1060; obj* x_1062; 
x_1055 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1055);
lean::dec(x_1053);
x_1058 = lean::cnstr_get(x_1055, 0);
lean::inc(x_1058);
x_1060 = lean::cnstr_get(x_1055, 1);
lean::inc(x_1060);
x_1062 = lean::cnstr_get(x_1055, 2);
lean::inc(x_1062);
lean::dec(x_1055);
if (lean::obj_tag(x_1060) == 0)
{
if (lean::obj_tag(x_1062) == 0)
{
obj* x_1067; obj* x_1070; 
lean::dec(x_1058);
lean::dec(x_1052);
x_1067 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_0);
x_1070 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1067, x_1, x_2);
if (lean::obj_tag(x_1070) == 0)
{
obj* x_1074; obj* x_1076; obj* x_1077; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1074 = lean::cnstr_get(x_1070, 0);
lean::inc(x_1074);
if (lean::is_exclusive(x_1070)) {
 lean::cnstr_release(x_1070, 0);
 x_1076 = x_1070;
} else {
 lean::dec(x_1070);
 x_1076 = lean::box(0);
}
if (lean::is_scalar(x_1076)) {
 x_1077 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1077 = x_1076;
}
lean::cnstr_set(x_1077, 0, x_1074);
return x_1077;
}
else
{
obj* x_1078; 
x_1078 = lean::cnstr_get(x_1070, 0);
lean::inc(x_1078);
lean::dec(x_1070);
x_14 = x_1078;
goto lbl_15;
}
}
else
{
obj* x_1081; obj* x_1084; obj* x_1088; 
x_1081 = lean::cnstr_get(x_1062, 0);
lean::inc(x_1081);
lean::dec(x_1062);
x_1084 = lean::cnstr_get(x_1081, 1);
lean::inc(x_1084);
lean::dec(x_1081);
lean::inc(x_1);
x_1088 = l_lean_elaborator_to__pexpr___main(x_1084, x_1, x_2);
if (lean::obj_tag(x_1088) == 0)
{
obj* x_1094; obj* x_1096; obj* x_1097; 
lean::dec(x_1058);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1052);
x_1094 = lean::cnstr_get(x_1088, 0);
lean::inc(x_1094);
if (lean::is_exclusive(x_1088)) {
 lean::cnstr_release(x_1088, 0);
 x_1096 = x_1088;
} else {
 lean::dec(x_1088);
 x_1096 = lean::box(0);
}
if (lean::is_scalar(x_1096)) {
 x_1097 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1097 = x_1096;
}
lean::cnstr_set(x_1097, 0, x_1094);
return x_1097;
}
else
{
obj* x_1098; obj* x_1100; obj* x_1101; obj* x_1103; obj* x_1105; obj* x_1106; obj* x_1109; 
x_1098 = lean::cnstr_get(x_1088, 0);
lean::inc(x_1098);
if (lean::is_exclusive(x_1088)) {
 lean::cnstr_release(x_1088, 0);
 x_1100 = x_1088;
} else {
 lean::dec(x_1088);
 x_1100 = lean::box(0);
}
x_1101 = lean::cnstr_get(x_1098, 0);
lean::inc(x_1101);
x_1103 = lean::cnstr_get(x_1098, 1);
lean::inc(x_1103);
if (lean::is_exclusive(x_1098)) {
 lean::cnstr_release(x_1098, 0);
 lean::cnstr_release(x_1098, 1);
 x_1105 = x_1098;
} else {
 lean::dec(x_1098);
 x_1105 = lean::box(0);
}
x_1106 = lean::cnstr_get(x_1052, 3);
lean::inc(x_1106);
lean::inc(x_1);
x_1109 = l_lean_elaborator_to__pexpr___main(x_1106, x_1, x_1103);
if (lean::obj_tag(x_1109) == 0)
{
obj* x_1117; obj* x_1120; 
lean::dec(x_1058);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1105);
lean::dec(x_1101);
lean::dec(x_1052);
x_1117 = lean::cnstr_get(x_1109, 0);
lean::inc(x_1117);
lean::dec(x_1109);
if (lean::is_scalar(x_1100)) {
 x_1120 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1120 = x_1100;
 lean::cnstr_set_tag(x_1100, 0);
}
lean::cnstr_set(x_1120, 0, x_1117);
return x_1120;
}
else
{
obj* x_1121; obj* x_1124; obj* x_1126; obj* x_1129; obj* x_1133; 
x_1121 = lean::cnstr_get(x_1109, 0);
lean::inc(x_1121);
lean::dec(x_1109);
x_1124 = lean::cnstr_get(x_1121, 0);
lean::inc(x_1124);
x_1126 = lean::cnstr_get(x_1121, 1);
lean::inc(x_1126);
lean::dec(x_1121);
x_1129 = lean::cnstr_get(x_1052, 5);
lean::inc(x_1129);
lean::dec(x_1052);
lean::inc(x_1);
x_1133 = l_lean_elaborator_to__pexpr___main(x_1129, x_1, x_1126);
if (lean::obj_tag(x_1133) == 0)
{
obj* x_1141; obj* x_1144; 
lean::dec(x_1124);
lean::dec(x_1058);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1105);
lean::dec(x_1101);
x_1141 = lean::cnstr_get(x_1133, 0);
lean::inc(x_1141);
lean::dec(x_1133);
if (lean::is_scalar(x_1100)) {
 x_1144 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1144 = x_1100;
 lean::cnstr_set_tag(x_1100, 0);
}
lean::cnstr_set(x_1144, 0, x_1141);
return x_1144;
}
else
{
obj* x_1146; obj* x_1149; obj* x_1151; obj* x_1154; obj* x_1155; obj* x_1156; 
lean::dec(x_1100);
x_1146 = lean::cnstr_get(x_1133, 0);
lean::inc(x_1146);
lean::dec(x_1133);
x_1149 = lean::cnstr_get(x_1146, 0);
lean::inc(x_1149);
x_1151 = lean::cnstr_get(x_1146, 1);
lean::inc(x_1151);
lean::dec(x_1146);
x_1154 = l_lean_elaborator_mangle__ident(x_1058);
x_1155 = lean_expr_mk_let(x_1154, x_1101, x_1124, x_1149);
if (lean::is_scalar(x_1105)) {
 x_1156 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1156 = x_1105;
}
lean::cnstr_set(x_1156, 0, x_1155);
lean::cnstr_set(x_1156, 1, x_1151);
x_14 = x_1156;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1161; obj* x_1164; 
lean::dec(x_1062);
lean::dec(x_1060);
lean::dec(x_1058);
lean::dec(x_1052);
x_1161 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_0);
x_1164 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1161, x_1, x_2);
if (lean::obj_tag(x_1164) == 0)
{
obj* x_1168; obj* x_1170; obj* x_1171; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1168 = lean::cnstr_get(x_1164, 0);
lean::inc(x_1168);
if (lean::is_exclusive(x_1164)) {
 lean::cnstr_release(x_1164, 0);
 x_1170 = x_1164;
} else {
 lean::dec(x_1164);
 x_1170 = lean::box(0);
}
if (lean::is_scalar(x_1170)) {
 x_1171 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1171 = x_1170;
}
lean::cnstr_set(x_1171, 0, x_1168);
return x_1171;
}
else
{
obj* x_1172; 
x_1172 = lean::cnstr_get(x_1164, 0);
lean::inc(x_1172);
lean::dec(x_1164);
x_14 = x_1172;
goto lbl_15;
}
}
}
else
{
obj* x_1177; obj* x_1180; 
lean::dec(x_1052);
lean::dec(x_1053);
x_1177 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_0);
x_1180 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1177, x_1, x_2);
if (lean::obj_tag(x_1180) == 0)
{
obj* x_1184; obj* x_1186; obj* x_1187; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1184 = lean::cnstr_get(x_1180, 0);
lean::inc(x_1184);
if (lean::is_exclusive(x_1180)) {
 lean::cnstr_release(x_1180, 0);
 x_1186 = x_1180;
} else {
 lean::dec(x_1180);
 x_1186 = lean::box(0);
}
if (lean::is_scalar(x_1186)) {
 x_1187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1187 = x_1186;
}
lean::cnstr_set(x_1187, 0, x_1184);
return x_1187;
}
else
{
obj* x_1188; 
x_1188 = lean::cnstr_get(x_1180, 0);
lean::inc(x_1188);
lean::dec(x_1180);
x_14 = x_1188;
goto lbl_15;
}
}
}
}
else
{
obj* x_1192; obj* x_1193; obj* x_1197; obj* x_1198; obj* x_1201; 
lean::dec(x_9);
x_1192 = l_lean_parser_term_show_has__view;
x_1193 = lean::cnstr_get(x_1192, 0);
lean::inc(x_1193);
lean::dec(x_1192);
lean::inc(x_0);
x_1197 = lean::apply_1(x_1193, x_0);
x_1198 = lean::cnstr_get(x_1197, 1);
lean::inc(x_1198);
lean::inc(x_1);
x_1201 = l_lean_elaborator_to__pexpr___main(x_1198, x_1, x_2);
if (lean::obj_tag(x_1201) == 0)
{
obj* x_1206; obj* x_1208; obj* x_1209; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1197);
x_1206 = lean::cnstr_get(x_1201, 0);
lean::inc(x_1206);
if (lean::is_exclusive(x_1201)) {
 lean::cnstr_release(x_1201, 0);
 x_1208 = x_1201;
} else {
 lean::dec(x_1201);
 x_1208 = lean::box(0);
}
if (lean::is_scalar(x_1208)) {
 x_1209 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1209 = x_1208;
}
lean::cnstr_set(x_1209, 0, x_1206);
return x_1209;
}
else
{
obj* x_1210; obj* x_1212; obj* x_1213; obj* x_1215; obj* x_1217; obj* x_1218; obj* x_1221; obj* x_1225; 
x_1210 = lean::cnstr_get(x_1201, 0);
lean::inc(x_1210);
if (lean::is_exclusive(x_1201)) {
 lean::cnstr_release(x_1201, 0);
 x_1212 = x_1201;
} else {
 lean::dec(x_1201);
 x_1212 = lean::box(0);
}
x_1213 = lean::cnstr_get(x_1210, 0);
lean::inc(x_1213);
x_1215 = lean::cnstr_get(x_1210, 1);
lean::inc(x_1215);
if (lean::is_exclusive(x_1210)) {
 lean::cnstr_release(x_1210, 0);
 lean::cnstr_release(x_1210, 1);
 x_1217 = x_1210;
} else {
 lean::dec(x_1210);
 x_1217 = lean::box(0);
}
x_1218 = lean::cnstr_get(x_1197, 3);
lean::inc(x_1218);
lean::dec(x_1197);
x_1221 = lean::cnstr_get(x_1218, 1);
lean::inc(x_1221);
lean::dec(x_1218);
lean::inc(x_1);
x_1225 = l_lean_elaborator_to__pexpr___main(x_1221, x_1, x_1215);
if (lean::obj_tag(x_1225) == 0)
{
obj* x_1231; obj* x_1234; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1213);
lean::dec(x_1217);
x_1231 = lean::cnstr_get(x_1225, 0);
lean::inc(x_1231);
lean::dec(x_1225);
if (lean::is_scalar(x_1212)) {
 x_1234 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1234 = x_1212;
 lean::cnstr_set_tag(x_1212, 0);
}
lean::cnstr_set(x_1234, 0, x_1231);
return x_1234;
}
else
{
obj* x_1236; obj* x_1239; obj* x_1241; obj* x_1244; uint8 x_1245; obj* x_1246; obj* x_1247; obj* x_1248; obj* x_1249; obj* x_1250; obj* x_1251; 
lean::dec(x_1212);
x_1236 = lean::cnstr_get(x_1225, 0);
lean::inc(x_1236);
lean::dec(x_1225);
x_1239 = lean::cnstr_get(x_1236, 0);
lean::inc(x_1239);
x_1241 = lean::cnstr_get(x_1236, 1);
lean::inc(x_1241);
lean::dec(x_1236);
x_1244 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1245 = 0;
x_1246 = l_lean_elaborator_to__pexpr___main___closed__38;
x_1247 = lean_expr_mk_lambda(x_1244, x_1245, x_1213, x_1246);
x_1248 = lean_expr_mk_app(x_1247, x_1239);
x_1249 = l_lean_elaborator_to__pexpr___main___closed__39;
x_1250 = l_lean_elaborator_expr_mk__annotation(x_1249, x_1248);
if (lean::is_scalar(x_1217)) {
 x_1251 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1251 = x_1217;
}
lean::cnstr_set(x_1251, 0, x_1250);
lean::cnstr_set(x_1251, 1, x_1241);
x_14 = x_1251;
goto lbl_15;
}
}
}
}
else
{
obj* x_1253; obj* x_1254; obj* x_1258; obj* x_1259; obj* x_1261; obj* x_1264; 
lean::dec(x_9);
x_1253 = l_lean_parser_term_have_has__view;
x_1254 = lean::cnstr_get(x_1253, 0);
lean::inc(x_1254);
lean::dec(x_1253);
lean::inc(x_0);
x_1258 = lean::apply_1(x_1254, x_0);
x_1261 = lean::cnstr_get(x_1258, 2);
lean::inc(x_1261);
lean::inc(x_1);
x_1264 = l_lean_elaborator_to__pexpr___main(x_1261, x_1, x_2);
if (lean::obj_tag(x_1264) == 0)
{
obj* x_1269; obj* x_1271; obj* x_1272; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1258);
x_1269 = lean::cnstr_get(x_1264, 0);
lean::inc(x_1269);
if (lean::is_exclusive(x_1264)) {
 lean::cnstr_release(x_1264, 0);
 x_1271 = x_1264;
} else {
 lean::dec(x_1264);
 x_1271 = lean::box(0);
}
if (lean::is_scalar(x_1271)) {
 x_1272 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1272 = x_1271;
}
lean::cnstr_set(x_1272, 0, x_1269);
return x_1272;
}
else
{
obj* x_1273; obj* x_1275; obj* x_1276; obj* x_1278; obj* x_1280; obj* x_1281; obj* x_1284; 
x_1273 = lean::cnstr_get(x_1264, 0);
lean::inc(x_1273);
if (lean::is_exclusive(x_1264)) {
 lean::cnstr_release(x_1264, 0);
 x_1275 = x_1264;
} else {
 lean::dec(x_1264);
 x_1275 = lean::box(0);
}
x_1276 = lean::cnstr_get(x_1273, 0);
lean::inc(x_1276);
x_1278 = lean::cnstr_get(x_1273, 1);
lean::inc(x_1278);
if (lean::is_exclusive(x_1273)) {
 lean::cnstr_release(x_1273, 0);
 lean::cnstr_release(x_1273, 1);
 x_1280 = x_1273;
} else {
 lean::dec(x_1273);
 x_1280 = lean::box(0);
}
x_1281 = lean::cnstr_get(x_1258, 5);
lean::inc(x_1281);
lean::inc(x_1);
x_1284 = l_lean_elaborator_to__pexpr___main(x_1281, x_1, x_1278);
if (lean::obj_tag(x_1284) == 0)
{
obj* x_1291; obj* x_1294; 
lean::dec(x_1276);
lean::dec(x_1280);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1258);
x_1291 = lean::cnstr_get(x_1284, 0);
lean::inc(x_1291);
lean::dec(x_1284);
if (lean::is_scalar(x_1275)) {
 x_1294 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1294 = x_1275;
 lean::cnstr_set_tag(x_1275, 0);
}
lean::cnstr_set(x_1294, 0, x_1291);
return x_1294;
}
else
{
obj* x_1296; obj* x_1299; obj* x_1301; obj* x_1304; obj* x_1306; obj* x_1307; obj* x_1308; obj* x_1309; obj* x_1310; obj* x_1311; uint8 x_1312; obj* x_1313; obj* x_1314; 
lean::dec(x_1275);
x_1296 = lean::cnstr_get(x_1284, 0);
lean::inc(x_1296);
lean::dec(x_1284);
x_1299 = lean::cnstr_get(x_1296, 0);
lean::inc(x_1299);
x_1301 = lean::cnstr_get(x_1296, 1);
lean::inc(x_1301);
lean::dec(x_1296);
x_1304 = lean::cnstr_get(x_1258, 1);
lean::inc(x_1304);
x_1306 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1307 = l_option_map___rarg(x_1306, x_1304);
x_1308 = l_lean_elaborator_to__pexpr___main___closed__28;
x_1309 = l_option_map___rarg(x_1308, x_1307);
x_1310 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1311 = l_option_get__or__else___main___rarg(x_1309, x_1310);
x_1312 = 0;
x_1313 = lean_expr_mk_lambda(x_1311, x_1312, x_1276, x_1299);
if (lean::is_scalar(x_1280)) {
 x_1314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1314 = x_1280;
}
lean::cnstr_set(x_1314, 0, x_1313);
lean::cnstr_set(x_1314, 1, x_1301);
x_1259 = x_1314;
goto lbl_1260;
}
}
lbl_1260:
{
obj* x_1315; obj* x_1317; obj* x_1319; obj* x_1320; 
x_1315 = lean::cnstr_get(x_1259, 0);
lean::inc(x_1315);
x_1317 = lean::cnstr_get(x_1259, 1);
lean::inc(x_1317);
if (lean::is_exclusive(x_1259)) {
 lean::cnstr_release(x_1259, 0);
 lean::cnstr_release(x_1259, 1);
 x_1319 = x_1259;
} else {
 lean::dec(x_1259);
 x_1319 = lean::box(0);
}
x_1320 = lean::cnstr_get(x_1258, 3);
lean::inc(x_1320);
lean::dec(x_1258);
if (lean::obj_tag(x_1320) == 0)
{
obj* x_1323; obj* x_1326; obj* x_1330; 
x_1323 = lean::cnstr_get(x_1320, 0);
lean::inc(x_1323);
lean::dec(x_1320);
x_1326 = lean::cnstr_get(x_1323, 1);
lean::inc(x_1326);
lean::dec(x_1323);
lean::inc(x_1);
x_1330 = l_lean_elaborator_to__pexpr___main(x_1326, x_1, x_1317);
if (lean::obj_tag(x_1330) == 0)
{
obj* x_1336; obj* x_1338; obj* x_1339; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1315);
lean::dec(x_1319);
x_1336 = lean::cnstr_get(x_1330, 0);
lean::inc(x_1336);
if (lean::is_exclusive(x_1330)) {
 lean::cnstr_release(x_1330, 0);
 x_1338 = x_1330;
} else {
 lean::dec(x_1330);
 x_1338 = lean::box(0);
}
if (lean::is_scalar(x_1338)) {
 x_1339 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1339 = x_1338;
}
lean::cnstr_set(x_1339, 0, x_1336);
return x_1339;
}
else
{
obj* x_1340; obj* x_1343; obj* x_1345; obj* x_1348; obj* x_1349; obj* x_1350; obj* x_1351; 
x_1340 = lean::cnstr_get(x_1330, 0);
lean::inc(x_1340);
lean::dec(x_1330);
x_1343 = lean::cnstr_get(x_1340, 0);
lean::inc(x_1343);
x_1345 = lean::cnstr_get(x_1340, 1);
lean::inc(x_1345);
lean::dec(x_1340);
x_1348 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1349 = l_lean_elaborator_expr_mk__annotation(x_1348, x_1315);
x_1350 = lean_expr_mk_app(x_1349, x_1343);
if (lean::is_scalar(x_1319)) {
 x_1351 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1351 = x_1319;
}
lean::cnstr_set(x_1351, 0, x_1350);
lean::cnstr_set(x_1351, 1, x_1345);
x_14 = x_1351;
goto lbl_15;
}
}
else
{
obj* x_1352; obj* x_1355; obj* x_1358; obj* x_1362; 
x_1352 = lean::cnstr_get(x_1320, 0);
lean::inc(x_1352);
lean::dec(x_1320);
x_1355 = lean::cnstr_get(x_1352, 1);
lean::inc(x_1355);
lean::dec(x_1352);
x_1358 = lean::cnstr_get(x_1355, 1);
lean::inc(x_1358);
lean::dec(x_1355);
lean::inc(x_1);
x_1362 = l_lean_elaborator_to__pexpr___main(x_1358, x_1, x_1317);
if (lean::obj_tag(x_1362) == 0)
{
obj* x_1368; obj* x_1370; obj* x_1371; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1315);
lean::dec(x_1319);
x_1368 = lean::cnstr_get(x_1362, 0);
lean::inc(x_1368);
if (lean::is_exclusive(x_1362)) {
 lean::cnstr_release(x_1362, 0);
 x_1370 = x_1362;
} else {
 lean::dec(x_1362);
 x_1370 = lean::box(0);
}
if (lean::is_scalar(x_1370)) {
 x_1371 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1371 = x_1370;
}
lean::cnstr_set(x_1371, 0, x_1368);
return x_1371;
}
else
{
obj* x_1372; obj* x_1375; obj* x_1377; obj* x_1380; obj* x_1381; obj* x_1382; obj* x_1383; 
x_1372 = lean::cnstr_get(x_1362, 0);
lean::inc(x_1372);
lean::dec(x_1362);
x_1375 = lean::cnstr_get(x_1372, 0);
lean::inc(x_1375);
x_1377 = lean::cnstr_get(x_1372, 1);
lean::inc(x_1377);
lean::dec(x_1372);
x_1380 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1381 = l_lean_elaborator_expr_mk__annotation(x_1380, x_1315);
x_1382 = lean_expr_mk_app(x_1381, x_1375);
if (lean::is_scalar(x_1319)) {
 x_1383 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1383 = x_1319;
}
lean::cnstr_set(x_1383, 0, x_1382);
lean::cnstr_set(x_1383, 1, x_1377);
x_14 = x_1383;
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
obj* x_1386; 
x_1386 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1386) == 0)
{
obj* x_1388; obj* x_1389; obj* x_1390; 
lean::dec(x_1);
x_1388 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1389 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1389, 0, x_1388);
lean::cnstr_set(x_1389, 1, x_2);
x_1390 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1390, 0, x_1389);
return x_1390;
}
else
{
obj* x_1391; obj* x_1394; obj* x_1397; obj* x_1400; obj* x_1401; obj* x_1402; obj* x_1404; obj* x_1405; obj* x_1406; obj* x_1409; obj* x_1410; obj* x_1411; obj* x_1412; obj* x_1413; obj* x_1414; 
x_1391 = lean::cnstr_get(x_1386, 0);
lean::inc(x_1391);
lean::dec(x_1386);
x_1394 = lean::cnstr_get(x_1, 0);
lean::inc(x_1394);
lean::dec(x_1);
x_1397 = lean::cnstr_get(x_1394, 2);
lean::inc(x_1397);
lean::dec(x_1394);
x_1400 = l_lean_file__map_to__position(x_1397, x_1391);
x_1401 = lean::box(0);
x_1402 = lean::cnstr_get(x_1400, 1);
lean::inc(x_1402);
x_1404 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1405 = l_lean_kvmap_set__nat(x_1401, x_1404, x_1402);
x_1406 = lean::cnstr_get(x_1400, 0);
lean::inc(x_1406);
lean::dec(x_1400);
x_1409 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1410 = l_lean_kvmap_set__nat(x_1405, x_1409, x_1406);
x_1411 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1412 = lean_expr_mk_mdata(x_1410, x_1411);
x_1413 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1413, 0, x_1412);
lean::cnstr_set(x_1413, 1, x_2);
x_1414 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1414, 0, x_1413);
return x_1414;
}
}
else
{
obj* x_1417; obj* x_1418; obj* x_1419; 
lean::dec(x_1);
lean::dec(x_0);
x_1417 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1418 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1418, 0, x_1417);
lean::cnstr_set(x_1418, 1, x_2);
x_1419 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1419, 0, x_1418);
return x_1419;
}
}
}
else
{
obj* x_1421; obj* x_1422; obj* x_1426; obj* x_1427; obj* x_1430; obj* x_1431; obj* x_1432; obj* x_1434; 
lean::dec(x_9);
x_1421 = l_lean_parser_term_anonymous__constructor_has__view;
x_1422 = lean::cnstr_get(x_1421, 0);
lean::inc(x_1422);
lean::dec(x_1421);
lean::inc(x_0);
x_1426 = lean::apply_1(x_1422, x_0);
x_1427 = lean::cnstr_get(x_1426, 1);
lean::inc(x_1427);
lean::dec(x_1426);
x_1430 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_1427);
x_1431 = l_lean_expander_get__opt__type___main___closed__1;
x_1432 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_1431, x_1430);
lean::inc(x_1);
x_1434 = l_lean_elaborator_to__pexpr___main(x_1432, x_1, x_2);
if (lean::obj_tag(x_1434) == 0)
{
obj* x_1438; obj* x_1440; obj* x_1441; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1438 = lean::cnstr_get(x_1434, 0);
lean::inc(x_1438);
if (lean::is_exclusive(x_1434)) {
 lean::cnstr_release(x_1434, 0);
 x_1440 = x_1434;
} else {
 lean::dec(x_1434);
 x_1440 = lean::box(0);
}
if (lean::is_scalar(x_1440)) {
 x_1441 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1441 = x_1440;
}
lean::cnstr_set(x_1441, 0, x_1438);
return x_1441;
}
else
{
obj* x_1442; obj* x_1445; obj* x_1447; obj* x_1449; obj* x_1450; obj* x_1451; obj* x_1452; 
x_1442 = lean::cnstr_get(x_1434, 0);
lean::inc(x_1442);
lean::dec(x_1434);
x_1445 = lean::cnstr_get(x_1442, 0);
lean::inc(x_1445);
x_1447 = lean::cnstr_get(x_1442, 1);
lean::inc(x_1447);
if (lean::is_exclusive(x_1442)) {
 lean::cnstr_release(x_1442, 0);
 lean::cnstr_release(x_1442, 1);
 x_1449 = x_1442;
} else {
 lean::dec(x_1442);
 x_1449 = lean::box(0);
}
x_1450 = l_lean_elaborator_to__pexpr___main___closed__43;
x_1451 = l_lean_elaborator_expr_mk__annotation(x_1450, x_1445);
if (lean::is_scalar(x_1449)) {
 x_1452 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1452 = x_1449;
}
lean::cnstr_set(x_1452, 0, x_1451);
lean::cnstr_set(x_1452, 1, x_1447);
x_14 = x_1452;
goto lbl_15;
}
}
}
else
{
obj* x_1454; obj* x_1455; obj* x_1459; obj* x_1460; obj* x_1461; obj* x_1464; obj* x_1466; 
lean::dec(x_9);
x_1454 = l_lean_parser_term_sort__app_has__view;
x_1455 = lean::cnstr_get(x_1454, 0);
lean::inc(x_1455);
lean::dec(x_1454);
lean::inc(x_0);
x_1459 = lean::apply_1(x_1455, x_0);
x_1460 = l_lean_parser_term_sort_has__view;
x_1461 = lean::cnstr_get(x_1460, 0);
lean::inc(x_1461);
lean::dec(x_1460);
x_1464 = lean::cnstr_get(x_1459, 0);
lean::inc(x_1464);
x_1466 = lean::apply_1(x_1461, x_1464);
if (lean::obj_tag(x_1466) == 0)
{
obj* x_1468; obj* x_1472; 
lean::dec(x_1466);
x_1468 = lean::cnstr_get(x_1459, 1);
lean::inc(x_1468);
lean::dec(x_1459);
lean::inc(x_1);
x_1472 = l_lean_elaborator_to__level___main(x_1468, x_1, x_2);
if (lean::obj_tag(x_1472) == 0)
{
obj* x_1476; obj* x_1478; obj* x_1479; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1476 = lean::cnstr_get(x_1472, 0);
lean::inc(x_1476);
if (lean::is_exclusive(x_1472)) {
 lean::cnstr_release(x_1472, 0);
 x_1478 = x_1472;
} else {
 lean::dec(x_1472);
 x_1478 = lean::box(0);
}
if (lean::is_scalar(x_1478)) {
 x_1479 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1479 = x_1478;
}
lean::cnstr_set(x_1479, 0, x_1476);
return x_1479;
}
else
{
obj* x_1480; obj* x_1483; obj* x_1485; obj* x_1487; obj* x_1488; obj* x_1489; 
x_1480 = lean::cnstr_get(x_1472, 0);
lean::inc(x_1480);
lean::dec(x_1472);
x_1483 = lean::cnstr_get(x_1480, 0);
lean::inc(x_1483);
x_1485 = lean::cnstr_get(x_1480, 1);
lean::inc(x_1485);
if (lean::is_exclusive(x_1480)) {
 lean::cnstr_release(x_1480, 0);
 lean::cnstr_release(x_1480, 1);
 x_1487 = x_1480;
} else {
 lean::dec(x_1480);
 x_1487 = lean::box(0);
}
x_1488 = lean_expr_mk_sort(x_1483);
if (lean::is_scalar(x_1487)) {
 x_1489 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1489 = x_1487;
}
lean::cnstr_set(x_1489, 0, x_1488);
lean::cnstr_set(x_1489, 1, x_1485);
x_14 = x_1489;
goto lbl_15;
}
}
else
{
obj* x_1491; obj* x_1495; 
lean::dec(x_1466);
x_1491 = lean::cnstr_get(x_1459, 1);
lean::inc(x_1491);
lean::dec(x_1459);
lean::inc(x_1);
x_1495 = l_lean_elaborator_to__level___main(x_1491, x_1, x_2);
if (lean::obj_tag(x_1495) == 0)
{
obj* x_1499; obj* x_1501; obj* x_1502; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1499 = lean::cnstr_get(x_1495, 0);
lean::inc(x_1499);
if (lean::is_exclusive(x_1495)) {
 lean::cnstr_release(x_1495, 0);
 x_1501 = x_1495;
} else {
 lean::dec(x_1495);
 x_1501 = lean::box(0);
}
if (lean::is_scalar(x_1501)) {
 x_1502 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1502 = x_1501;
}
lean::cnstr_set(x_1502, 0, x_1499);
return x_1502;
}
else
{
obj* x_1503; obj* x_1506; obj* x_1508; obj* x_1510; obj* x_1511; obj* x_1512; obj* x_1513; 
x_1503 = lean::cnstr_get(x_1495, 0);
lean::inc(x_1503);
lean::dec(x_1495);
x_1506 = lean::cnstr_get(x_1503, 0);
lean::inc(x_1506);
x_1508 = lean::cnstr_get(x_1503, 1);
lean::inc(x_1508);
if (lean::is_exclusive(x_1503)) {
 lean::cnstr_release(x_1503, 0);
 lean::cnstr_release(x_1503, 1);
 x_1510 = x_1503;
} else {
 lean::dec(x_1503);
 x_1510 = lean::box(0);
}
x_1511 = level_mk_succ(x_1506);
x_1512 = lean_expr_mk_sort(x_1511);
if (lean::is_scalar(x_1510)) {
 x_1513 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1513 = x_1510;
}
lean::cnstr_set(x_1513, 0, x_1512);
lean::cnstr_set(x_1513, 1, x_1508);
x_14 = x_1513;
goto lbl_15;
}
}
}
}
else
{
obj* x_1516; obj* x_1517; obj* x_1521; 
lean::dec(x_9);
lean::dec(x_7);
x_1516 = l_lean_parser_term_sort_has__view;
x_1517 = lean::cnstr_get(x_1516, 0);
lean::inc(x_1517);
lean::dec(x_1516);
lean::inc(x_0);
x_1521 = lean::apply_1(x_1517, x_0);
if (lean::obj_tag(x_1521) == 0)
{
lean::dec(x_1521);
if (x_21 == 0)
{
obj* x_1523; 
x_1523 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1523) == 0)
{
obj* x_1525; obj* x_1526; obj* x_1527; 
lean::dec(x_1);
x_1525 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1526 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1526, 0, x_1525);
lean::cnstr_set(x_1526, 1, x_2);
x_1527 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1527, 0, x_1526);
return x_1527;
}
else
{
obj* x_1528; obj* x_1531; obj* x_1534; obj* x_1537; obj* x_1538; obj* x_1539; obj* x_1541; obj* x_1542; obj* x_1543; obj* x_1546; obj* x_1547; obj* x_1548; obj* x_1549; obj* x_1550; obj* x_1551; 
x_1528 = lean::cnstr_get(x_1523, 0);
lean::inc(x_1528);
lean::dec(x_1523);
x_1531 = lean::cnstr_get(x_1, 0);
lean::inc(x_1531);
lean::dec(x_1);
x_1534 = lean::cnstr_get(x_1531, 2);
lean::inc(x_1534);
lean::dec(x_1531);
x_1537 = l_lean_file__map_to__position(x_1534, x_1528);
x_1538 = lean::box(0);
x_1539 = lean::cnstr_get(x_1537, 1);
lean::inc(x_1539);
x_1541 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1542 = l_lean_kvmap_set__nat(x_1538, x_1541, x_1539);
x_1543 = lean::cnstr_get(x_1537, 0);
lean::inc(x_1543);
lean::dec(x_1537);
x_1546 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1547 = l_lean_kvmap_set__nat(x_1542, x_1546, x_1543);
x_1548 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1549 = lean_expr_mk_mdata(x_1547, x_1548);
x_1550 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1550, 0, x_1549);
lean::cnstr_set(x_1550, 1, x_2);
x_1551 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1551, 0, x_1550);
return x_1551;
}
}
else
{
obj* x_1554; obj* x_1555; obj* x_1556; 
lean::dec(x_1);
lean::dec(x_0);
x_1554 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1555 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1555, 0, x_1554);
lean::cnstr_set(x_1555, 1, x_2);
x_1556 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1556, 0, x_1555);
return x_1556;
}
}
else
{
lean::dec(x_1521);
if (x_21 == 0)
{
obj* x_1558; 
x_1558 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1558) == 0)
{
obj* x_1560; obj* x_1561; obj* x_1562; 
lean::dec(x_1);
x_1560 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1561 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1561, 0, x_1560);
lean::cnstr_set(x_1561, 1, x_2);
x_1562 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1562, 0, x_1561);
return x_1562;
}
else
{
obj* x_1563; obj* x_1566; obj* x_1569; obj* x_1572; obj* x_1573; obj* x_1574; obj* x_1576; obj* x_1577; obj* x_1578; obj* x_1581; obj* x_1582; obj* x_1583; obj* x_1584; obj* x_1585; obj* x_1586; 
x_1563 = lean::cnstr_get(x_1558, 0);
lean::inc(x_1563);
lean::dec(x_1558);
x_1566 = lean::cnstr_get(x_1, 0);
lean::inc(x_1566);
lean::dec(x_1);
x_1569 = lean::cnstr_get(x_1566, 2);
lean::inc(x_1569);
lean::dec(x_1566);
x_1572 = l_lean_file__map_to__position(x_1569, x_1563);
x_1573 = lean::box(0);
x_1574 = lean::cnstr_get(x_1572, 1);
lean::inc(x_1574);
x_1576 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1577 = l_lean_kvmap_set__nat(x_1573, x_1576, x_1574);
x_1578 = lean::cnstr_get(x_1572, 0);
lean::inc(x_1578);
lean::dec(x_1572);
x_1581 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1582 = l_lean_kvmap_set__nat(x_1577, x_1581, x_1578);
x_1583 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1584 = lean_expr_mk_mdata(x_1582, x_1583);
x_1585 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1585, 0, x_1584);
lean::cnstr_set(x_1585, 1, x_2);
x_1586 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1586, 0, x_1585);
return x_1586;
}
}
else
{
obj* x_1589; obj* x_1590; obj* x_1591; 
lean::dec(x_1);
lean::dec(x_0);
x_1589 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1590 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1590, 0, x_1589);
lean::cnstr_set(x_1590, 1, x_2);
x_1591 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1591, 0, x_1590);
return x_1591;
}
}
}
}
else
{
obj* x_1593; obj* x_1594; obj* x_1598; obj* x_1599; 
lean::dec(x_9);
x_1593 = l_lean_parser_term_pi_has__view;
x_1594 = lean::cnstr_get(x_1593, 0);
lean::inc(x_1594);
lean::dec(x_1593);
lean::inc(x_0);
x_1598 = lean::apply_1(x_1594, x_0);
x_1599 = lean::cnstr_get(x_1598, 1);
lean::inc(x_1599);
if (lean::obj_tag(x_1599) == 0)
{
obj* x_1603; obj* x_1606; 
lean::dec(x_1598);
lean::dec(x_1599);
x_1603 = l_lean_elaborator_to__pexpr___main___closed__45;
lean::inc(x_1);
lean::inc(x_0);
x_1606 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1603, x_1, x_2);
if (lean::obj_tag(x_1606) == 0)
{
obj* x_1610; obj* x_1612; obj* x_1613; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1610 = lean::cnstr_get(x_1606, 0);
lean::inc(x_1610);
if (lean::is_exclusive(x_1606)) {
 lean::cnstr_release(x_1606, 0);
 x_1612 = x_1606;
} else {
 lean::dec(x_1606);
 x_1612 = lean::box(0);
}
if (lean::is_scalar(x_1612)) {
 x_1613 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1613 = x_1612;
}
lean::cnstr_set(x_1613, 0, x_1610);
return x_1613;
}
else
{
obj* x_1614; 
x_1614 = lean::cnstr_get(x_1606, 0);
lean::inc(x_1614);
lean::dec(x_1606);
x_14 = x_1614;
goto lbl_15;
}
}
else
{
obj* x_1617; obj* x_1620; obj* x_1621; obj* x_1623; obj* x_1625; obj* x_1626; obj* x_1628; obj* x_1632; 
x_1617 = lean::cnstr_get(x_1599, 0);
lean::inc(x_1617);
lean::dec(x_1599);
x_1620 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1617);
x_1621 = lean::cnstr_get(x_1620, 0);
lean::inc(x_1621);
x_1623 = lean::cnstr_get(x_1620, 1);
lean::inc(x_1623);
if (lean::is_exclusive(x_1620)) {
 lean::cnstr_release(x_1620, 0);
 lean::cnstr_release(x_1620, 1);
 x_1625 = x_1620;
} else {
 lean::dec(x_1620);
 x_1625 = lean::box(0);
}
x_1626 = lean::cnstr_get(x_1623, 0);
lean::inc(x_1626);
x_1628 = lean::cnstr_get(x_1623, 1);
lean::inc(x_1628);
lean::dec(x_1623);
lean::inc(x_1);
x_1632 = l_lean_elaborator_to__pexpr___main(x_1628, x_1, x_2);
if (lean::obj_tag(x_1632) == 0)
{
obj* x_1640; obj* x_1642; obj* x_1643; 
lean::dec(x_1598);
lean::dec(x_1625);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1626);
lean::dec(x_1621);
x_1640 = lean::cnstr_get(x_1632, 0);
lean::inc(x_1640);
if (lean::is_exclusive(x_1632)) {
 lean::cnstr_release(x_1632, 0);
 x_1642 = x_1632;
} else {
 lean::dec(x_1632);
 x_1642 = lean::box(0);
}
if (lean::is_scalar(x_1642)) {
 x_1643 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1643 = x_1642;
}
lean::cnstr_set(x_1643, 0, x_1640);
return x_1643;
}
else
{
obj* x_1644; obj* x_1646; obj* x_1647; obj* x_1649; obj* x_1652; obj* x_1656; 
x_1644 = lean::cnstr_get(x_1632, 0);
lean::inc(x_1644);
if (lean::is_exclusive(x_1632)) {
 lean::cnstr_release(x_1632, 0);
 x_1646 = x_1632;
} else {
 lean::dec(x_1632);
 x_1646 = lean::box(0);
}
x_1647 = lean::cnstr_get(x_1644, 0);
lean::inc(x_1647);
x_1649 = lean::cnstr_get(x_1644, 1);
lean::inc(x_1649);
lean::dec(x_1644);
x_1652 = lean::cnstr_get(x_1598, 3);
lean::inc(x_1652);
lean::dec(x_1598);
lean::inc(x_1);
x_1656 = l_lean_elaborator_to__pexpr___main(x_1652, x_1, x_1649);
if (lean::obj_tag(x_1656) == 0)
{
obj* x_1664; obj* x_1667; 
lean::dec(x_1625);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1626);
lean::dec(x_1621);
lean::dec(x_1647);
x_1664 = lean::cnstr_get(x_1656, 0);
lean::inc(x_1664);
lean::dec(x_1656);
if (lean::is_scalar(x_1646)) {
 x_1667 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1667 = x_1646;
 lean::cnstr_set_tag(x_1646, 0);
}
lean::cnstr_set(x_1667, 0, x_1664);
return x_1667;
}
else
{
obj* x_1669; obj* x_1672; obj* x_1674; obj* x_1677; uint8 x_1678; obj* x_1680; obj* x_1681; 
lean::dec(x_1646);
x_1669 = lean::cnstr_get(x_1656, 0);
lean::inc(x_1669);
lean::dec(x_1656);
x_1672 = lean::cnstr_get(x_1669, 0);
lean::inc(x_1672);
x_1674 = lean::cnstr_get(x_1669, 1);
lean::inc(x_1674);
lean::dec(x_1669);
x_1677 = l_lean_elaborator_mangle__ident(x_1626);
x_1678 = lean::unbox(x_1621);
lean::dec(x_1621);
x_1680 = lean_expr_mk_pi(x_1677, x_1678, x_1647, x_1672);
if (lean::is_scalar(x_1625)) {
 x_1681 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1681 = x_1625;
}
lean::cnstr_set(x_1681, 0, x_1680);
lean::cnstr_set(x_1681, 1, x_1674);
x_14 = x_1681;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1683; obj* x_1684; obj* x_1688; obj* x_1689; 
lean::dec(x_9);
x_1683 = l_lean_parser_term_lambda_has__view;
x_1684 = lean::cnstr_get(x_1683, 0);
lean::inc(x_1684);
lean::dec(x_1683);
lean::inc(x_0);
x_1688 = lean::apply_1(x_1684, x_0);
x_1689 = lean::cnstr_get(x_1688, 1);
lean::inc(x_1689);
if (lean::obj_tag(x_1689) == 0)
{
obj* x_1693; obj* x_1696; 
lean::dec(x_1688);
lean::dec(x_1689);
x_1693 = l_lean_elaborator_to__pexpr___main___closed__46;
lean::inc(x_1);
lean::inc(x_0);
x_1696 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1693, x_1, x_2);
if (lean::obj_tag(x_1696) == 0)
{
obj* x_1700; obj* x_1702; obj* x_1703; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1700 = lean::cnstr_get(x_1696, 0);
lean::inc(x_1700);
if (lean::is_exclusive(x_1696)) {
 lean::cnstr_release(x_1696, 0);
 x_1702 = x_1696;
} else {
 lean::dec(x_1696);
 x_1702 = lean::box(0);
}
if (lean::is_scalar(x_1702)) {
 x_1703 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1703 = x_1702;
}
lean::cnstr_set(x_1703, 0, x_1700);
return x_1703;
}
else
{
obj* x_1704; 
x_1704 = lean::cnstr_get(x_1696, 0);
lean::inc(x_1704);
lean::dec(x_1696);
x_14 = x_1704;
goto lbl_15;
}
}
else
{
obj* x_1707; obj* x_1710; obj* x_1711; obj* x_1713; obj* x_1715; obj* x_1716; obj* x_1718; obj* x_1722; 
x_1707 = lean::cnstr_get(x_1689, 0);
lean::inc(x_1707);
lean::dec(x_1689);
x_1710 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1707);
x_1711 = lean::cnstr_get(x_1710, 0);
lean::inc(x_1711);
x_1713 = lean::cnstr_get(x_1710, 1);
lean::inc(x_1713);
if (lean::is_exclusive(x_1710)) {
 lean::cnstr_release(x_1710, 0);
 lean::cnstr_release(x_1710, 1);
 x_1715 = x_1710;
} else {
 lean::dec(x_1710);
 x_1715 = lean::box(0);
}
x_1716 = lean::cnstr_get(x_1713, 0);
lean::inc(x_1716);
x_1718 = lean::cnstr_get(x_1713, 1);
lean::inc(x_1718);
lean::dec(x_1713);
lean::inc(x_1);
x_1722 = l_lean_elaborator_to__pexpr___main(x_1718, x_1, x_2);
if (lean::obj_tag(x_1722) == 0)
{
obj* x_1730; obj* x_1732; obj* x_1733; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1711);
lean::dec(x_1688);
lean::dec(x_1716);
lean::dec(x_1715);
x_1730 = lean::cnstr_get(x_1722, 0);
lean::inc(x_1730);
if (lean::is_exclusive(x_1722)) {
 lean::cnstr_release(x_1722, 0);
 x_1732 = x_1722;
} else {
 lean::dec(x_1722);
 x_1732 = lean::box(0);
}
if (lean::is_scalar(x_1732)) {
 x_1733 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1733 = x_1732;
}
lean::cnstr_set(x_1733, 0, x_1730);
return x_1733;
}
else
{
obj* x_1734; obj* x_1736; obj* x_1737; obj* x_1739; obj* x_1742; obj* x_1746; 
x_1734 = lean::cnstr_get(x_1722, 0);
lean::inc(x_1734);
if (lean::is_exclusive(x_1722)) {
 lean::cnstr_release(x_1722, 0);
 x_1736 = x_1722;
} else {
 lean::dec(x_1722);
 x_1736 = lean::box(0);
}
x_1737 = lean::cnstr_get(x_1734, 0);
lean::inc(x_1737);
x_1739 = lean::cnstr_get(x_1734, 1);
lean::inc(x_1739);
lean::dec(x_1734);
x_1742 = lean::cnstr_get(x_1688, 3);
lean::inc(x_1742);
lean::dec(x_1688);
lean::inc(x_1);
x_1746 = l_lean_elaborator_to__pexpr___main(x_1742, x_1, x_1739);
if (lean::obj_tag(x_1746) == 0)
{
obj* x_1754; obj* x_1757; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1711);
lean::dec(x_1737);
lean::dec(x_1716);
lean::dec(x_1715);
x_1754 = lean::cnstr_get(x_1746, 0);
lean::inc(x_1754);
lean::dec(x_1746);
if (lean::is_scalar(x_1736)) {
 x_1757 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1757 = x_1736;
 lean::cnstr_set_tag(x_1736, 0);
}
lean::cnstr_set(x_1757, 0, x_1754);
return x_1757;
}
else
{
obj* x_1759; obj* x_1762; obj* x_1764; obj* x_1767; uint8 x_1768; obj* x_1770; obj* x_1771; 
lean::dec(x_1736);
x_1759 = lean::cnstr_get(x_1746, 0);
lean::inc(x_1759);
lean::dec(x_1746);
x_1762 = lean::cnstr_get(x_1759, 0);
lean::inc(x_1762);
x_1764 = lean::cnstr_get(x_1759, 1);
lean::inc(x_1764);
lean::dec(x_1759);
x_1767 = l_lean_elaborator_mangle__ident(x_1716);
x_1768 = lean::unbox(x_1711);
lean::dec(x_1711);
x_1770 = lean_expr_mk_lambda(x_1767, x_1768, x_1737, x_1762);
if (lean::is_scalar(x_1715)) {
 x_1771 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1771 = x_1715;
}
lean::cnstr_set(x_1771, 0, x_1770);
lean::cnstr_set(x_1771, 1, x_1764);
x_14 = x_1771;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1773; obj* x_1774; obj* x_1778; obj* x_1779; obj* x_1782; 
lean::dec(x_9);
x_1773 = l_lean_parser_term_app_has__view;
x_1774 = lean::cnstr_get(x_1773, 0);
lean::inc(x_1774);
lean::dec(x_1773);
lean::inc(x_0);
x_1778 = lean::apply_1(x_1774, x_0);
x_1779 = lean::cnstr_get(x_1778, 0);
lean::inc(x_1779);
lean::inc(x_1);
x_1782 = l_lean_elaborator_to__pexpr___main(x_1779, x_1, x_2);
if (lean::obj_tag(x_1782) == 0)
{
obj* x_1787; obj* x_1789; obj* x_1790; 
lean::dec(x_1778);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1787 = lean::cnstr_get(x_1782, 0);
lean::inc(x_1787);
if (lean::is_exclusive(x_1782)) {
 lean::cnstr_release(x_1782, 0);
 x_1789 = x_1782;
} else {
 lean::dec(x_1782);
 x_1789 = lean::box(0);
}
if (lean::is_scalar(x_1789)) {
 x_1790 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1790 = x_1789;
}
lean::cnstr_set(x_1790, 0, x_1787);
return x_1790;
}
else
{
obj* x_1791; obj* x_1793; obj* x_1794; obj* x_1796; obj* x_1798; obj* x_1799; obj* x_1803; 
x_1791 = lean::cnstr_get(x_1782, 0);
lean::inc(x_1791);
if (lean::is_exclusive(x_1782)) {
 lean::cnstr_release(x_1782, 0);
 x_1793 = x_1782;
} else {
 lean::dec(x_1782);
 x_1793 = lean::box(0);
}
x_1794 = lean::cnstr_get(x_1791, 0);
lean::inc(x_1794);
x_1796 = lean::cnstr_get(x_1791, 1);
lean::inc(x_1796);
if (lean::is_exclusive(x_1791)) {
 lean::cnstr_release(x_1791, 0);
 lean::cnstr_release(x_1791, 1);
 x_1798 = x_1791;
} else {
 lean::dec(x_1791);
 x_1798 = lean::box(0);
}
x_1799 = lean::cnstr_get(x_1778, 1);
lean::inc(x_1799);
lean::dec(x_1778);
lean::inc(x_1);
x_1803 = l_lean_elaborator_to__pexpr___main(x_1799, x_1, x_1796);
if (lean::obj_tag(x_1803) == 0)
{
obj* x_1809; obj* x_1812; 
lean::dec(x_1798);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1794);
x_1809 = lean::cnstr_get(x_1803, 0);
lean::inc(x_1809);
lean::dec(x_1803);
if (lean::is_scalar(x_1793)) {
 x_1812 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1812 = x_1793;
 lean::cnstr_set_tag(x_1793, 0);
}
lean::cnstr_set(x_1812, 0, x_1809);
return x_1812;
}
else
{
obj* x_1814; obj* x_1817; obj* x_1819; obj* x_1822; obj* x_1823; 
lean::dec(x_1793);
x_1814 = lean::cnstr_get(x_1803, 0);
lean::inc(x_1814);
lean::dec(x_1803);
x_1817 = lean::cnstr_get(x_1814, 0);
lean::inc(x_1817);
x_1819 = lean::cnstr_get(x_1814, 1);
lean::inc(x_1819);
lean::dec(x_1814);
x_1822 = lean_expr_mk_app(x_1794, x_1817);
if (lean::is_scalar(x_1798)) {
 x_1823 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1823 = x_1798;
}
lean::cnstr_set(x_1823, 0, x_1822);
lean::cnstr_set(x_1823, 1, x_1819);
x_14 = x_1823;
goto lbl_15;
}
}
}
}
else
{
obj* x_1825; obj* x_1826; obj* x_1830; obj* x_1831; obj* x_1833; 
lean::dec(x_9);
x_1825 = l_lean_parser_ident__univs_has__view;
x_1826 = lean::cnstr_get(x_1825, 0);
lean::inc(x_1826);
lean::dec(x_1825);
lean::inc(x_0);
x_1830 = lean::apply_1(x_1826, x_0);
x_1831 = lean::cnstr_get(x_1830, 0);
lean::inc(x_1831);
x_1833 = lean::cnstr_get(x_1830, 1);
lean::inc(x_1833);
lean::dec(x_1830);
if (lean::obj_tag(x_1833) == 0)
{
obj* x_1837; obj* x_1838; obj* x_1839; obj* x_1840; obj* x_1843; obj* x_1844; obj* x_1845; obj* x_1846; obj* x_1847; obj* x_1848; uint8 x_1849; 
lean::inc(x_1831);
x_1837 = l_lean_elaborator_mangle__ident(x_1831);
x_1838 = lean::box(0);
x_1839 = lean_expr_mk_const(x_1837, x_1838);
x_1840 = lean::cnstr_get(x_1831, 3);
lean::inc(x_1840);
lean::dec(x_1831);
x_1843 = lean::mk_nat_obj(0u);
x_1844 = l_list_enum__from___main___rarg(x_1843, x_1840);
x_1845 = l_lean_elaborator_to__pexpr___main___closed__47;
x_1846 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(x_1845, x_1844);
x_1847 = lean_expr_mk_mdata(x_1846, x_1839);
x_1848 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1849 = lean_name_dec_eq(x_7, x_1848);
lean::dec(x_7);
if (x_1849 == 0)
{
obj* x_1851; 
x_1851 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1851) == 0)
{
obj* x_1853; obj* x_1854; 
lean::dec(x_1);
x_1853 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1853, 0, x_1847);
lean::cnstr_set(x_1853, 1, x_2);
x_1854 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1854, 0, x_1853);
return x_1854;
}
else
{
obj* x_1855; obj* x_1858; obj* x_1861; obj* x_1864; obj* x_1865; obj* x_1867; obj* x_1868; obj* x_1869; obj* x_1872; obj* x_1873; obj* x_1874; obj* x_1875; obj* x_1876; 
x_1855 = lean::cnstr_get(x_1851, 0);
lean::inc(x_1855);
lean::dec(x_1851);
x_1858 = lean::cnstr_get(x_1, 0);
lean::inc(x_1858);
lean::dec(x_1);
x_1861 = lean::cnstr_get(x_1858, 2);
lean::inc(x_1861);
lean::dec(x_1858);
x_1864 = l_lean_file__map_to__position(x_1861, x_1855);
x_1865 = lean::cnstr_get(x_1864, 1);
lean::inc(x_1865);
x_1867 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1868 = l_lean_kvmap_set__nat(x_1838, x_1867, x_1865);
x_1869 = lean::cnstr_get(x_1864, 0);
lean::inc(x_1869);
lean::dec(x_1864);
x_1872 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1873 = l_lean_kvmap_set__nat(x_1868, x_1872, x_1869);
x_1874 = lean_expr_mk_mdata(x_1873, x_1847);
x_1875 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1875, 0, x_1874);
lean::cnstr_set(x_1875, 1, x_2);
x_1876 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1876, 0, x_1875);
return x_1876;
}
}
else
{
obj* x_1879; obj* x_1880; 
lean::dec(x_1);
lean::dec(x_0);
x_1879 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1879, 0, x_1847);
lean::cnstr_set(x_1879, 1, x_2);
x_1880 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1880, 0, x_1879);
return x_1880;
}
}
else
{
obj* x_1881; obj* x_1884; obj* x_1888; 
x_1881 = lean::cnstr_get(x_1833, 0);
lean::inc(x_1881);
lean::dec(x_1833);
x_1884 = lean::cnstr_get(x_1881, 1);
lean::inc(x_1884);
lean::dec(x_1881);
lean::inc(x_1);
x_1888 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_1884, x_1, x_2);
if (lean::obj_tag(x_1888) == 0)
{
obj* x_1893; obj* x_1895; obj* x_1896; 
lean::dec(x_1831);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1893 = lean::cnstr_get(x_1888, 0);
lean::inc(x_1893);
if (lean::is_exclusive(x_1888)) {
 lean::cnstr_release(x_1888, 0);
 x_1895 = x_1888;
} else {
 lean::dec(x_1888);
 x_1895 = lean::box(0);
}
if (lean::is_scalar(x_1895)) {
 x_1896 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1896 = x_1895;
}
lean::cnstr_set(x_1896, 0, x_1893);
return x_1896;
}
else
{
obj* x_1897; obj* x_1900; obj* x_1902; obj* x_1904; obj* x_1906; obj* x_1907; obj* x_1908; obj* x_1911; obj* x_1912; obj* x_1913; obj* x_1914; obj* x_1915; obj* x_1916; 
x_1897 = lean::cnstr_get(x_1888, 0);
lean::inc(x_1897);
lean::dec(x_1888);
x_1900 = lean::cnstr_get(x_1897, 0);
lean::inc(x_1900);
x_1902 = lean::cnstr_get(x_1897, 1);
lean::inc(x_1902);
if (lean::is_exclusive(x_1897)) {
 lean::cnstr_release(x_1897, 0);
 lean::cnstr_release(x_1897, 1);
 x_1904 = x_1897;
} else {
 lean::dec(x_1897);
 x_1904 = lean::box(0);
}
lean::inc(x_1831);
x_1906 = l_lean_elaborator_mangle__ident(x_1831);
x_1907 = lean_expr_mk_const(x_1906, x_1900);
x_1908 = lean::cnstr_get(x_1831, 3);
lean::inc(x_1908);
lean::dec(x_1831);
x_1911 = lean::mk_nat_obj(0u);
x_1912 = l_list_enum__from___main___rarg(x_1911, x_1908);
x_1913 = l_lean_elaborator_to__pexpr___main___closed__47;
x_1914 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(x_1913, x_1912);
x_1915 = lean_expr_mk_mdata(x_1914, x_1907);
if (lean::is_scalar(x_1904)) {
 x_1916 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1916 = x_1904;
}
lean::cnstr_set(x_1916, 0, x_1915);
lean::cnstr_set(x_1916, 1, x_1902);
x_14 = x_1916;
goto lbl_15;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_1920; obj* x_1922; obj* x_1923; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1920 = lean::cnstr_get(x_12, 0);
lean::inc(x_1920);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_1922 = x_12;
} else {
 lean::dec(x_12);
 x_1922 = lean::box(0);
}
if (lean::is_scalar(x_1922)) {
 x_1923 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1923 = x_1922;
}
lean::cnstr_set(x_1923, 0, x_1920);
return x_1923;
}
else
{
obj* x_1924; obj* x_1926; obj* x_1927; obj* x_1929; obj* x_1931; obj* x_1932; uint8 x_1933; 
x_1924 = lean::cnstr_get(x_12, 0);
lean::inc(x_1924);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_1926 = x_12;
} else {
 lean::dec(x_12);
 x_1926 = lean::box(0);
}
x_1927 = lean::cnstr_get(x_1924, 0);
lean::inc(x_1927);
x_1929 = lean::cnstr_get(x_1924, 1);
lean::inc(x_1929);
if (lean::is_exclusive(x_1924)) {
 lean::cnstr_release(x_1924, 0);
 lean::cnstr_release(x_1924, 1);
 x_1931 = x_1924;
} else {
 lean::dec(x_1924);
 x_1931 = lean::box(0);
}
x_1932 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1933 = lean_name_dec_eq(x_7, x_1932);
lean::dec(x_7);
if (x_1933 == 0)
{
obj* x_1935; 
x_1935 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1935) == 0)
{
obj* x_1937; obj* x_1938; 
lean::dec(x_1);
if (lean::is_scalar(x_1931)) {
 x_1937 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1937 = x_1931;
}
lean::cnstr_set(x_1937, 0, x_1927);
lean::cnstr_set(x_1937, 1, x_1929);
if (lean::is_scalar(x_1926)) {
 x_1938 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1938 = x_1926;
}
lean::cnstr_set(x_1938, 0, x_1937);
return x_1938;
}
else
{
obj* x_1939; obj* x_1942; obj* x_1945; obj* x_1948; obj* x_1949; obj* x_1950; obj* x_1952; obj* x_1953; obj* x_1954; obj* x_1957; obj* x_1958; obj* x_1959; obj* x_1960; obj* x_1961; 
x_1939 = lean::cnstr_get(x_1935, 0);
lean::inc(x_1939);
lean::dec(x_1935);
x_1942 = lean::cnstr_get(x_1, 0);
lean::inc(x_1942);
lean::dec(x_1);
x_1945 = lean::cnstr_get(x_1942, 2);
lean::inc(x_1945);
lean::dec(x_1942);
x_1948 = l_lean_file__map_to__position(x_1945, x_1939);
x_1949 = lean::box(0);
x_1950 = lean::cnstr_get(x_1948, 1);
lean::inc(x_1950);
x_1952 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1953 = l_lean_kvmap_set__nat(x_1949, x_1952, x_1950);
x_1954 = lean::cnstr_get(x_1948, 0);
lean::inc(x_1954);
lean::dec(x_1948);
x_1957 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1958 = l_lean_kvmap_set__nat(x_1953, x_1957, x_1954);
x_1959 = lean_expr_mk_mdata(x_1958, x_1927);
if (lean::is_scalar(x_1931)) {
 x_1960 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1960 = x_1931;
}
lean::cnstr_set(x_1960, 0, x_1959);
lean::cnstr_set(x_1960, 1, x_1929);
if (lean::is_scalar(x_1926)) {
 x_1961 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1961 = x_1926;
}
lean::cnstr_set(x_1961, 0, x_1960);
return x_1961;
}
}
else
{
obj* x_1964; obj* x_1965; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_1931)) {
 x_1964 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1964 = x_1931;
}
lean::cnstr_set(x_1964, 0, x_1927);
lean::cnstr_set(x_1964, 1, x_1929);
if (lean::is_scalar(x_1926)) {
 x_1965 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1965 = x_1926;
}
lean::cnstr_set(x_1965, 0, x_1964);
return x_1965;
}
}
}
lbl_15:
{
obj* x_1966; obj* x_1968; obj* x_1970; obj* x_1971; uint8 x_1972; 
x_1966 = lean::cnstr_get(x_14, 0);
lean::inc(x_1966);
x_1968 = lean::cnstr_get(x_14, 1);
lean::inc(x_1968);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_1970 = x_14;
} else {
 lean::dec(x_14);
 x_1970 = lean::box(0);
}
x_1971 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1972 = lean_name_dec_eq(x_7, x_1971);
lean::dec(x_7);
if (x_1972 == 0)
{
obj* x_1974; 
x_1974 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1974) == 0)
{
obj* x_1976; obj* x_1977; 
lean::dec(x_1);
if (lean::is_scalar(x_1970)) {
 x_1976 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1976 = x_1970;
}
lean::cnstr_set(x_1976, 0, x_1966);
lean::cnstr_set(x_1976, 1, x_1968);
x_1977 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1977, 0, x_1976);
return x_1977;
}
else
{
obj* x_1978; obj* x_1981; obj* x_1984; obj* x_1987; obj* x_1988; obj* x_1989; obj* x_1991; obj* x_1992; obj* x_1993; obj* x_1996; obj* x_1997; obj* x_1998; obj* x_1999; obj* x_2000; 
x_1978 = lean::cnstr_get(x_1974, 0);
lean::inc(x_1978);
lean::dec(x_1974);
x_1981 = lean::cnstr_get(x_1, 0);
lean::inc(x_1981);
lean::dec(x_1);
x_1984 = lean::cnstr_get(x_1981, 2);
lean::inc(x_1984);
lean::dec(x_1981);
x_1987 = l_lean_file__map_to__position(x_1984, x_1978);
x_1988 = lean::box(0);
x_1989 = lean::cnstr_get(x_1987, 1);
lean::inc(x_1989);
x_1991 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1992 = l_lean_kvmap_set__nat(x_1988, x_1991, x_1989);
x_1993 = lean::cnstr_get(x_1987, 0);
lean::inc(x_1993);
lean::dec(x_1987);
x_1996 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1997 = l_lean_kvmap_set__nat(x_1992, x_1996, x_1993);
x_1998 = lean_expr_mk_mdata(x_1997, x_1966);
if (lean::is_scalar(x_1970)) {
 x_1999 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1999 = x_1970;
}
lean::cnstr_set(x_1999, 0, x_1998);
lean::cnstr_set(x_1999, 1, x_1968);
x_2000 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2000, 0, x_1999);
return x_2000;
}
}
else
{
obj* x_2003; obj* x_2004; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_1970)) {
 x_2003 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2003 = x_1970;
}
lean::cnstr_set(x_2003, 0, x_1966);
lean::cnstr_set(x_2003, 1, x_1968);
x_2004 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2004, 0, x_2003);
return x_2004;
}
}
lbl_17:
{
obj* x_2005; obj* x_2007; obj* x_2009; 
x_2005 = lean::cnstr_get(x_16, 0);
lean::inc(x_2005);
x_2007 = lean::cnstr_get(x_16, 1);
lean::inc(x_2007);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_2009 = x_16;
} else {
 lean::dec(x_16);
 x_2009 = lean::box(0);
}
if (lean::obj_tag(x_2005) == 0)
{
obj* x_2012; obj* x_2015; 
lean::dec(x_9);
lean::dec(x_2009);
x_2012 = l_lean_elaborator_to__pexpr___main___closed__5;
lean::inc(x_1);
lean::inc(x_0);
x_2015 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2012, x_1, x_2007);
if (lean::obj_tag(x_2015) == 0)
{
obj* x_2019; obj* x_2021; obj* x_2022; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_2019 = lean::cnstr_get(x_2015, 0);
lean::inc(x_2019);
if (lean::is_exclusive(x_2015)) {
 lean::cnstr_release(x_2015, 0);
 x_2021 = x_2015;
} else {
 lean::dec(x_2015);
 x_2021 = lean::box(0);
}
if (lean::is_scalar(x_2021)) {
 x_2022 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2022 = x_2021;
}
lean::cnstr_set(x_2022, 0, x_2019);
return x_2022;
}
else
{
obj* x_2023; 
x_2023 = lean::cnstr_get(x_2015, 0);
lean::inc(x_2023);
lean::dec(x_2015);
x_14 = x_2023;
goto lbl_15;
}
}
else
{
obj* x_2026; obj* x_2028; obj* x_2031; obj* x_2032; obj* x_2033; obj* x_2034; obj* x_2035; obj* x_2036; obj* x_2037; obj* x_2038; obj* x_2039; 
x_2026 = lean::cnstr_get(x_2005, 0);
lean::inc(x_2026);
x_2028 = lean::cnstr_get(x_2005, 1);
lean::inc(x_2028);
lean::dec(x_2005);
x_2031 = lean::box(0);
x_2032 = lean::mk_nat_obj(0u);
x_2033 = l_list_length__aux___main___rarg(x_9, x_2032);
x_2034 = l_lean_elaborator_to__pexpr___main___closed__6;
x_2035 = l_lean_kvmap_set__nat(x_2031, x_2034, x_2033);
x_2036 = l_list_reverse___rarg(x_2028);
x_2037 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_2026, x_2036);
x_2038 = lean_expr_mk_mdata(x_2035, x_2037);
if (lean::is_scalar(x_2009)) {
 x_2039 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2039 = x_2009;
}
lean::cnstr_set(x_2039, 0, x_2038);
lean::cnstr_set(x_2039, 1, x_2007);
x_14 = x_2039;
goto lbl_15;
}
}
}
default:
{
obj* x_2040; 
x_2040 = lean::box(0);
x_3 = x_2040;
goto lbl_4;
}
}
lbl_4:
{
obj* x_2043; obj* x_2044; obj* x_2045; obj* x_2046; obj* x_2047; obj* x_2049; 
lean::dec(x_3);
lean::inc(x_0);
x_2043 = l_lean_parser_syntax_to__format___main(x_0);
x_2044 = lean::mk_nat_obj(80u);
x_2045 = l_lean_format_pretty(x_2043, x_2044);
x_2046 = l_lean_elaborator_to__pexpr___main___closed__1;
x_2047 = lean::string_append(x_2046, x_2045);
lean::dec(x_2045);
x_2049 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2047, x_1, x_2);
return x_2049;
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
lean::inc(x_36);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_38 = x_8;
} else {
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
lean::inc(x_40);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_42 = x_8;
} else {
 lean::dec(x_8);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 lean::cnstr_release(x_40, 1);
 x_47 = x_40;
} else {
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
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
obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
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
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_75 = x_68;
} else {
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
lean::inc(x_87);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 x_89 = x_85;
} else {
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
lean::inc(x_91);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 x_93 = x_85;
} else {
 lean::dec(x_85);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_91, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_91, 1);
lean::inc(x_96);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 x_98 = x_91;
} else {
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
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
lean::inc(x_42);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_44 = x_33;
} else {
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
lean::inc(x_46);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_48 = x_33;
} else {
 lean::dec(x_33);
 x_48 = lean::box(0);
}
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
lean::inc(x_72);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_74 = x_62;
} else {
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
lean::inc(x_92);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_94 = x_62;
} else {
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
lean::inc(x_164);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 x_166 = x_153;
} else {
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
lean::inc(x_182);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 x_184 = x_153;
} else {
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
lean::inc(x_227);
if (lean::is_exclusive(x_218)) {
 lean::cnstr_release(x_218, 0);
 x_229 = x_218;
} else {
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
lean::inc(x_253);
if (lean::is_exclusive(x_242)) {
 lean::cnstr_release(x_242, 0);
 x_255 = x_242;
} else {
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
lean::inc(x_34);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_36 = x_29;
} else {
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
lean::inc(x_53);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 x_55 = x_48;
} else {
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
lean::inc(x_73);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 x_75 = x_67;
} else {
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
lean::inc(x_104);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 x_106 = x_99;
} else {
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
lean::inc(x_111);
x_113 = lean::cnstr_get(x_14, 1);
lean::inc(x_113);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_115 = x_14;
} else {
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
lean::inc(x_120);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_release(x_116, 0);
 x_122 = x_116;
} else {
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
lean::inc(x_124);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_release(x_116, 0);
 x_126 = x_116;
} else {
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
lean::inc(x_31);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 x_33 = x_26;
} else {
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
lean::inc(x_75);
x_77 = lean::cnstr_get(x_14, 1);
lean::inc(x_77);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_79 = x_14;
} else {
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
lean::inc(x_100);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_102 = x_92;
} else {
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
lean::inc(x_104);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_106 = x_92;
} else {
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
obj* x_122; obj* x_125; obj* x_127; obj* x_130; obj* x_131; uint8 x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
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
lean::dec(x_80);
x_134 = lean_expr_local(x_130, x_130, x_131, x_132);
x_135 = lean::cnstr_get(x_82, 0);
lean::inc(x_135);
x_137 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(x_135);
x_138 = l_lean_elaborator_names__to__pexpr(x_137);
x_139 = lean::cnstr_get(x_82, 1);
lean::inc(x_139);
lean::dec(x_82);
x_142 = l_lean_elaborator_infer__mod__to__pexpr(x_139);
x_143 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_144 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_144 = x_13;
}
lean::cnstr_set(x_144, 0, x_107);
lean::cnstr_set(x_144, 1, x_143);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_142);
lean::cnstr_set(x_145, 1, x_144);
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_138);
lean::cnstr_set(x_146, 1, x_145);
x_147 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_147, 0, x_134);
lean::cnstr_set(x_147, 1, x_146);
x_148 = l_lean_expr_mk__capp(x_130, x_147);
x_149 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_125);
if (lean::is_scalar(x_79)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_79;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_127);
if (lean::is_scalar(x_106)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_106;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
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
lean::inc(x_114);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 x_116 = x_109;
} else {
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
lean::inc(x_118);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 x_120 = x_109;
} else {
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
lean::inc(x_208);
if (lean::is_exclusive(x_199)) {
 lean::cnstr_release(x_199, 0);
 x_210 = x_199;
} else {
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
lean::inc(x_212);
if (lean::is_exclusive(x_199)) {
 lean::cnstr_release(x_199, 0);
 x_214 = x_199;
} else {
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
lean::inc(x_246);
if (lean::is_exclusive(x_233)) {
 lean::cnstr_release(x_233, 0);
 x_248 = x_233;
} else {
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
lean::inc(x_530);
if (lean::is_exclusive(x_520)) {
 lean::cnstr_release(x_520, 0);
 x_532 = x_520;
} else {
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
lean::inc(x_534);
if (lean::is_exclusive(x_520)) {
 lean::cnstr_release(x_520, 0);
 x_536 = x_520;
} else {
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
lean::inc(x_558);
if (lean::is_exclusive(x_548)) {
 lean::cnstr_release(x_548, 0);
 x_560 = x_548;
} else {
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
lean::inc(x_578);
if (lean::is_exclusive(x_548)) {
 lean::cnstr_release(x_548, 0);
 x_580 = x_548;
} else {
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
lean::inc(x_650);
if (lean::is_exclusive(x_639)) {
 lean::cnstr_release(x_639, 0);
 x_652 = x_639;
} else {
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
lean::inc(x_668);
if (lean::is_exclusive(x_639)) {
 lean::cnstr_release(x_639, 0);
 x_670 = x_639;
} else {
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
lean::inc(x_852);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_854 = x_5;
} else {
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
lean::inc(x_856);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_858 = x_5;
} else {
 lean::dec(x_5);
 x_858 = lean::box(0);
}
x_859 = lean::cnstr_get(x_856, 1);
lean::inc(x_859);
if (lean::is_exclusive(x_856)) {
 lean::cnstr_release(x_856, 0);
 lean::cnstr_release(x_856, 1);
 x_861 = x_856;
} else {
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
lean::inc(x_37);
x_39 = lean::cnstr_get(x_11, 1);
lean::inc(x_39);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_41 = x_11;
} else {
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
lean::inc(x_47);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_49 = x_42;
} else {
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
lean::inc(x_51);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_53 = x_42;
} else {
 lean::dec(x_42);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
x_59 = lean::unbox(x_37);
lean::dec(x_37);
if (x_59 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_6);
lean::dec(x_10);
if (lean::is_scalar(x_41)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_41;
}
lean::cnstr_set(x_63, 0, x_54);
lean::cnstr_set(x_63, 1, x_56);
if (lean::is_scalar(x_53)) {
 x_64 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_64 = x_53;
}
lean::cnstr_set(x_64, 0, x_63);
return x_64;
}
else
{
obj* x_65; obj* x_66; obj* x_67; 
if (lean::is_scalar(x_10)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_10;
}
lean::cnstr_set(x_65, 0, x_6);
lean::cnstr_set(x_65, 1, x_54);
if (lean::is_scalar(x_41)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_41;
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
}
lbl_26:
{
obj* x_69; obj* x_70; obj* x_72; obj* x_76; 
lean::dec(x_25);
x_69 = l_lean_elaborator_mangle__ident(x_20);
x_70 = lean::cnstr_get(x_2, 4);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_70, 2);
lean::inc(x_72);
lean::inc(x_69);
lean::inc(x_72);
x_76 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_72, x_69);
if (lean::obj_tag(x_76) == 0)
{
obj* x_80; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_89; 
lean::dec(x_15);
lean::dec(x_72);
lean::dec(x_70);
x_80 = lean::box(0);
x_81 = l_lean_name_to__string___closed__1;
lean::inc(x_69);
x_83 = l_lean_name_to__string__with__sep___main(x_81, x_69);
x_84 = l_lean_parser_substring_of__string(x_83);
x_85 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_85, 0, x_80);
lean::cnstr_set(x_85, 1, x_84);
lean::cnstr_set(x_85, 2, x_69);
lean::cnstr_set(x_85, 3, x_80);
lean::cnstr_set(x_85, 4, x_80);
x_86 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_86, 0, x_85);
x_87 = l_string_join___closed__1;
lean::inc(x_1);
x_89 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_86, x_87, x_1, x_2);
if (lean::obj_tag(x_89) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_19);
x_95 = lean::cnstr_get(x_89, 0);
lean::inc(x_95);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 x_97 = x_89;
} else {
 lean::dec(x_89);
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
obj* x_99; obj* x_102; uint8 x_105; obj* x_106; obj* x_107; 
x_99 = lean::cnstr_get(x_89, 0);
lean::inc(x_99);
lean::dec(x_89);
x_102 = lean::cnstr_get(x_99, 1);
lean::inc(x_102);
lean::dec(x_99);
x_105 = 0;
x_106 = lean::box(x_105);
if (lean::is_scalar(x_19)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_19;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_102);
x_11 = x_107;
goto lbl_12;
}
}
else
{
obj* x_108; obj* x_111; obj* x_114; obj* x_116; obj* x_118; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_131; uint8 x_132; obj* x_134; obj* x_135; obj* x_136; obj* x_138; obj* x_140; obj* x_142; obj* x_145; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_159; uint8 x_160; obj* x_161; obj* x_162; 
x_108 = lean::cnstr_get(x_76, 0);
lean::inc(x_108);
lean::dec(x_76);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
lean::dec(x_108);
x_114 = lean::cnstr_get(x_2, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_2, 1);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_2, 2);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_2, 3);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_70, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_70, 1);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_111, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_111, 1);
lean::inc(x_128);
lean::dec(x_111);
x_131 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_131, 0, x_126);
lean::cnstr_set(x_131, 1, x_128);
x_132 = lean::unbox(x_15);
lean::dec(x_15);
lean::cnstr_set_scalar(x_131, sizeof(void*)*2, x_132);
x_134 = x_131;
x_135 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(x_72, x_69, x_134);
x_136 = lean::cnstr_get(x_70, 3);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_70, 4);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_70, 5);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_70, 6);
lean::inc(x_142);
lean::dec(x_70);
x_145 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_145, 0, x_122);
lean::cnstr_set(x_145, 1, x_124);
lean::cnstr_set(x_145, 2, x_135);
lean::cnstr_set(x_145, 3, x_136);
lean::cnstr_set(x_145, 4, x_138);
lean::cnstr_set(x_145, 5, x_140);
lean::cnstr_set(x_145, 6, x_142);
x_146 = lean::cnstr_get(x_2, 5);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_2, 6);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_2, 7);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_2, 8);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_2, 9);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_2, 10);
lean::inc(x_156);
lean::dec(x_2);
x_159 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_159, 0, x_114);
lean::cnstr_set(x_159, 1, x_116);
lean::cnstr_set(x_159, 2, x_118);
lean::cnstr_set(x_159, 3, x_120);
lean::cnstr_set(x_159, 4, x_145);
lean::cnstr_set(x_159, 5, x_146);
lean::cnstr_set(x_159, 6, x_148);
lean::cnstr_set(x_159, 7, x_150);
lean::cnstr_set(x_159, 8, x_152);
lean::cnstr_set(x_159, 9, x_154);
lean::cnstr_set(x_159, 10, x_156);
x_160 = 0;
x_161 = lean::box(x_160);
if (lean::is_scalar(x_19)) {
 x_162 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_162 = x_19;
}
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_159);
x_11 = x_162;
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
lean::inc(x_58);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_60 = x_55;
} else {
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
lean::inc(x_62);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_64 = x_55;
} else {
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
lean::inc(x_31);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_33 = x_7;
} else {
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
lean::inc(x_35);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_37 = x_7;
} else {
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
lean::inc(x_56);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 x_58 = x_52;
} else {
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
lean::inc(x_100);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_102 = x_50;
} else {
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
lean::inc(x_104);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_106 = x_50;
} else {
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
lean::inc(x_44);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_46 = x_16;
} else {
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
lean::inc(x_27);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_29 = x_16;
} else {
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
lean::inc(x_94);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 x_96 = x_85;
} else {
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
lean::inc(x_157);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 x_159 = x_94;
} else {
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
lean::inc(x_169);
if (lean::is_exclusive(x_162)) {
 lean::cnstr_release(x_162, 0);
 x_171 = x_162;
} else {
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
lean::inc(x_247);
if (lean::is_exclusive(x_160)) {
 lean::cnstr_release(x_160, 0);
 x_249 = x_160;
} else {
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
lean::inc(x_260);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_262 = x_7;
} else {
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
lean::inc(x_33);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_35 = x_30;
} else {
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
lean::inc(x_62);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_64 = x_60;
} else {
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
lean::inc(x_66);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_68 = x_60;
} else {
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
lean::inc(x_31);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 x_33 = x_27;
} else {
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
lean::inc(x_35);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 x_37 = x_27;
} else {
 lean::dec(x_27);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 lean::cnstr_release(x_35, 1);
 x_42 = x_35;
} else {
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
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
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
lean::inc(x_97);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 x_99 = x_93;
} else {
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
lean::inc(x_101);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 x_103 = x_93;
} else {
 lean::dec(x_93);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get(x_101, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_108 = x_101;
} else {
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
lean::inc(x_16);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_18 = x_12;
} else {
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
lean::inc(x_20);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_22 = x_12;
} else {
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
lean::inc(x_16);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_18 = x_13;
} else {
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
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
lean::inc(x_50);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_52 = x_14;
} else {
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
lean::inc(x_63);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_65 = x_60;
} else {
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
