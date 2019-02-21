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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
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
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_55; obj* x_57; obj* x_60; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_47 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_49 = x_41;
} else {
 lean::inc(x_47);
 lean::dec(x_41);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
lean::dec(x_47);
x_55 = lean::cnstr_get(x_50, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_50, 1);
lean::inc(x_57);
lean::dec(x_50);
x_60 = lean::cnstr_get(x_36, 1);
lean::inc(x_60);
lean::dec(x_36);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_57);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_55);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_21; obj* x_24; obj* x_26; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_11);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_34 = x_29;
} else {
 lean::inc(x_32);
 lean::dec(x_29);
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
lean::dec(x_36);
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
x_45 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_21; obj* x_24; obj* x_26; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_11);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_34 = x_29;
} else {
 lean::inc(x_32);
 lean::dec(x_29);
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
lean::dec(x_36);
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
x_45 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_22; obj* x_26; 
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
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_15, 1);
lean::inc(x_22);
lean::dec(x_15);
lean::inc(x_20);
x_26 = l_lean_parser_syntax_kind___main(x_20);
if (lean::obj_tag(x_26) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_37; 
lean::dec(x_14);
lean::dec(x_20);
lean::dec(x_22);
lean::inc(x_0);
x_31 = l_lean_parser_syntax_to__format___main(x_0);
x_32 = lean::mk_nat_obj(80u);
x_33 = l_lean_format_pretty(x_31, x_32);
x_34 = l_lean_elaborator_to__level___main___closed__1;
x_35 = lean::string_append(x_34, x_33);
lean::dec(x_33);
x_37 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_35, x_1, x_17);
return x_37;
}
else
{
obj* x_38; obj* x_41; uint8 x_42; 
x_38 = lean::cnstr_get(x_26, 0);
lean::inc(x_38);
lean::dec(x_26);
x_41 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_42 = lean_name_dec_eq(x_38, x_41);
if (x_42 == 0)
{
obj* x_44; uint8 x_45; 
lean::dec(x_14);
x_44 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_45 = lean_name_dec_eq(x_38, x_44);
lean::dec(x_38);
if (x_45 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_56; 
lean::dec(x_20);
lean::dec(x_22);
lean::inc(x_0);
x_50 = l_lean_parser_syntax_to__format___main(x_0);
x_51 = lean::mk_nat_obj(80u);
x_52 = l_lean_format_pretty(x_50, x_51);
x_53 = l_lean_elaborator_to__level___main___closed__1;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_56 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_54, x_1, x_17);
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_61; 
x_57 = l_lean_parser_level_trailing_has__view;
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
lean::dec(x_57);
x_61 = lean::apply_1(x_58, x_20);
if (lean::obj_tag(x_61) == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_22);
lean::dec(x_61);
x_64 = l_lean_elaborator_to__level___main___closed__2;
x_65 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_64, x_1, x_17);
return x_65;
}
else
{
if (lean::obj_tag(x_22) == 0)
{
obj* x_67; obj* x_70; obj* x_72; 
lean::dec(x_0);
x_67 = lean::cnstr_get(x_61, 0);
lean::inc(x_67);
lean::dec(x_61);
x_70 = lean::cnstr_get(x_67, 0);
lean::inc(x_70);
x_72 = l_lean_elaborator_to__level___main(x_70, x_1, x_17);
if (lean::obj_tag(x_72) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_67);
x_74 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_76 = x_72;
} else {
 lean::inc(x_74);
 lean::dec(x_72);
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
obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_86; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_78 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_80 = x_72;
} else {
 lean::inc(x_78);
 lean::dec(x_72);
 x_80 = lean::box(0);
}
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 1);
lean::inc(x_83);
lean::dec(x_78);
x_86 = lean::cnstr_get(x_67, 2);
lean::inc(x_86);
lean::dec(x_67);
x_89 = l_lean_parser_number_view_to__nat___main(x_86);
x_90 = l_lean_elaborator_level__add___main(x_81, x_89);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_83);
if (lean::is_scalar(x_80)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_80;
}
lean::cnstr_set(x_92, 0, x_91);
return x_92;
}
}
else
{
obj* x_95; obj* x_96; 
lean::dec(x_22);
lean::dec(x_61);
x_95 = l_lean_elaborator_to__level___main___closed__2;
x_96 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_95, x_1, x_17);
return x_96;
}
}
}
}
else
{
obj* x_98; obj* x_99; obj* x_102; 
lean::dec(x_38);
x_98 = l_lean_parser_level_leading_has__view;
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
lean::dec(x_98);
x_102 = lean::apply_1(x_99, x_20);
switch (lean::obj_tag(x_102)) {
case 0:
{
lean::dec(x_14);
lean::dec(x_102);
if (lean::obj_tag(x_22) == 0)
{
obj* x_105; obj* x_106; 
x_105 = l_lean_elaborator_to__level___main___closed__2;
x_106 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_105, x_1, x_17);
return x_106;
}
else
{
obj* x_108; obj* x_110; obj* x_114; 
lean::dec(x_0);
x_108 = lean::cnstr_get(x_22, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_22, 1);
lean::inc(x_110);
lean::dec(x_22);
lean::inc(x_1);
x_114 = l_lean_elaborator_to__level___main(x_108, x_1, x_17);
if (lean::obj_tag(x_114) == 0)
{
obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_1);
lean::dec(x_110);
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
obj* x_121; obj* x_124; obj* x_126; obj* x_129; 
x_121 = lean::cnstr_get(x_114, 0);
lean::inc(x_121);
lean::dec(x_114);
x_124 = lean::cnstr_get(x_121, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_121, 1);
lean::inc(x_126);
lean::dec(x_121);
x_129 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_110, x_1, x_126);
if (lean::obj_tag(x_129) == 0)
{
obj* x_131; obj* x_133; obj* x_134; 
lean::dec(x_124);
x_131 = lean::cnstr_get(x_129, 0);
if (lean::is_exclusive(x_129)) {
 x_133 = x_129;
} else {
 lean::inc(x_131);
 lean::dec(x_129);
 x_133 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_133;
}
lean::cnstr_set(x_134, 0, x_131);
return x_134;
}
else
{
obj* x_135; obj* x_137; obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_145; 
x_135 = lean::cnstr_get(x_129, 0);
if (lean::is_exclusive(x_129)) {
 x_137 = x_129;
} else {
 lean::inc(x_135);
 lean::dec(x_129);
 x_137 = lean::box(0);
}
x_138 = lean::cnstr_get(x_135, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_135, 1);
lean::inc(x_140);
lean::dec(x_135);
x_143 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(x_124, x_138);
x_144 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_140);
if (lean::is_scalar(x_137)) {
 x_145 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_145 = x_137;
}
lean::cnstr_set(x_145, 0, x_144);
return x_145;
}
}
}
}
case 1:
{
lean::dec(x_14);
lean::dec(x_102);
if (lean::obj_tag(x_22) == 0)
{
obj* x_148; obj* x_149; 
x_148 = l_lean_elaborator_to__level___main___closed__2;
x_149 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_148, x_1, x_17);
return x_149;
}
else
{
obj* x_151; obj* x_153; obj* x_157; 
lean::dec(x_0);
x_151 = lean::cnstr_get(x_22, 0);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_22, 1);
lean::inc(x_153);
lean::dec(x_22);
lean::inc(x_1);
x_157 = l_lean_elaborator_to__level___main(x_151, x_1, x_17);
if (lean::obj_tag(x_157) == 0)
{
obj* x_160; obj* x_162; obj* x_163; 
lean::dec(x_153);
lean::dec(x_1);
x_160 = lean::cnstr_get(x_157, 0);
if (lean::is_exclusive(x_157)) {
 x_162 = x_157;
} else {
 lean::inc(x_160);
 lean::dec(x_157);
 x_162 = lean::box(0);
}
if (lean::is_scalar(x_162)) {
 x_163 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_163 = x_162;
}
lean::cnstr_set(x_163, 0, x_160);
return x_163;
}
else
{
obj* x_164; obj* x_167; obj* x_169; obj* x_172; 
x_164 = lean::cnstr_get(x_157, 0);
lean::inc(x_164);
lean::dec(x_157);
x_167 = lean::cnstr_get(x_164, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_164, 1);
lean::inc(x_169);
lean::dec(x_164);
x_172 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_153, x_1, x_169);
if (lean::obj_tag(x_172) == 0)
{
obj* x_174; obj* x_176; obj* x_177; 
lean::dec(x_167);
x_174 = lean::cnstr_get(x_172, 0);
if (lean::is_exclusive(x_172)) {
 x_176 = x_172;
} else {
 lean::inc(x_174);
 lean::dec(x_172);
 x_176 = lean::box(0);
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_174);
return x_177;
}
else
{
obj* x_178; obj* x_180; obj* x_181; obj* x_183; obj* x_186; obj* x_187; obj* x_188; 
x_178 = lean::cnstr_get(x_172, 0);
if (lean::is_exclusive(x_172)) {
 x_180 = x_172;
} else {
 lean::inc(x_178);
 lean::dec(x_172);
 x_180 = lean::box(0);
}
x_181 = lean::cnstr_get(x_178, 0);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_178, 1);
lean::inc(x_183);
lean::dec(x_178);
x_186 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(x_167, x_181);
x_187 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_187, 0, x_186);
lean::cnstr_set(x_187, 1, x_183);
if (lean::is_scalar(x_180)) {
 x_188 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_188 = x_180;
}
lean::cnstr_set(x_188, 0, x_187);
return x_188;
}
}
}
}
case 2:
{
lean::dec(x_102);
if (lean::obj_tag(x_22) == 0)
{
obj* x_192; obj* x_193; obj* x_194; 
lean::dec(x_1);
lean::dec(x_0);
x_192 = l_lean_elaborator_to__level___main___closed__3;
x_193 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_193, 0, x_192);
lean::cnstr_set(x_193, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_194 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_194 = x_14;
}
lean::cnstr_set(x_194, 0, x_193);
return x_194;
}
else
{
obj* x_197; obj* x_198; 
lean::dec(x_14);
lean::dec(x_22);
x_197 = l_lean_elaborator_to__level___main___closed__2;
x_198 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_197, x_1, x_17);
return x_198;
}
}
case 3:
{
obj* x_202; obj* x_203; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_102);
x_202 = l_lean_elaborator_to__level___main___closed__2;
x_203 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_202, x_1, x_17);
return x_203;
}
case 4:
{
if (lean::obj_tag(x_22) == 0)
{
obj* x_206; obj* x_209; obj* x_210; obj* x_211; obj* x_212; 
lean::dec(x_1);
lean::dec(x_0);
x_206 = lean::cnstr_get(x_102, 0);
lean::inc(x_206);
lean::dec(x_102);
x_209 = l_lean_parser_number_view_to__nat___main(x_206);
x_210 = l_lean_level_of__nat___main(x_209);
x_211 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_211, 0, x_210);
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
obj* x_216; obj* x_217; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_102);
x_216 = l_lean_elaborator_to__level___main___closed__2;
x_217 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_216, x_1, x_17);
return x_217;
}
}
default:
{
if (lean::obj_tag(x_22) == 0)
{
obj* x_218; obj* x_221; obj* x_222; obj* x_224; obj* x_228; 
x_218 = lean::cnstr_get(x_102, 0);
lean::inc(x_218);
lean::dec(x_102);
x_221 = l_lean_elaborator_mangle__ident(x_218);
x_222 = lean::cnstr_get(x_17, 4);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_222, 1);
lean::inc(x_224);
lean::dec(x_222);
lean::inc(x_221);
x_228 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_224, x_221);
if (lean::obj_tag(x_228) == 0)
{
obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_235; obj* x_236; obj* x_237; 
lean::dec(x_14);
x_230 = l_lean_name_to__string___closed__1;
x_231 = l_lean_name_to__string__with__sep___main(x_230, x_221);
x_232 = l_lean_elaborator_to__level___main___closed__4;
x_233 = lean::string_append(x_232, x_231);
lean::dec(x_231);
x_235 = l_char_has__repr___closed__1;
x_236 = lean::string_append(x_233, x_235);
x_237 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_236, x_1, x_17);
return x_237;
}
else
{
obj* x_241; obj* x_242; obj* x_243; 
lean::dec(x_228);
lean::dec(x_1);
lean::dec(x_0);
x_241 = level_mk_param(x_221);
x_242 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_242, 0, x_241);
lean::cnstr_set(x_242, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_243 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_243 = x_14;
}
lean::cnstr_set(x_243, 0, x_242);
return x_243;
}
}
else
{
obj* x_247; obj* x_248; 
lean::dec(x_14);
lean::dec(x_22);
lean::dec(x_102);
x_247 = l_lean_elaborator_to__level___main___closed__2;
x_248 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_247, x_1, x_17);
return x_248;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Prop");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_20; uint8 x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
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
obj* x_24; obj* x_27; obj* x_29; obj* x_32; 
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(x_9, x_1, x_29);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_11);
lean::dec(x_27);
x_35 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_37 = x_32;
} else {
 lean::inc(x_35);
 lean::dec(x_32);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_41 = x_32;
} else {
 lean::inc(x_39);
 lean::dec(x_32);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
lean::dec(x_39);
if (lean::is_scalar(x_11)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_11;
}
lean::cnstr_set(x_47, 0, x_27);
lean::cnstr_set(x_47, 1, x_42);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
obj* x_24; obj* x_27; obj* x_29; obj* x_32; obj* x_36; 
x_24 = lean::cnstr_get(x_15, 0);
lean::inc(x_24);
lean::dec(x_15);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_7, 2);
lean::inc(x_32);
lean::dec(x_7);
lean::inc(x_1);
x_36 = l_lean_elaborator_to__pexpr___main(x_32, x_1, x_29);
if (lean::obj_tag(x_36) == 0)
{
obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_27);
x_41 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_43 = x_36;
} else {
 lean::inc(x_41);
 lean::dec(x_36);
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
obj* x_45; obj* x_48; obj* x_50; obj* x_53; 
x_45 = lean::cnstr_get(x_36, 0);
lean::inc(x_45);
lean::dec(x_36);
x_48 = lean::cnstr_get(x_45, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
lean::dec(x_45);
x_53 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_9, x_1, x_50);
if (lean::obj_tag(x_53) == 0)
{
obj* x_57; obj* x_59; obj* x_60; 
lean::dec(x_11);
lean::dec(x_27);
lean::dec(x_48);
x_57 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_59 = x_53;
} else {
 lean::inc(x_57);
 lean::dec(x_53);
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
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_61 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_63 = x_53;
} else {
 lean::inc(x_61);
 lean::dec(x_53);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
lean::dec(x_61);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_27);
lean::cnstr_set(x_69, 1, x_48);
x_70 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1;
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_69);
if (lean::is_scalar(x_11)) {
 x_72 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_72 = x_11;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_64);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_66);
if (lean::is_scalar(x_63)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_63;
}
lean::cnstr_set(x_74, 0, x_73);
return x_74;
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
obj* x_24; obj* x_27; obj* x_29; obj* x_32; 
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_9, x_1, x_29);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_11);
lean::dec(x_27);
x_35 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_37 = x_32;
} else {
 lean::inc(x_35);
 lean::dec(x_32);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_41 = x_32;
} else {
 lean::inc(x_39);
 lean::dec(x_32);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
lean::dec(x_39);
if (lean::is_scalar(x_11)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_11;
}
lean::cnstr_set(x_47, 0, x_27);
lean::cnstr_set(x_47, 1, x_42);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; uint8 x_9; uint8 x_10; 
lean::dec(x_4);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = 1;
x_10 = l_coe__decidable__eq(x_9);
if (x_10 == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_7);
lean::dec(x_2);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_0);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; 
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_15 = x_0;
} else {
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_7);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_2);
lean::cnstr_set(x_22, 1, x_17);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
else
{
obj* x_25; uint8 x_27; uint8 x_28; 
lean::dec(x_4);
x_25 = lean::cnstr_get(x_0, 1);
lean::inc(x_25);
x_27 = 0;
x_28 = l_coe__decidable__eq(x_27);
if (x_28 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_2);
lean::dec(x_25);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_0);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_40; obj* x_41; 
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_33 = x_0;
} else {
 lean::dec(x_0);
 x_33 = lean::box(0);
}
x_34 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_25);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
if (lean::is_scalar(x_33)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_33;
}
lean::cnstr_set(x_40, 0, x_2);
lean::cnstr_set(x_40, 1, x_35);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_37);
return x_41;
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
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; uint8 x_9; uint8 x_10; 
lean::dec(x_4);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = 0;
x_10 = l_coe__decidable__eq(x_9);
if (x_10 == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_7);
lean::dec(x_2);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_0);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; 
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_15 = x_0;
} else {
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_7);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_2);
lean::cnstr_set(x_22, 1, x_17);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_4, 0);
lean::inc(x_24);
lean::dec(x_4);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_30; uint8 x_32; uint8 x_33; 
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
x_32 = 0;
x_33 = l_coe__decidable__eq(x_32);
if (x_33 == 0)
{
obj* x_36; obj* x_37; 
lean::dec(x_2);
lean::dec(x_30);
x_36 = lean::box(0);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_0);
return x_37;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_45; obj* x_46; 
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_38 = x_0;
} else {
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_30);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_2);
lean::cnstr_set(x_45, 1, x_40);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
return x_46;
}
}
else
{
obj* x_48; uint8 x_50; uint8 x_51; 
lean::dec(x_27);
x_48 = lean::cnstr_get(x_0, 1);
lean::inc(x_48);
x_50 = 1;
x_51 = l_coe__decidable__eq(x_50);
if (x_51 == 0)
{
obj* x_54; obj* x_55; 
lean::dec(x_2);
lean::dec(x_48);
x_54 = lean::box(0);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_0);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_63; obj* x_64; 
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_56 = x_0;
} else {
 lean::dec(x_0);
 x_56 = lean::box(0);
}
x_57 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_48);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::is_scalar(x_56)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_56;
}
lean::cnstr_set(x_63, 0, x_2);
lean::cnstr_set(x_63, 1, x_58);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_60);
return x_64;
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
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_20; obj* x_23; 
x_14 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::inc(x_2);
x_23 = l_lean_elaborator_to__pexpr___main(x_20, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_17);
x_29 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
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
obj* x_33; obj* x_36; obj* x_38; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
lean::dec(x_23);
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
lean::dec(x_33);
x_41 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_14, x_2, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_16);
lean::dec(x_36);
lean::dec(x_17);
x_45 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_47 = x_41;
} else {
 lean::inc(x_45);
 lean::dec(x_41);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_49 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_51 = x_41;
} else {
 lean::inc(x_49);
 lean::dec(x_41);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
lean::dec(x_49);
x_57 = lean::box(0);
x_58 = lean::cnstr_get(x_17, 0);
lean::inc(x_58);
lean::dec(x_17);
x_61 = l_lean_elaborator_mangle__ident(x_58);
x_62 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_63 = l_lean_kvmap_set__name(x_57, x_62, x_61);
x_64 = lean_expr_mk_mdata(x_63, x_36);
if (lean::is_scalar(x_16)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_16;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_52);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_51;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
obj* x_69; obj* x_71; obj* x_72; obj* x_75; 
lean::dec(x_11);
x_69 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_71 = x_1;
} else {
 lean::inc(x_69);
 lean::dec(x_1);
 x_71 = lean::box(0);
}
x_72 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_75 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_72, x_2, x_3);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_71);
lean::dec(x_69);
x_80 = lean::cnstr_get(x_75, 0);
if (lean::is_exclusive(x_75)) {
 x_82 = x_75;
} else {
 lean::inc(x_80);
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
obj* x_84; obj* x_87; obj* x_89; obj* x_92; 
x_84 = lean::cnstr_get(x_75, 0);
lean::inc(x_84);
lean::dec(x_75);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_69, x_2, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_71);
lean::dec(x_87);
x_95 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_97 = x_92;
} else {
 lean::inc(x_95);
 lean::dec(x_92);
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
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_99, 1);
lean::inc(x_104);
lean::dec(x_99);
if (lean::is_scalar(x_71)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_71;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_104);
if (lean::is_scalar(x_101)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_101;
}
lean::cnstr_set(x_109, 0, x_108);
return x_109;
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
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; 
lean::dec(x_11);
x_15 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_21 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_15);
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
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
obj* x_30; obj* x_33; obj* x_35; obj* x_38; 
x_30 = lean::cnstr_get(x_21, 0);
lean::inc(x_30);
lean::dec(x_21);
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 1);
lean::inc(x_35);
lean::dec(x_30);
x_38 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_15, x_2, x_35);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_17);
lean::dec(x_33);
x_41 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_43 = x_38;
} else {
 lean::inc(x_41);
 lean::dec(x_38);
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
obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_53; obj* x_54; obj* x_55; 
x_45 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_47 = x_38;
} else {
 lean::inc(x_45);
 lean::dec(x_38);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_45, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
lean::dec(x_45);
if (lean::is_scalar(x_17)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_17;
}
lean::cnstr_set(x_53, 0, x_33);
lean::cnstr_set(x_53, 1, x_48);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_50);
if (lean::is_scalar(x_47)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_47;
}
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
obj* x_56; obj* x_59; 
x_56 = lean::cnstr_get(x_11, 0);
lean::inc(x_56);
lean::dec(x_11);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_64; obj* x_65; obj* x_68; 
x_62 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_64 = x_1;
} else {
 lean::inc(x_62);
 lean::dec(x_1);
 x_64 = lean::box(0);
}
x_65 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_68 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_65, x_2, x_3);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_64);
lean::dec(x_62);
x_73 = lean::cnstr_get(x_68, 0);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_73);
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
obj* x_77; obj* x_80; obj* x_82; obj* x_85; 
x_77 = lean::cnstr_get(x_68, 0);
lean::inc(x_77);
lean::dec(x_68);
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
lean::dec(x_77);
x_85 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_62, x_2, x_82);
if (lean::obj_tag(x_85) == 0)
{
obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_64);
lean::dec(x_80);
x_88 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_90 = x_85;
} else {
 lean::inc(x_88);
 lean::dec(x_85);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
return x_91;
}
else
{
obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_100; obj* x_101; obj* x_102; 
x_92 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_94 = x_85;
} else {
 lean::inc(x_92);
 lean::dec(x_85);
 x_94 = lean::box(0);
}
x_95 = lean::cnstr_get(x_92, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_92, 1);
lean::inc(x_97);
lean::dec(x_92);
if (lean::is_scalar(x_64)) {
 x_100 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_100 = x_64;
}
lean::cnstr_set(x_100, 0, x_80);
lean::cnstr_set(x_100, 1, x_95);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_97);
if (lean::is_scalar(x_94)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_94;
}
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
obj* x_103; obj* x_105; obj* x_106; obj* x_110; 
x_103 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_105 = x_1;
} else {
 lean::inc(x_103);
 lean::dec(x_1);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_59, 0);
lean::inc(x_106);
lean::dec(x_59);
lean::inc(x_2);
x_110 = l_lean_elaborator_to__pexpr___main(x_106, x_2, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_105);
lean::dec(x_103);
x_115 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
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
obj* x_119; obj* x_122; obj* x_124; obj* x_127; 
x_119 = lean::cnstr_get(x_110, 0);
lean::inc(x_119);
lean::dec(x_110);
x_122 = lean::cnstr_get(x_119, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 1);
lean::inc(x_124);
lean::dec(x_119);
x_127 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_103, x_2, x_124);
if (lean::obj_tag(x_127) == 0)
{
obj* x_130; obj* x_132; obj* x_133; 
lean::dec(x_105);
lean::dec(x_122);
x_130 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_132 = x_127;
} else {
 lean::inc(x_130);
 lean::dec(x_127);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_130);
return x_133;
}
else
{
obj* x_134; obj* x_136; obj* x_137; obj* x_139; obj* x_142; obj* x_143; obj* x_144; 
x_134 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_136 = x_127;
} else {
 lean::inc(x_134);
 lean::dec(x_127);
 x_136 = lean::box(0);
}
x_137 = lean::cnstr_get(x_134, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_134, 1);
lean::inc(x_139);
lean::dec(x_134);
if (lean::is_scalar(x_105)) {
 x_142 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_142 = x_105;
}
lean::cnstr_set(x_142, 0, x_122);
lean::cnstr_set(x_142, 1, x_137);
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_139);
if (lean::is_scalar(x_136)) {
 x_144 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_144 = x_136;
}
lean::cnstr_set(x_144, 0, x_143);
return x_144;
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
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_20; obj* x_23; 
x_14 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::inc(x_2);
x_23 = l_lean_elaborator_to__pexpr___main(x_20, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_17);
x_29 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
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
obj* x_33; obj* x_36; obj* x_38; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
lean::dec(x_23);
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
lean::dec(x_33);
x_41 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_14, x_2, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_16);
lean::dec(x_36);
lean::dec(x_17);
x_45 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_47 = x_41;
} else {
 lean::inc(x_45);
 lean::dec(x_41);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_49 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_51 = x_41;
} else {
 lean::inc(x_49);
 lean::dec(x_41);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
lean::dec(x_49);
x_57 = lean::box(0);
x_58 = lean::cnstr_get(x_17, 0);
lean::inc(x_58);
lean::dec(x_17);
x_61 = l_lean_elaborator_mangle__ident(x_58);
x_62 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_63 = l_lean_kvmap_set__name(x_57, x_62, x_61);
x_64 = lean_expr_mk_mdata(x_63, x_36);
if (lean::is_scalar(x_16)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_16;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_52);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_51;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
obj* x_69; obj* x_71; obj* x_72; obj* x_75; 
lean::dec(x_11);
x_69 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_71 = x_1;
} else {
 lean::inc(x_69);
 lean::dec(x_1);
 x_71 = lean::box(0);
}
x_72 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_75 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_72, x_2, x_3);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_71);
lean::dec(x_69);
x_80 = lean::cnstr_get(x_75, 0);
if (lean::is_exclusive(x_75)) {
 x_82 = x_75;
} else {
 lean::inc(x_80);
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
obj* x_84; obj* x_87; obj* x_89; obj* x_92; 
x_84 = lean::cnstr_get(x_75, 0);
lean::inc(x_84);
lean::dec(x_75);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_69, x_2, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_71);
lean::dec(x_87);
x_95 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_97 = x_92;
} else {
 lean::inc(x_95);
 lean::dec(x_92);
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
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_99, 1);
lean::inc(x_104);
lean::dec(x_99);
if (lean::is_scalar(x_71)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_71;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_104);
if (lean::is_scalar(x_101)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_101;
}
lean::cnstr_set(x_109, 0, x_108);
return x_109;
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
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; 
lean::dec(x_11);
x_15 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_21 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_15);
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
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
obj* x_30; obj* x_33; obj* x_35; obj* x_38; 
x_30 = lean::cnstr_get(x_21, 0);
lean::inc(x_30);
lean::dec(x_21);
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 1);
lean::inc(x_35);
lean::dec(x_30);
x_38 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_15, x_2, x_35);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_17);
lean::dec(x_33);
x_41 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_43 = x_38;
} else {
 lean::inc(x_41);
 lean::dec(x_38);
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
obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_53; obj* x_54; obj* x_55; 
x_45 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_47 = x_38;
} else {
 lean::inc(x_45);
 lean::dec(x_38);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_45, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
lean::dec(x_45);
if (lean::is_scalar(x_17)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_17;
}
lean::cnstr_set(x_53, 0, x_33);
lean::cnstr_set(x_53, 1, x_48);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_50);
if (lean::is_scalar(x_47)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_47;
}
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
obj* x_56; obj* x_59; 
x_56 = lean::cnstr_get(x_11, 0);
lean::inc(x_56);
lean::dec(x_11);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_64; obj* x_65; obj* x_68; 
x_62 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_64 = x_1;
} else {
 lean::inc(x_62);
 lean::dec(x_1);
 x_64 = lean::box(0);
}
x_65 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_68 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_65, x_2, x_3);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_64);
lean::dec(x_62);
x_73 = lean::cnstr_get(x_68, 0);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_73);
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
obj* x_77; obj* x_80; obj* x_82; obj* x_85; 
x_77 = lean::cnstr_get(x_68, 0);
lean::inc(x_77);
lean::dec(x_68);
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
lean::dec(x_77);
x_85 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_62, x_2, x_82);
if (lean::obj_tag(x_85) == 0)
{
obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_64);
lean::dec(x_80);
x_88 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_90 = x_85;
} else {
 lean::inc(x_88);
 lean::dec(x_85);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
return x_91;
}
else
{
obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_100; obj* x_101; obj* x_102; 
x_92 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_94 = x_85;
} else {
 lean::inc(x_92);
 lean::dec(x_85);
 x_94 = lean::box(0);
}
x_95 = lean::cnstr_get(x_92, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_92, 1);
lean::inc(x_97);
lean::dec(x_92);
if (lean::is_scalar(x_64)) {
 x_100 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_100 = x_64;
}
lean::cnstr_set(x_100, 0, x_80);
lean::cnstr_set(x_100, 1, x_95);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_97);
if (lean::is_scalar(x_94)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_94;
}
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
obj* x_103; obj* x_105; obj* x_106; obj* x_110; 
x_103 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_105 = x_1;
} else {
 lean::inc(x_103);
 lean::dec(x_1);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_59, 0);
lean::inc(x_106);
lean::dec(x_59);
lean::inc(x_2);
x_110 = l_lean_elaborator_to__pexpr___main(x_106, x_2, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_105);
lean::dec(x_103);
x_115 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
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
obj* x_119; obj* x_122; obj* x_124; obj* x_127; 
x_119 = lean::cnstr_get(x_110, 0);
lean::inc(x_119);
lean::dec(x_110);
x_122 = lean::cnstr_get(x_119, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 1);
lean::inc(x_124);
lean::dec(x_119);
x_127 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_103, x_2, x_124);
if (lean::obj_tag(x_127) == 0)
{
obj* x_130; obj* x_132; obj* x_133; 
lean::dec(x_105);
lean::dec(x_122);
x_130 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_132 = x_127;
} else {
 lean::inc(x_130);
 lean::dec(x_127);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_130);
return x_133;
}
else
{
obj* x_134; obj* x_136; obj* x_137; obj* x_139; obj* x_142; obj* x_143; obj* x_144; 
x_134 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_136 = x_127;
} else {
 lean::inc(x_134);
 lean::dec(x_127);
 x_136 = lean::box(0);
}
x_137 = lean::cnstr_get(x_134, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_134, 1);
lean::inc(x_139);
lean::dec(x_134);
if (lean::is_scalar(x_105)) {
 x_142 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_142 = x_105;
}
lean::cnstr_set(x_142, 0, x_122);
lean::cnstr_set(x_142, 1, x_137);
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_139);
if (lean::is_scalar(x_136)) {
 x_144 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_144 = x_136;
}
lean::cnstr_set(x_144, 0, x_143);
return x_144;
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
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_20; obj* x_23; 
x_14 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::inc(x_2);
x_23 = l_lean_elaborator_to__pexpr___main(x_20, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_17);
x_29 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
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
obj* x_33; obj* x_36; obj* x_38; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
lean::dec(x_23);
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
lean::dec(x_33);
x_41 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_14, x_2, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_16);
lean::dec(x_36);
lean::dec(x_17);
x_45 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_47 = x_41;
} else {
 lean::inc(x_45);
 lean::dec(x_41);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_49 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_51 = x_41;
} else {
 lean::inc(x_49);
 lean::dec(x_41);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
lean::dec(x_49);
x_57 = lean::box(0);
x_58 = lean::cnstr_get(x_17, 0);
lean::inc(x_58);
lean::dec(x_17);
x_61 = l_lean_elaborator_mangle__ident(x_58);
x_62 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_63 = l_lean_kvmap_set__name(x_57, x_62, x_61);
x_64 = lean_expr_mk_mdata(x_63, x_36);
if (lean::is_scalar(x_16)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_16;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_52);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_51;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
obj* x_69; obj* x_71; obj* x_72; obj* x_75; 
lean::dec(x_11);
x_69 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_71 = x_1;
} else {
 lean::inc(x_69);
 lean::dec(x_1);
 x_71 = lean::box(0);
}
x_72 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_75 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_72, x_2, x_3);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_71);
lean::dec(x_69);
x_80 = lean::cnstr_get(x_75, 0);
if (lean::is_exclusive(x_75)) {
 x_82 = x_75;
} else {
 lean::inc(x_80);
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
obj* x_84; obj* x_87; obj* x_89; obj* x_92; 
x_84 = lean::cnstr_get(x_75, 0);
lean::inc(x_84);
lean::dec(x_75);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_69, x_2, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_71);
lean::dec(x_87);
x_95 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_97 = x_92;
} else {
 lean::inc(x_95);
 lean::dec(x_92);
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
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_99, 1);
lean::inc(x_104);
lean::dec(x_99);
if (lean::is_scalar(x_71)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_71;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_104);
if (lean::is_scalar(x_101)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_101;
}
lean::cnstr_set(x_109, 0, x_108);
return x_109;
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
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; 
lean::dec(x_11);
x_15 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_21 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_15);
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
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
obj* x_30; obj* x_33; obj* x_35; obj* x_38; 
x_30 = lean::cnstr_get(x_21, 0);
lean::inc(x_30);
lean::dec(x_21);
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 1);
lean::inc(x_35);
lean::dec(x_30);
x_38 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_15, x_2, x_35);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_17);
lean::dec(x_33);
x_41 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_43 = x_38;
} else {
 lean::inc(x_41);
 lean::dec(x_38);
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
obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_53; obj* x_54; obj* x_55; 
x_45 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_47 = x_38;
} else {
 lean::inc(x_45);
 lean::dec(x_38);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_45, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
lean::dec(x_45);
if (lean::is_scalar(x_17)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_17;
}
lean::cnstr_set(x_53, 0, x_33);
lean::cnstr_set(x_53, 1, x_48);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_50);
if (lean::is_scalar(x_47)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_47;
}
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
obj* x_56; obj* x_59; 
x_56 = lean::cnstr_get(x_11, 0);
lean::inc(x_56);
lean::dec(x_11);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_64; obj* x_65; obj* x_68; 
x_62 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_64 = x_1;
} else {
 lean::inc(x_62);
 lean::dec(x_1);
 x_64 = lean::box(0);
}
x_65 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_68 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_65, x_2, x_3);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_64);
lean::dec(x_62);
x_73 = lean::cnstr_get(x_68, 0);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_73);
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
obj* x_77; obj* x_80; obj* x_82; obj* x_85; 
x_77 = lean::cnstr_get(x_68, 0);
lean::inc(x_77);
lean::dec(x_68);
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
lean::dec(x_77);
x_85 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_62, x_2, x_82);
if (lean::obj_tag(x_85) == 0)
{
obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_64);
lean::dec(x_80);
x_88 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_90 = x_85;
} else {
 lean::inc(x_88);
 lean::dec(x_85);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
return x_91;
}
else
{
obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_100; obj* x_101; obj* x_102; 
x_92 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_94 = x_85;
} else {
 lean::inc(x_92);
 lean::dec(x_85);
 x_94 = lean::box(0);
}
x_95 = lean::cnstr_get(x_92, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_92, 1);
lean::inc(x_97);
lean::dec(x_92);
if (lean::is_scalar(x_64)) {
 x_100 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_100 = x_64;
}
lean::cnstr_set(x_100, 0, x_80);
lean::cnstr_set(x_100, 1, x_95);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_97);
if (lean::is_scalar(x_94)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_94;
}
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
obj* x_103; obj* x_105; obj* x_106; obj* x_110; 
x_103 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_105 = x_1;
} else {
 lean::inc(x_103);
 lean::dec(x_1);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_59, 0);
lean::inc(x_106);
lean::dec(x_59);
lean::inc(x_2);
x_110 = l_lean_elaborator_to__pexpr___main(x_106, x_2, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_105);
lean::dec(x_103);
x_115 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
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
obj* x_119; obj* x_122; obj* x_124; obj* x_127; 
x_119 = lean::cnstr_get(x_110, 0);
lean::inc(x_119);
lean::dec(x_110);
x_122 = lean::cnstr_get(x_119, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 1);
lean::inc(x_124);
lean::dec(x_119);
x_127 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_103, x_2, x_124);
if (lean::obj_tag(x_127) == 0)
{
obj* x_130; obj* x_132; obj* x_133; 
lean::dec(x_105);
lean::dec(x_122);
x_130 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_132 = x_127;
} else {
 lean::inc(x_130);
 lean::dec(x_127);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_130);
return x_133;
}
else
{
obj* x_134; obj* x_136; obj* x_137; obj* x_139; obj* x_142; obj* x_143; obj* x_144; 
x_134 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_136 = x_127;
} else {
 lean::inc(x_134);
 lean::dec(x_127);
 x_136 = lean::box(0);
}
x_137 = lean::cnstr_get(x_134, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_134, 1);
lean::inc(x_139);
lean::dec(x_134);
if (lean::is_scalar(x_105)) {
 x_142 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_142 = x_105;
}
lean::cnstr_set(x_142, 0, x_122);
lean::cnstr_set(x_142, 1, x_137);
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_139);
if (lean::is_scalar(x_136)) {
 x_144 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_144 = x_136;
}
lean::cnstr_set(x_144, 0, x_143);
return x_144;
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
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_20; obj* x_23; 
x_14 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::inc(x_2);
x_23 = l_lean_elaborator_to__pexpr___main(x_20, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_17);
x_29 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
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
obj* x_33; obj* x_36; obj* x_38; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
lean::dec(x_23);
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
lean::dec(x_33);
x_41 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_14, x_2, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_16);
lean::dec(x_36);
lean::dec(x_17);
x_45 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_47 = x_41;
} else {
 lean::inc(x_45);
 lean::dec(x_41);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_49 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_51 = x_41;
} else {
 lean::inc(x_49);
 lean::dec(x_41);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
lean::dec(x_49);
x_57 = lean::box(0);
x_58 = lean::cnstr_get(x_17, 0);
lean::inc(x_58);
lean::dec(x_17);
x_61 = l_lean_elaborator_mangle__ident(x_58);
x_62 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_63 = l_lean_kvmap_set__name(x_57, x_62, x_61);
x_64 = lean_expr_mk_mdata(x_63, x_36);
if (lean::is_scalar(x_16)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_16;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_52);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_51;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
obj* x_69; obj* x_71; obj* x_72; obj* x_75; 
lean::dec(x_11);
x_69 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_71 = x_1;
} else {
 lean::inc(x_69);
 lean::dec(x_1);
 x_71 = lean::box(0);
}
x_72 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_75 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_72, x_2, x_3);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_71);
lean::dec(x_69);
x_80 = lean::cnstr_get(x_75, 0);
if (lean::is_exclusive(x_75)) {
 x_82 = x_75;
} else {
 lean::inc(x_80);
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
obj* x_84; obj* x_87; obj* x_89; obj* x_92; 
x_84 = lean::cnstr_get(x_75, 0);
lean::inc(x_84);
lean::dec(x_75);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_69, x_2, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_71);
lean::dec(x_87);
x_95 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_97 = x_92;
} else {
 lean::inc(x_95);
 lean::dec(x_92);
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
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_99, 1);
lean::inc(x_104);
lean::dec(x_99);
if (lean::is_scalar(x_71)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_71;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_104);
if (lean::is_scalar(x_101)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_101;
}
lean::cnstr_set(x_109, 0, x_108);
return x_109;
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
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; 
lean::dec(x_11);
x_15 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
x_18 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_21 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_18, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_15);
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
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
obj* x_30; obj* x_33; obj* x_35; obj* x_38; 
x_30 = lean::cnstr_get(x_21, 0);
lean::inc(x_30);
lean::dec(x_21);
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 1);
lean::inc(x_35);
lean::dec(x_30);
x_38 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_15, x_2, x_35);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_17);
lean::dec(x_33);
x_41 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_43 = x_38;
} else {
 lean::inc(x_41);
 lean::dec(x_38);
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
obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_53; obj* x_54; obj* x_55; 
x_45 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_47 = x_38;
} else {
 lean::inc(x_45);
 lean::dec(x_38);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_45, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
lean::dec(x_45);
if (lean::is_scalar(x_17)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_17;
}
lean::cnstr_set(x_53, 0, x_33);
lean::cnstr_set(x_53, 1, x_48);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_50);
if (lean::is_scalar(x_47)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_47;
}
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
obj* x_56; obj* x_59; 
x_56 = lean::cnstr_get(x_11, 0);
lean::inc(x_56);
lean::dec(x_11);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_64; obj* x_65; obj* x_68; 
x_62 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_64 = x_1;
} else {
 lean::inc(x_62);
 lean::dec(x_1);
 x_64 = lean::box(0);
}
x_65 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_68 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_65, x_2, x_3);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_64);
lean::dec(x_62);
x_73 = lean::cnstr_get(x_68, 0);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_73);
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
obj* x_77; obj* x_80; obj* x_82; obj* x_85; 
x_77 = lean::cnstr_get(x_68, 0);
lean::inc(x_77);
lean::dec(x_68);
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
lean::dec(x_77);
x_85 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_62, x_2, x_82);
if (lean::obj_tag(x_85) == 0)
{
obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_64);
lean::dec(x_80);
x_88 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_90 = x_85;
} else {
 lean::inc(x_88);
 lean::dec(x_85);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
return x_91;
}
else
{
obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_100; obj* x_101; obj* x_102; 
x_92 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_94 = x_85;
} else {
 lean::inc(x_92);
 lean::dec(x_85);
 x_94 = lean::box(0);
}
x_95 = lean::cnstr_get(x_92, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_92, 1);
lean::inc(x_97);
lean::dec(x_92);
if (lean::is_scalar(x_64)) {
 x_100 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_100 = x_64;
}
lean::cnstr_set(x_100, 0, x_80);
lean::cnstr_set(x_100, 1, x_95);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_97);
if (lean::is_scalar(x_94)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_94;
}
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
obj* x_103; obj* x_105; obj* x_106; obj* x_110; 
x_103 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_105 = x_1;
} else {
 lean::inc(x_103);
 lean::dec(x_1);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_59, 0);
lean::inc(x_106);
lean::dec(x_59);
lean::inc(x_2);
x_110 = l_lean_elaborator_to__pexpr___main(x_106, x_2, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_105);
lean::dec(x_103);
x_115 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
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
obj* x_119; obj* x_122; obj* x_124; obj* x_127; 
x_119 = lean::cnstr_get(x_110, 0);
lean::inc(x_119);
lean::dec(x_110);
x_122 = lean::cnstr_get(x_119, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 1);
lean::inc(x_124);
lean::dec(x_119);
x_127 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_103, x_2, x_124);
if (lean::obj_tag(x_127) == 0)
{
obj* x_130; obj* x_132; obj* x_133; 
lean::dec(x_105);
lean::dec(x_122);
x_130 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_132 = x_127;
} else {
 lean::inc(x_130);
 lean::dec(x_127);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_130);
return x_133;
}
else
{
obj* x_134; obj* x_136; obj* x_137; obj* x_139; obj* x_142; obj* x_143; obj* x_144; 
x_134 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_136 = x_127;
} else {
 lean::inc(x_134);
 lean::dec(x_127);
 x_136 = lean::box(0);
}
x_137 = lean::cnstr_get(x_134, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_134, 1);
lean::inc(x_139);
lean::dec(x_134);
if (lean::is_scalar(x_105)) {
 x_142 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_142 = x_105;
}
lean::cnstr_set(x_142, 0, x_122);
lean::cnstr_set(x_142, 1, x_137);
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_139);
if (lean::is_scalar(x_136)) {
 x_144 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_144 = x_136;
}
lean::cnstr_set(x_144, 0, x_143);
return x_144;
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
obj* x_21; obj* x_24; obj* x_26; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_11);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_34 = x_29;
} else {
 lean::inc(x_32);
 lean::dec(x_29);
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
lean::dec(x_36);
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
x_45 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_21; obj* x_24; obj* x_26; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_11);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_34 = x_29;
} else {
 lean::inc(x_32);
 lean::dec(x_29);
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
lean::dec(x_36);
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
x_45 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("annotation");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("preresolved");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_lean_kvmap_set__name(x_0, x_3, x_5);
return x_6;
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
if (x_21 == 0)
{
obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_81; 
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
lean::inc(x_76);
x_78 = lean::cnstr_get(x_73, 1);
lean::inc(x_78);
lean::dec(x_73);
x_81 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_81) == 0)
{
obj* x_83; obj* x_84; 
lean::dec(x_1);
x_83 = lean::alloc_cnstr(0, 2, 0);
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
x_106 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_110; obj* x_112; obj* x_113; obj* x_115; obj* x_118; obj* x_119; 
lean::dec(x_1);
lean::dec(x_0);
x_110 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 x_112 = x_66;
} else {
 lean::inc(x_110);
 lean::dec(x_66);
 x_112 = lean::box(0);
}
x_113 = lean::cnstr_get(x_110, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_110, 1);
lean::inc(x_115);
lean::dec(x_110);
x_118 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_118, 0, x_113);
lean::cnstr_set(x_118, 1, x_115);
if (lean::is_scalar(x_112)) {
 x_119 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_119 = x_112;
}
lean::cnstr_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
obj* x_120; obj* x_121; obj* x_125; obj* x_126; obj* x_128; obj* x_130; 
x_120 = l_lean_parser_term_match_has__view;
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
lean::dec(x_120);
lean::inc(x_0);
x_125 = lean::apply_1(x_121, x_0);
x_126 = lean::cnstr_get(x_125, 5);
lean::inc(x_126);
x_128 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(x_126);
lean::inc(x_1);
x_130 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_128, x_1, x_2);
if (lean::obj_tag(x_130) == 0)
{
obj* x_132; obj* x_134; obj* x_135; 
lean::dec(x_125);
x_132 = lean::cnstr_get(x_130, 0);
if (lean::is_exclusive(x_130)) {
 x_134 = x_130;
} else {
 lean::inc(x_132);
 lean::dec(x_130);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_132);
x_12 = x_135;
goto lbl_13;
}
else
{
obj* x_136; obj* x_139; obj* x_141; obj* x_144; obj* x_146; obj* x_148; 
x_136 = lean::cnstr_get(x_130, 0);
lean::inc(x_136);
lean::dec(x_130);
x_139 = lean::cnstr_get(x_136, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_136, 1);
lean::inc(x_141);
lean::dec(x_136);
x_144 = lean::cnstr_get(x_125, 2);
lean::inc(x_144);
x_146 = l_lean_expander_get__opt__type___main(x_144);
lean::inc(x_1);
x_148 = l_lean_elaborator_to__pexpr___main(x_146, x_1, x_141);
if (lean::obj_tag(x_148) == 0)
{
obj* x_151; obj* x_153; obj* x_154; 
lean::dec(x_139);
lean::dec(x_125);
x_151 = lean::cnstr_get(x_148, 0);
if (lean::is_exclusive(x_148)) {
 x_153 = x_148;
} else {
 lean::inc(x_151);
 lean::dec(x_148);
 x_153 = lean::box(0);
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_151);
x_12 = x_154;
goto lbl_13;
}
else
{
obj* x_155; obj* x_158; obj* x_160; obj* x_163; 
x_155 = lean::cnstr_get(x_148, 0);
lean::inc(x_155);
lean::dec(x_148);
x_158 = lean::cnstr_get(x_155, 0);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_155, 1);
lean::inc(x_160);
lean::dec(x_155);
x_163 = l_lean_elaborator_mk__eqns(x_158, x_139);
switch (lean::obj_tag(x_163)) {
case 10:
{
obj* x_164; obj* x_166; obj* x_169; obj* x_173; 
x_164 = lean::cnstr_get(x_163, 0);
lean::inc(x_164);
x_166 = lean::cnstr_get(x_163, 1);
lean::inc(x_166);
lean::dec(x_163);
x_169 = lean::cnstr_get(x_125, 1);
lean::inc(x_169);
lean::dec(x_125);
lean::inc(x_1);
x_173 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_169, x_1, x_160);
if (lean::obj_tag(x_173) == 0)
{
obj* x_176; obj* x_178; obj* x_179; 
lean::dec(x_164);
lean::dec(x_166);
x_176 = lean::cnstr_get(x_173, 0);
if (lean::is_exclusive(x_173)) {
 x_178 = x_173;
} else {
 lean::inc(x_176);
 lean::dec(x_173);
 x_178 = lean::box(0);
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_176);
x_12 = x_179;
goto lbl_13;
}
else
{
obj* x_180; obj* x_182; obj* x_183; obj* x_185; obj* x_188; uint8 x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
x_180 = lean::cnstr_get(x_173, 0);
if (lean::is_exclusive(x_173)) {
 x_182 = x_173;
} else {
 lean::inc(x_180);
 lean::dec(x_173);
 x_182 = lean::box(0);
}
x_183 = lean::cnstr_get(x_180, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_180, 1);
lean::inc(x_185);
lean::dec(x_180);
x_188 = l_lean_elaborator_to__pexpr___main___closed__24;
x_189 = 1;
x_190 = l_lean_kvmap_set__bool(x_164, x_188, x_189);
x_191 = lean_expr_mk_mdata(x_190, x_166);
x_192 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_191, x_183);
x_193 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_193, 0, x_192);
lean::cnstr_set(x_193, 1, x_185);
if (lean::is_scalar(x_182)) {
 x_194 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_194 = x_182;
}
lean::cnstr_set(x_194, 0, x_193);
x_12 = x_194;
goto lbl_13;
}
}
default:
{
obj* x_197; obj* x_200; 
lean::dec(x_163);
lean::dec(x_125);
x_197 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_1);
lean::inc(x_0);
x_200 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_197, x_1, x_160);
x_12 = x_200;
goto lbl_13;
}
}
}
}
}
}
else
{
obj* x_201; obj* x_202; obj* x_206; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_215; obj* x_216; 
x_201 = l_lean_parser_term_struct__inst_has__view;
x_202 = lean::cnstr_get(x_201, 0);
lean::inc(x_202);
lean::dec(x_201);
lean::inc(x_0);
x_206 = lean::apply_1(x_202, x_0);
x_207 = lean::cnstr_get(x_206, 3);
lean::inc(x_207);
x_209 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_207);
x_210 = lean::cnstr_get(x_209, 0);
lean::inc(x_210);
x_212 = lean::cnstr_get(x_209, 1);
lean::inc(x_212);
lean::dec(x_209);
x_215 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_212);
x_216 = lean::cnstr_get(x_215, 1);
lean::inc(x_216);
if (lean::obj_tag(x_216) == 0)
{
obj* x_218; obj* x_223; 
x_218 = lean::cnstr_get(x_215, 0);
lean::inc(x_218);
lean::dec(x_215);
lean::inc(x_1);
lean::inc(x_0);
x_223 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_210, x_1, x_2);
if (lean::obj_tag(x_223) == 0)
{
obj* x_229; obj* x_231; obj* x_232; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_218);
lean::dec(x_206);
x_229 = lean::cnstr_get(x_223, 0);
if (lean::is_exclusive(x_223)) {
 x_231 = x_223;
} else {
 lean::inc(x_229);
 lean::dec(x_223);
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
obj* x_233; obj* x_236; obj* x_238; obj* x_241; obj* x_245; 
x_233 = lean::cnstr_get(x_223, 0);
lean::inc(x_233);
lean::dec(x_223);
x_236 = lean::cnstr_get(x_233, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get(x_233, 1);
lean::inc(x_238);
lean::dec(x_233);
lean::inc(x_1);
lean::inc(x_0);
x_245 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_218, x_1, x_238);
if (lean::obj_tag(x_245) == 0)
{
obj* x_251; obj* x_253; obj* x_254; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_236);
x_251 = lean::cnstr_get(x_245, 0);
if (lean::is_exclusive(x_245)) {
 x_253 = x_245;
} else {
 lean::inc(x_251);
 lean::dec(x_245);
 x_253 = lean::box(0);
}
if (lean::is_scalar(x_253)) {
 x_254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_254 = x_253;
}
lean::cnstr_set(x_254, 0, x_251);
return x_254;
}
else
{
obj* x_255; 
x_255 = lean::cnstr_get(x_206, 2);
lean::inc(x_255);
if (lean::obj_tag(x_255) == 0)
{
obj* x_257; obj* x_260; obj* x_262; obj* x_265; 
x_257 = lean::cnstr_get(x_245, 0);
lean::inc(x_257);
lean::dec(x_245);
x_260 = lean::cnstr_get(x_257, 0);
lean::inc(x_260);
x_262 = lean::cnstr_get(x_257, 1);
lean::inc(x_262);
lean::dec(x_257);
x_265 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_265, 0, x_260);
lean::cnstr_set(x_265, 1, x_262);
x_241 = x_265;
goto lbl_242;
}
else
{
obj* x_266; obj* x_269; obj* x_271; obj* x_274; obj* x_277; obj* x_281; 
x_266 = lean::cnstr_get(x_245, 0);
lean::inc(x_266);
lean::dec(x_245);
x_269 = lean::cnstr_get(x_266, 0);
lean::inc(x_269);
x_271 = lean::cnstr_get(x_266, 1);
lean::inc(x_271);
lean::dec(x_266);
x_274 = lean::cnstr_get(x_255, 0);
lean::inc(x_274);
lean::dec(x_255);
x_277 = lean::cnstr_get(x_274, 0);
lean::inc(x_277);
lean::dec(x_274);
lean::inc(x_1);
x_281 = l_lean_elaborator_to__pexpr___main(x_277, x_1, x_271);
if (lean::obj_tag(x_281) == 0)
{
obj* x_288; obj* x_290; obj* x_291; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_269);
lean::dec(x_236);
x_288 = lean::cnstr_get(x_281, 0);
if (lean::is_exclusive(x_281)) {
 x_290 = x_281;
} else {
 lean::inc(x_288);
 lean::dec(x_281);
 x_290 = lean::box(0);
}
if (lean::is_scalar(x_290)) {
 x_291 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_291 = x_290;
}
lean::cnstr_set(x_291, 0, x_288);
return x_291;
}
else
{
obj* x_292; obj* x_295; obj* x_297; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
x_292 = lean::cnstr_get(x_281, 0);
lean::inc(x_292);
lean::dec(x_281);
x_295 = lean::cnstr_get(x_292, 0);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_292, 1);
lean::inc(x_297);
lean::dec(x_292);
x_300 = lean::box(0);
x_301 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_301, 0, x_295);
lean::cnstr_set(x_301, 1, x_300);
x_302 = l_list_append___rarg(x_269, x_301);
x_303 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_303, 0, x_302);
lean::cnstr_set(x_303, 1, x_297);
x_241 = x_303;
goto lbl_242;
}
}
}
lbl_242:
{
obj* x_304; obj* x_306; obj* x_309; obj* x_310; obj* x_312; obj* x_313; obj* x_314; obj* x_315; uint8 x_316; obj* x_317; obj* x_318; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; obj* x_331; obj* x_332; 
x_304 = lean::cnstr_get(x_241, 0);
lean::inc(x_304);
x_306 = lean::cnstr_get(x_241, 1);
lean::inc(x_306);
lean::dec(x_241);
x_309 = lean::box(0);
x_310 = lean::mk_nat_obj(0u);
lean::inc(x_236);
x_312 = l_list_length__aux___main___rarg(x_236, x_310);
x_313 = l_lean_elaborator_to__pexpr___main___closed__25;
x_314 = l_lean_kvmap_set__nat(x_309, x_313, x_312);
x_315 = l_lean_elaborator_to__pexpr___main___closed__26;
x_316 = 0;
x_317 = l_lean_kvmap_set__bool(x_314, x_315, x_316);
x_318 = lean::cnstr_get(x_206, 1);
lean::inc(x_318);
lean::dec(x_206);
x_321 = l_lean_elaborator_to__pexpr___main___closed__27;
x_322 = l_option_map___rarg(x_321, x_318);
x_323 = l_lean_elaborator_to__pexpr___main___closed__28;
x_324 = l_option_map___rarg(x_323, x_322);
x_325 = lean::box(0);
x_326 = l_option_get__or__else___main___rarg(x_324, x_325);
x_327 = l_lean_elaborator_to__pexpr___main___closed__29;
x_328 = l_lean_kvmap_set__name(x_317, x_327, x_326);
x_329 = l_list_append___rarg(x_236, x_304);
x_330 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(x_329);
x_331 = lean_expr_mk_mdata(x_328, x_330);
x_332 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_332, 0, x_331);
lean::cnstr_set(x_332, 1, x_306);
x_14 = x_332;
goto lbl_15;
}
}
}
else
{
obj* x_333; obj* x_335; 
x_333 = lean::cnstr_get(x_216, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_333, 0);
lean::inc(x_335);
lean::dec(x_333);
if (lean::obj_tag(x_335) == 0)
{
obj* x_338; obj* x_339; obj* x_342; obj* x_343; obj* x_346; obj* x_347; obj* x_349; 
if (lean::is_exclusive(x_216)) {
 lean::cnstr_release(x_216, 0);
 lean::cnstr_release(x_216, 1);
 x_338 = x_216;
} else {
 lean::dec(x_216);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_215, 0);
lean::inc(x_339);
lean::dec(x_215);
x_342 = l_lean_parser_term_struct__inst__item_has__view;
x_343 = lean::cnstr_get(x_342, 1);
lean::inc(x_343);
lean::dec(x_342);
x_346 = lean::apply_1(x_343, x_335);
x_347 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
x_349 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_346, x_347, x_1, x_2);
if (lean::obj_tag(x_349) == 0)
{
obj* x_357; obj* x_359; obj* x_360; 
lean::dec(x_339);
lean::dec(x_338);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_210);
lean::dec(x_206);
x_357 = lean::cnstr_get(x_349, 0);
if (lean::is_exclusive(x_349)) {
 x_359 = x_349;
} else {
 lean::inc(x_357);
 lean::dec(x_349);
 x_359 = lean::box(0);
}
if (lean::is_scalar(x_359)) {
 x_360 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_360 = x_359;
}
lean::cnstr_set(x_360, 0, x_357);
return x_360;
}
else
{
obj* x_361; obj* x_364; obj* x_366; obj* x_371; 
x_361 = lean::cnstr_get(x_349, 0);
lean::inc(x_361);
lean::dec(x_349);
x_364 = lean::cnstr_get(x_361, 0);
lean::inc(x_364);
x_366 = lean::cnstr_get(x_361, 1);
lean::inc(x_366);
lean::dec(x_361);
lean::inc(x_1);
lean::inc(x_0);
x_371 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_210, x_1, x_366);
if (lean::obj_tag(x_371) == 0)
{
obj* x_379; obj* x_381; obj* x_382; 
lean::dec(x_339);
lean::dec(x_338);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_364);
lean::dec(x_206);
x_379 = lean::cnstr_get(x_371, 0);
if (lean::is_exclusive(x_371)) {
 x_381 = x_371;
} else {
 lean::inc(x_379);
 lean::dec(x_371);
 x_381 = lean::box(0);
}
if (lean::is_scalar(x_381)) {
 x_382 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_382 = x_381;
}
lean::cnstr_set(x_382, 0, x_379);
return x_382;
}
else
{
obj* x_383; obj* x_386; obj* x_388; obj* x_391; obj* x_395; 
x_383 = lean::cnstr_get(x_371, 0);
lean::inc(x_383);
lean::dec(x_371);
x_386 = lean::cnstr_get(x_383, 0);
lean::inc(x_386);
x_388 = lean::cnstr_get(x_383, 1);
lean::inc(x_388);
lean::dec(x_383);
lean::inc(x_1);
lean::inc(x_0);
x_395 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_339, x_1, x_388);
if (lean::obj_tag(x_395) == 0)
{
obj* x_403; obj* x_405; obj* x_406; 
lean::dec(x_338);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_364);
lean::dec(x_386);
lean::dec(x_206);
x_403 = lean::cnstr_get(x_395, 0);
if (lean::is_exclusive(x_395)) {
 x_405 = x_395;
} else {
 lean::inc(x_403);
 lean::dec(x_395);
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
obj* x_407; 
x_407 = lean::cnstr_get(x_206, 2);
lean::inc(x_407);
if (lean::obj_tag(x_407) == 0)
{
obj* x_410; obj* x_413; obj* x_415; obj* x_418; 
lean::dec(x_338);
x_410 = lean::cnstr_get(x_395, 0);
lean::inc(x_410);
lean::dec(x_395);
x_413 = lean::cnstr_get(x_410, 0);
lean::inc(x_413);
x_415 = lean::cnstr_get(x_410, 1);
lean::inc(x_415);
lean::dec(x_410);
x_418 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_418, 0, x_413);
lean::cnstr_set(x_418, 1, x_415);
x_391 = x_418;
goto lbl_392;
}
else
{
obj* x_419; obj* x_422; obj* x_424; obj* x_427; obj* x_430; obj* x_434; 
x_419 = lean::cnstr_get(x_395, 0);
lean::inc(x_419);
lean::dec(x_395);
x_422 = lean::cnstr_get(x_419, 0);
lean::inc(x_422);
x_424 = lean::cnstr_get(x_419, 1);
lean::inc(x_424);
lean::dec(x_419);
x_427 = lean::cnstr_get(x_407, 0);
lean::inc(x_427);
lean::dec(x_407);
x_430 = lean::cnstr_get(x_427, 0);
lean::inc(x_430);
lean::dec(x_427);
lean::inc(x_1);
x_434 = l_lean_elaborator_to__pexpr___main(x_430, x_1, x_424);
if (lean::obj_tag(x_434) == 0)
{
obj* x_443; obj* x_445; obj* x_446; 
lean::dec(x_338);
lean::dec(x_422);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_364);
lean::dec(x_386);
lean::dec(x_206);
x_443 = lean::cnstr_get(x_434, 0);
if (lean::is_exclusive(x_434)) {
 x_445 = x_434;
} else {
 lean::inc(x_443);
 lean::dec(x_434);
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
obj* x_447; obj* x_450; obj* x_452; obj* x_455; obj* x_456; obj* x_457; obj* x_458; 
x_447 = lean::cnstr_get(x_434, 0);
lean::inc(x_447);
lean::dec(x_434);
x_450 = lean::cnstr_get(x_447, 0);
lean::inc(x_450);
x_452 = lean::cnstr_get(x_447, 1);
lean::inc(x_452);
lean::dec(x_447);
x_455 = lean::box(0);
if (lean::is_scalar(x_338)) {
 x_456 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_456 = x_338;
}
lean::cnstr_set(x_456, 0, x_450);
lean::cnstr_set(x_456, 1, x_455);
x_457 = l_list_append___rarg(x_422, x_456);
x_458 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_458, 0, x_457);
lean::cnstr_set(x_458, 1, x_452);
x_391 = x_458;
goto lbl_392;
}
}
}
lbl_392:
{
obj* x_459; obj* x_461; obj* x_464; obj* x_465; obj* x_467; obj* x_468; obj* x_469; obj* x_470; uint8 x_471; obj* x_472; obj* x_473; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; obj* x_487; 
x_459 = lean::cnstr_get(x_391, 0);
lean::inc(x_459);
x_461 = lean::cnstr_get(x_391, 1);
lean::inc(x_461);
lean::dec(x_391);
x_464 = lean::box(0);
x_465 = lean::mk_nat_obj(0u);
lean::inc(x_386);
x_467 = l_list_length__aux___main___rarg(x_386, x_465);
x_468 = l_lean_elaborator_to__pexpr___main___closed__25;
x_469 = l_lean_kvmap_set__nat(x_464, x_468, x_467);
x_470 = l_lean_elaborator_to__pexpr___main___closed__26;
x_471 = lean::unbox(x_364);
x_472 = l_lean_kvmap_set__bool(x_469, x_470, x_471);
x_473 = lean::cnstr_get(x_206, 1);
lean::inc(x_473);
lean::dec(x_206);
x_476 = l_lean_elaborator_to__pexpr___main___closed__27;
x_477 = l_option_map___rarg(x_476, x_473);
x_478 = l_lean_elaborator_to__pexpr___main___closed__28;
x_479 = l_option_map___rarg(x_478, x_477);
x_480 = lean::box(0);
x_481 = l_option_get__or__else___main___rarg(x_479, x_480);
x_482 = l_lean_elaborator_to__pexpr___main___closed__29;
x_483 = l_lean_kvmap_set__name(x_472, x_482, x_481);
x_484 = l_list_append___rarg(x_386, x_459);
x_485 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_484);
x_486 = lean_expr_mk_mdata(x_483, x_485);
x_487 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_487, 0, x_486);
lean::cnstr_set(x_487, 1, x_461);
x_14 = x_487;
goto lbl_15;
}
}
}
}
else
{
obj* x_488; obj* x_490; 
x_488 = lean::cnstr_get(x_216, 1);
if (lean::is_exclusive(x_216)) {
 lean::cnstr_release(x_216, 0);
 lean::cnstr_set(x_216, 1, lean::box(0));
 x_490 = x_216;
} else {
 lean::inc(x_488);
 lean::dec(x_216);
 x_490 = lean::box(0);
}
if (lean::obj_tag(x_488) == 0)
{
obj* x_492; obj* x_497; 
lean::dec(x_335);
x_492 = lean::cnstr_get(x_215, 0);
lean::inc(x_492);
lean::dec(x_215);
lean::inc(x_1);
lean::inc(x_0);
x_497 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_210, x_1, x_2);
if (lean::obj_tag(x_497) == 0)
{
obj* x_504; obj* x_506; obj* x_507; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_490);
lean::dec(x_492);
x_504 = lean::cnstr_get(x_497, 0);
if (lean::is_exclusive(x_497)) {
 x_506 = x_497;
} else {
 lean::inc(x_504);
 lean::dec(x_497);
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
obj* x_508; obj* x_511; obj* x_513; obj* x_516; obj* x_520; 
x_508 = lean::cnstr_get(x_497, 0);
lean::inc(x_508);
lean::dec(x_497);
x_511 = lean::cnstr_get(x_508, 0);
lean::inc(x_511);
x_513 = lean::cnstr_get(x_508, 1);
lean::inc(x_513);
lean::dec(x_508);
lean::inc(x_1);
lean::inc(x_0);
x_520 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_492, x_1, x_513);
if (lean::obj_tag(x_520) == 0)
{
obj* x_527; obj* x_529; obj* x_530; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_511);
lean::dec(x_490);
x_527 = lean::cnstr_get(x_520, 0);
if (lean::is_exclusive(x_520)) {
 x_529 = x_520;
} else {
 lean::inc(x_527);
 lean::dec(x_520);
 x_529 = lean::box(0);
}
if (lean::is_scalar(x_529)) {
 x_530 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_530 = x_529;
}
lean::cnstr_set(x_530, 0, x_527);
return x_530;
}
else
{
obj* x_531; 
x_531 = lean::cnstr_get(x_206, 2);
lean::inc(x_531);
if (lean::obj_tag(x_531) == 0)
{
obj* x_534; obj* x_537; obj* x_539; obj* x_542; 
lean::dec(x_490);
x_534 = lean::cnstr_get(x_520, 0);
lean::inc(x_534);
lean::dec(x_520);
x_537 = lean::cnstr_get(x_534, 0);
lean::inc(x_537);
x_539 = lean::cnstr_get(x_534, 1);
lean::inc(x_539);
lean::dec(x_534);
x_542 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_542, 0, x_537);
lean::cnstr_set(x_542, 1, x_539);
x_516 = x_542;
goto lbl_517;
}
else
{
obj* x_543; obj* x_546; obj* x_548; obj* x_551; obj* x_554; obj* x_558; 
x_543 = lean::cnstr_get(x_520, 0);
lean::inc(x_543);
lean::dec(x_520);
x_546 = lean::cnstr_get(x_543, 0);
lean::inc(x_546);
x_548 = lean::cnstr_get(x_543, 1);
lean::inc(x_548);
lean::dec(x_543);
x_551 = lean::cnstr_get(x_531, 0);
lean::inc(x_551);
lean::dec(x_531);
x_554 = lean::cnstr_get(x_551, 0);
lean::inc(x_554);
lean::dec(x_551);
lean::inc(x_1);
x_558 = l_lean_elaborator_to__pexpr___main(x_554, x_1, x_548);
if (lean::obj_tag(x_558) == 0)
{
obj* x_566; obj* x_568; obj* x_569; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_511);
lean::dec(x_546);
lean::dec(x_490);
x_566 = lean::cnstr_get(x_558, 0);
if (lean::is_exclusive(x_558)) {
 x_568 = x_558;
} else {
 lean::inc(x_566);
 lean::dec(x_558);
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
obj* x_570; obj* x_573; obj* x_575; obj* x_578; obj* x_579; obj* x_580; obj* x_581; 
x_570 = lean::cnstr_get(x_558, 0);
lean::inc(x_570);
lean::dec(x_558);
x_573 = lean::cnstr_get(x_570, 0);
lean::inc(x_573);
x_575 = lean::cnstr_get(x_570, 1);
lean::inc(x_575);
lean::dec(x_570);
x_578 = lean::box(0);
if (lean::is_scalar(x_490)) {
 x_579 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_579 = x_490;
}
lean::cnstr_set(x_579, 0, x_573);
lean::cnstr_set(x_579, 1, x_578);
x_580 = l_list_append___rarg(x_546, x_579);
x_581 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_581, 0, x_580);
lean::cnstr_set(x_581, 1, x_575);
x_516 = x_581;
goto lbl_517;
}
}
}
lbl_517:
{
obj* x_582; obj* x_584; obj* x_587; obj* x_588; obj* x_590; obj* x_591; obj* x_592; obj* x_593; uint8 x_594; obj* x_595; obj* x_596; obj* x_599; obj* x_600; obj* x_601; obj* x_602; obj* x_603; obj* x_604; obj* x_605; obj* x_606; obj* x_607; obj* x_608; obj* x_609; obj* x_610; 
x_582 = lean::cnstr_get(x_516, 0);
lean::inc(x_582);
x_584 = lean::cnstr_get(x_516, 1);
lean::inc(x_584);
lean::dec(x_516);
x_587 = lean::box(0);
x_588 = lean::mk_nat_obj(0u);
lean::inc(x_511);
x_590 = l_list_length__aux___main___rarg(x_511, x_588);
x_591 = l_lean_elaborator_to__pexpr___main___closed__25;
x_592 = l_lean_kvmap_set__nat(x_587, x_591, x_590);
x_593 = l_lean_elaborator_to__pexpr___main___closed__26;
x_594 = 1;
x_595 = l_lean_kvmap_set__bool(x_592, x_593, x_594);
x_596 = lean::cnstr_get(x_206, 1);
lean::inc(x_596);
lean::dec(x_206);
x_599 = l_lean_elaborator_to__pexpr___main___closed__27;
x_600 = l_option_map___rarg(x_599, x_596);
x_601 = l_lean_elaborator_to__pexpr___main___closed__28;
x_602 = l_option_map___rarg(x_601, x_600);
x_603 = lean::box(0);
x_604 = l_option_get__or__else___main___rarg(x_602, x_603);
x_605 = l_lean_elaborator_to__pexpr___main___closed__29;
x_606 = l_lean_kvmap_set__name(x_595, x_605, x_604);
x_607 = l_list_append___rarg(x_511, x_582);
x_608 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_607);
x_609 = lean_expr_mk_mdata(x_606, x_608);
x_610 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_610, 0, x_609);
lean::cnstr_set(x_610, 1, x_584);
x_14 = x_610;
goto lbl_15;
}
}
}
else
{
obj* x_612; obj* x_613; obj* x_616; obj* x_617; obj* x_620; obj* x_621; obj* x_623; 
lean::dec(x_490);
if (lean::is_exclusive(x_488)) {
 lean::cnstr_release(x_488, 0);
 lean::cnstr_release(x_488, 1);
 x_612 = x_488;
} else {
 lean::dec(x_488);
 x_612 = lean::box(0);
}
x_613 = lean::cnstr_get(x_215, 0);
lean::inc(x_613);
lean::dec(x_215);
x_616 = l_lean_parser_term_struct__inst__item_has__view;
x_617 = lean::cnstr_get(x_616, 1);
lean::inc(x_617);
lean::dec(x_616);
x_620 = lean::apply_1(x_617, x_335);
x_621 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
x_623 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_620, x_621, x_1, x_2);
if (lean::obj_tag(x_623) == 0)
{
obj* x_631; obj* x_633; obj* x_634; 
lean::dec(x_612);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_613);
lean::dec(x_210);
lean::dec(x_206);
x_631 = lean::cnstr_get(x_623, 0);
if (lean::is_exclusive(x_623)) {
 x_633 = x_623;
} else {
 lean::inc(x_631);
 lean::dec(x_623);
 x_633 = lean::box(0);
}
if (lean::is_scalar(x_633)) {
 x_634 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_634 = x_633;
}
lean::cnstr_set(x_634, 0, x_631);
return x_634;
}
else
{
obj* x_635; obj* x_638; obj* x_640; obj* x_645; 
x_635 = lean::cnstr_get(x_623, 0);
lean::inc(x_635);
lean::dec(x_623);
x_638 = lean::cnstr_get(x_635, 0);
lean::inc(x_638);
x_640 = lean::cnstr_get(x_635, 1);
lean::inc(x_640);
lean::dec(x_635);
lean::inc(x_1);
lean::inc(x_0);
x_645 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_210, x_1, x_640);
if (lean::obj_tag(x_645) == 0)
{
obj* x_653; obj* x_655; obj* x_656; 
lean::dec(x_638);
lean::dec(x_612);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_613);
lean::dec(x_206);
x_653 = lean::cnstr_get(x_645, 0);
if (lean::is_exclusive(x_645)) {
 x_655 = x_645;
} else {
 lean::inc(x_653);
 lean::dec(x_645);
 x_655 = lean::box(0);
}
if (lean::is_scalar(x_655)) {
 x_656 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_656 = x_655;
}
lean::cnstr_set(x_656, 0, x_653);
return x_656;
}
else
{
obj* x_657; obj* x_660; obj* x_662; obj* x_665; obj* x_669; 
x_657 = lean::cnstr_get(x_645, 0);
lean::inc(x_657);
lean::dec(x_645);
x_660 = lean::cnstr_get(x_657, 0);
lean::inc(x_660);
x_662 = lean::cnstr_get(x_657, 1);
lean::inc(x_662);
lean::dec(x_657);
lean::inc(x_1);
lean::inc(x_0);
x_669 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_613, x_1, x_662);
if (lean::obj_tag(x_669) == 0)
{
obj* x_677; obj* x_679; obj* x_680; 
lean::dec(x_638);
lean::dec(x_612);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_660);
x_677 = lean::cnstr_get(x_669, 0);
if (lean::is_exclusive(x_669)) {
 x_679 = x_669;
} else {
 lean::inc(x_677);
 lean::dec(x_669);
 x_679 = lean::box(0);
}
if (lean::is_scalar(x_679)) {
 x_680 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_680 = x_679;
}
lean::cnstr_set(x_680, 0, x_677);
return x_680;
}
else
{
obj* x_681; 
x_681 = lean::cnstr_get(x_206, 2);
lean::inc(x_681);
if (lean::obj_tag(x_681) == 0)
{
obj* x_684; obj* x_687; obj* x_689; obj* x_692; 
lean::dec(x_612);
x_684 = lean::cnstr_get(x_669, 0);
lean::inc(x_684);
lean::dec(x_669);
x_687 = lean::cnstr_get(x_684, 0);
lean::inc(x_687);
x_689 = lean::cnstr_get(x_684, 1);
lean::inc(x_689);
lean::dec(x_684);
x_692 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_692, 0, x_687);
lean::cnstr_set(x_692, 1, x_689);
x_665 = x_692;
goto lbl_666;
}
else
{
obj* x_693; obj* x_696; obj* x_698; obj* x_701; obj* x_704; obj* x_708; 
x_693 = lean::cnstr_get(x_669, 0);
lean::inc(x_693);
lean::dec(x_669);
x_696 = lean::cnstr_get(x_693, 0);
lean::inc(x_696);
x_698 = lean::cnstr_get(x_693, 1);
lean::inc(x_698);
lean::dec(x_693);
x_701 = lean::cnstr_get(x_681, 0);
lean::inc(x_701);
lean::dec(x_681);
x_704 = lean::cnstr_get(x_701, 0);
lean::inc(x_704);
lean::dec(x_701);
lean::inc(x_1);
x_708 = l_lean_elaborator_to__pexpr___main(x_704, x_1, x_698);
if (lean::obj_tag(x_708) == 0)
{
obj* x_717; obj* x_719; obj* x_720; 
lean::dec(x_638);
lean::dec(x_612);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_206);
lean::dec(x_696);
lean::dec(x_660);
x_717 = lean::cnstr_get(x_708, 0);
if (lean::is_exclusive(x_708)) {
 x_719 = x_708;
} else {
 lean::inc(x_717);
 lean::dec(x_708);
 x_719 = lean::box(0);
}
if (lean::is_scalar(x_719)) {
 x_720 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_720 = x_719;
}
lean::cnstr_set(x_720, 0, x_717);
return x_720;
}
else
{
obj* x_721; obj* x_724; obj* x_726; obj* x_729; obj* x_730; obj* x_731; obj* x_732; 
x_721 = lean::cnstr_get(x_708, 0);
lean::inc(x_721);
lean::dec(x_708);
x_724 = lean::cnstr_get(x_721, 0);
lean::inc(x_724);
x_726 = lean::cnstr_get(x_721, 1);
lean::inc(x_726);
lean::dec(x_721);
x_729 = lean::box(0);
if (lean::is_scalar(x_612)) {
 x_730 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_730 = x_612;
}
lean::cnstr_set(x_730, 0, x_724);
lean::cnstr_set(x_730, 1, x_729);
x_731 = l_list_append___rarg(x_696, x_730);
x_732 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_732, 0, x_731);
lean::cnstr_set(x_732, 1, x_726);
x_665 = x_732;
goto lbl_666;
}
}
}
lbl_666:
{
obj* x_733; obj* x_735; obj* x_738; obj* x_739; obj* x_741; obj* x_742; obj* x_743; obj* x_744; uint8 x_745; obj* x_746; obj* x_747; obj* x_750; obj* x_751; obj* x_752; obj* x_753; obj* x_754; obj* x_755; obj* x_756; obj* x_757; obj* x_758; obj* x_759; obj* x_760; obj* x_761; 
x_733 = lean::cnstr_get(x_665, 0);
lean::inc(x_733);
x_735 = lean::cnstr_get(x_665, 1);
lean::inc(x_735);
lean::dec(x_665);
x_738 = lean::box(0);
x_739 = lean::mk_nat_obj(0u);
lean::inc(x_660);
x_741 = l_list_length__aux___main___rarg(x_660, x_739);
x_742 = l_lean_elaborator_to__pexpr___main___closed__25;
x_743 = l_lean_kvmap_set__nat(x_738, x_742, x_741);
x_744 = l_lean_elaborator_to__pexpr___main___closed__26;
x_745 = lean::unbox(x_638);
x_746 = l_lean_kvmap_set__bool(x_743, x_744, x_745);
x_747 = lean::cnstr_get(x_206, 1);
lean::inc(x_747);
lean::dec(x_206);
x_750 = l_lean_elaborator_to__pexpr___main___closed__27;
x_751 = l_option_map___rarg(x_750, x_747);
x_752 = l_lean_elaborator_to__pexpr___main___closed__28;
x_753 = l_option_map___rarg(x_752, x_751);
x_754 = lean::box(0);
x_755 = l_option_get__or__else___main___rarg(x_753, x_754);
x_756 = l_lean_elaborator_to__pexpr___main___closed__29;
x_757 = l_lean_kvmap_set__name(x_746, x_756, x_755);
x_758 = l_list_append___rarg(x_660, x_733);
x_759 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_758);
x_760 = lean_expr_mk_mdata(x_757, x_759);
x_761 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_761, 0, x_760);
lean::cnstr_set(x_761, 1, x_735);
x_14 = x_761;
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
obj* x_764; 
lean::inc(x_1);
lean::inc(x_9);
x_764 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_9, x_1, x_2);
if (lean::obj_tag(x_764) == 0)
{
obj* x_769; obj* x_771; obj* x_772; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_769 = lean::cnstr_get(x_764, 0);
if (lean::is_exclusive(x_764)) {
 x_771 = x_764;
} else {
 lean::inc(x_769);
 lean::dec(x_764);
 x_771 = lean::box(0);
}
if (lean::is_scalar(x_771)) {
 x_772 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_772 = x_771;
}
lean::cnstr_set(x_772, 0, x_769);
return x_772;
}
else
{
obj* x_773; obj* x_776; obj* x_778; obj* x_781; obj* x_782; 
x_773 = lean::cnstr_get(x_764, 0);
lean::inc(x_773);
lean::dec(x_764);
x_776 = lean::cnstr_get(x_773, 0);
lean::inc(x_776);
x_778 = lean::cnstr_get(x_773, 1);
lean::inc(x_778);
lean::dec(x_773);
x_781 = l_list_reverse___rarg(x_776);
x_782 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_782, 0, x_781);
lean::cnstr_set(x_782, 1, x_778);
x_16 = x_782;
goto lbl_17;
}
}
}
else
{
obj* x_785; obj* x_786; obj* x_790; obj* x_791; obj* x_792; obj* x_793; obj* x_794; obj* x_795; 
lean::dec(x_9);
lean::dec(x_7);
x_785 = l_lean_parser_string__lit_has__view;
x_786 = lean::cnstr_get(x_785, 0);
lean::inc(x_786);
lean::dec(x_785);
lean::inc(x_0);
x_790 = lean::apply_1(x_786, x_0);
x_791 = l_lean_parser_string__lit_view_value(x_790);
x_792 = l_lean_elaborator_to__pexpr___main___closed__31;
x_793 = l_option_get__or__else___main___rarg(x_791, x_792);
x_794 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_794, 0, x_793);
x_795 = lean_expr_mk_lit(x_794);
if (x_21 == 0)
{
obj* x_796; 
x_796 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_796) == 0)
{
obj* x_798; obj* x_799; 
lean::dec(x_1);
x_798 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_798, 0, x_795);
lean::cnstr_set(x_798, 1, x_2);
x_799 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_799, 0, x_798);
return x_799;
}
else
{
obj* x_800; obj* x_803; obj* x_806; obj* x_809; obj* x_810; obj* x_811; obj* x_813; obj* x_814; obj* x_815; obj* x_818; obj* x_819; obj* x_820; obj* x_821; obj* x_822; 
x_800 = lean::cnstr_get(x_796, 0);
lean::inc(x_800);
lean::dec(x_796);
x_803 = lean::cnstr_get(x_1, 0);
lean::inc(x_803);
lean::dec(x_1);
x_806 = lean::cnstr_get(x_803, 2);
lean::inc(x_806);
lean::dec(x_803);
x_809 = l_lean_file__map_to__position(x_806, x_800);
x_810 = lean::box(0);
x_811 = lean::cnstr_get(x_809, 1);
lean::inc(x_811);
x_813 = l_lean_elaborator_to__pexpr___main___closed__3;
x_814 = l_lean_kvmap_set__nat(x_810, x_813, x_811);
x_815 = lean::cnstr_get(x_809, 0);
lean::inc(x_815);
lean::dec(x_809);
x_818 = l_lean_elaborator_to__pexpr___main___closed__4;
x_819 = l_lean_kvmap_set__nat(x_814, x_818, x_815);
x_820 = lean_expr_mk_mdata(x_819, x_795);
x_821 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_821, 0, x_820);
lean::cnstr_set(x_821, 1, x_2);
x_822 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_822, 0, x_821);
return x_822;
}
}
else
{
obj* x_825; obj* x_826; 
lean::dec(x_1);
lean::dec(x_0);
x_825 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_825, 0, x_795);
lean::cnstr_set(x_825, 1, x_2);
x_826 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_826, 0, x_825);
return x_826;
}
}
}
else
{
obj* x_829; obj* x_830; obj* x_834; obj* x_835; obj* x_836; obj* x_837; 
lean::dec(x_9);
lean::dec(x_7);
x_829 = l_lean_parser_number_has__view;
x_830 = lean::cnstr_get(x_829, 0);
lean::inc(x_830);
lean::dec(x_829);
lean::inc(x_0);
x_834 = lean::apply_1(x_830, x_0);
x_835 = l_lean_parser_number_view_to__nat___main(x_834);
x_836 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_836, 0, x_835);
x_837 = lean_expr_mk_lit(x_836);
if (x_21 == 0)
{
obj* x_838; 
x_838 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_838) == 0)
{
obj* x_840; obj* x_841; 
lean::dec(x_1);
x_840 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_840, 0, x_837);
lean::cnstr_set(x_840, 1, x_2);
x_841 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_841, 0, x_840);
return x_841;
}
else
{
obj* x_842; obj* x_845; obj* x_848; obj* x_851; obj* x_852; obj* x_853; obj* x_855; obj* x_856; obj* x_857; obj* x_860; obj* x_861; obj* x_862; obj* x_863; obj* x_864; 
x_842 = lean::cnstr_get(x_838, 0);
lean::inc(x_842);
lean::dec(x_838);
x_845 = lean::cnstr_get(x_1, 0);
lean::inc(x_845);
lean::dec(x_1);
x_848 = lean::cnstr_get(x_845, 2);
lean::inc(x_848);
lean::dec(x_845);
x_851 = l_lean_file__map_to__position(x_848, x_842);
x_852 = lean::box(0);
x_853 = lean::cnstr_get(x_851, 1);
lean::inc(x_853);
x_855 = l_lean_elaborator_to__pexpr___main___closed__3;
x_856 = l_lean_kvmap_set__nat(x_852, x_855, x_853);
x_857 = lean::cnstr_get(x_851, 0);
lean::inc(x_857);
lean::dec(x_851);
x_860 = l_lean_elaborator_to__pexpr___main___closed__4;
x_861 = l_lean_kvmap_set__nat(x_856, x_860, x_857);
x_862 = lean_expr_mk_mdata(x_861, x_837);
x_863 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_863, 0, x_862);
lean::cnstr_set(x_863, 1, x_2);
x_864 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_864, 0, x_863);
return x_864;
}
}
else
{
obj* x_867; obj* x_868; 
lean::dec(x_1);
lean::dec(x_0);
x_867 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_867, 0, x_837);
lean::cnstr_set(x_867, 1, x_2);
x_868 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_868, 0, x_867);
return x_868;
}
}
}
else
{
obj* x_870; obj* x_871; obj* x_875; obj* x_876; obj* x_880; 
lean::dec(x_9);
x_870 = l_lean_parser_term_borrowed_has__view;
x_871 = lean::cnstr_get(x_870, 0);
lean::inc(x_871);
lean::dec(x_870);
lean::inc(x_0);
x_875 = lean::apply_1(x_871, x_0);
x_876 = lean::cnstr_get(x_875, 1);
lean::inc(x_876);
lean::dec(x_875);
lean::inc(x_1);
x_880 = l_lean_elaborator_to__pexpr___main(x_876, x_1, x_2);
if (lean::obj_tag(x_880) == 0)
{
obj* x_884; obj* x_886; obj* x_887; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_884 = lean::cnstr_get(x_880, 0);
if (lean::is_exclusive(x_880)) {
 x_886 = x_880;
} else {
 lean::inc(x_884);
 lean::dec(x_880);
 x_886 = lean::box(0);
}
if (lean::is_scalar(x_886)) {
 x_887 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_887 = x_886;
}
lean::cnstr_set(x_887, 0, x_884);
return x_887;
}
else
{
obj* x_888; obj* x_891; obj* x_893; obj* x_896; obj* x_897; obj* x_898; 
x_888 = lean::cnstr_get(x_880, 0);
lean::inc(x_888);
lean::dec(x_880);
x_891 = lean::cnstr_get(x_888, 0);
lean::inc(x_891);
x_893 = lean::cnstr_get(x_888, 1);
lean::inc(x_893);
lean::dec(x_888);
x_896 = l_lean_elaborator_to__pexpr___main___closed__32;
x_897 = l_lean_elaborator_expr_mk__annotation(x_896, x_891);
x_898 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_898, 0, x_897);
lean::cnstr_set(x_898, 1, x_893);
x_14 = x_898;
goto lbl_15;
}
}
}
else
{
obj* x_900; obj* x_901; obj* x_905; obj* x_906; obj* x_910; 
lean::dec(x_9);
x_900 = l_lean_parser_term_inaccessible_has__view;
x_901 = lean::cnstr_get(x_900, 0);
lean::inc(x_901);
lean::dec(x_900);
lean::inc(x_0);
x_905 = lean::apply_1(x_901, x_0);
x_906 = lean::cnstr_get(x_905, 1);
lean::inc(x_906);
lean::dec(x_905);
lean::inc(x_1);
x_910 = l_lean_elaborator_to__pexpr___main(x_906, x_1, x_2);
if (lean::obj_tag(x_910) == 0)
{
obj* x_914; obj* x_916; obj* x_917; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_914 = lean::cnstr_get(x_910, 0);
if (lean::is_exclusive(x_910)) {
 x_916 = x_910;
} else {
 lean::inc(x_914);
 lean::dec(x_910);
 x_916 = lean::box(0);
}
if (lean::is_scalar(x_916)) {
 x_917 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_917 = x_916;
}
lean::cnstr_set(x_917, 0, x_914);
return x_917;
}
else
{
obj* x_918; obj* x_921; obj* x_923; obj* x_926; obj* x_927; obj* x_928; 
x_918 = lean::cnstr_get(x_910, 0);
lean::inc(x_918);
lean::dec(x_910);
x_921 = lean::cnstr_get(x_918, 0);
lean::inc(x_921);
x_923 = lean::cnstr_get(x_918, 1);
lean::inc(x_923);
lean::dec(x_918);
x_926 = l_lean_elaborator_to__pexpr___main___closed__33;
x_927 = l_lean_elaborator_expr_mk__annotation(x_926, x_921);
x_928 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_928, 0, x_927);
lean::cnstr_set(x_928, 1, x_923);
x_14 = x_928;
goto lbl_15;
}
}
}
else
{
obj* x_930; obj* x_931; obj* x_935; obj* x_936; obj* x_938; obj* x_939; obj* x_942; obj* x_945; 
lean::dec(x_9);
x_930 = l_lean_parser_term_explicit_has__view;
x_931 = lean::cnstr_get(x_930, 0);
lean::inc(x_931);
lean::dec(x_930);
lean::inc(x_0);
x_935 = lean::apply_1(x_931, x_0);
x_936 = lean::cnstr_get(x_935, 0);
lean::inc(x_936);
x_938 = l_lean_parser_ident__univs_has__view;
x_939 = lean::cnstr_get(x_938, 1);
lean::inc(x_939);
lean::dec(x_938);
x_942 = lean::cnstr_get(x_935, 1);
lean::inc(x_942);
lean::dec(x_935);
x_945 = lean::apply_1(x_939, x_942);
if (lean::obj_tag(x_936) == 0)
{
obj* x_948; 
lean::dec(x_936);
lean::inc(x_1);
x_948 = l_lean_elaborator_to__pexpr___main(x_945, x_1, x_2);
if (lean::obj_tag(x_948) == 0)
{
obj* x_952; obj* x_954; obj* x_955; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_952 = lean::cnstr_get(x_948, 0);
if (lean::is_exclusive(x_948)) {
 x_954 = x_948;
} else {
 lean::inc(x_952);
 lean::dec(x_948);
 x_954 = lean::box(0);
}
if (lean::is_scalar(x_954)) {
 x_955 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_955 = x_954;
}
lean::cnstr_set(x_955, 0, x_952);
return x_955;
}
else
{
obj* x_956; obj* x_959; obj* x_961; obj* x_964; obj* x_965; obj* x_966; 
x_956 = lean::cnstr_get(x_948, 0);
lean::inc(x_956);
lean::dec(x_948);
x_959 = lean::cnstr_get(x_956, 0);
lean::inc(x_959);
x_961 = lean::cnstr_get(x_956, 1);
lean::inc(x_961);
lean::dec(x_956);
x_964 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
x_965 = l_lean_elaborator_expr_mk__annotation(x_964, x_959);
x_966 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_966, 0, x_965);
lean::cnstr_set(x_966, 1, x_961);
x_14 = x_966;
goto lbl_15;
}
}
else
{
obj* x_969; 
lean::dec(x_936);
lean::inc(x_1);
x_969 = l_lean_elaborator_to__pexpr___main(x_945, x_1, x_2);
if (lean::obj_tag(x_969) == 0)
{
obj* x_973; obj* x_975; obj* x_976; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_973 = lean::cnstr_get(x_969, 0);
if (lean::is_exclusive(x_969)) {
 x_975 = x_969;
} else {
 lean::inc(x_973);
 lean::dec(x_969);
 x_975 = lean::box(0);
}
if (lean::is_scalar(x_975)) {
 x_976 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_976 = x_975;
}
lean::cnstr_set(x_976, 0, x_973);
return x_976;
}
else
{
obj* x_977; obj* x_980; obj* x_982; obj* x_985; obj* x_986; obj* x_987; 
x_977 = lean::cnstr_get(x_969, 0);
lean::inc(x_977);
lean::dec(x_969);
x_980 = lean::cnstr_get(x_977, 0);
lean::inc(x_980);
x_982 = lean::cnstr_get(x_977, 1);
lean::inc(x_982);
lean::dec(x_977);
x_985 = l_lean_elaborator_to__pexpr___main___closed__34;
x_986 = l_lean_elaborator_expr_mk__annotation(x_985, x_980);
x_987 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_987, 0, x_986);
lean::cnstr_set(x_987, 1, x_982);
x_14 = x_987;
goto lbl_15;
}
}
}
}
else
{
obj* x_989; obj* x_990; obj* x_994; obj* x_995; 
lean::dec(x_9);
x_989 = l_lean_parser_term_projection_has__view;
x_990 = lean::cnstr_get(x_989, 0);
lean::inc(x_990);
lean::dec(x_989);
lean::inc(x_0);
x_994 = lean::apply_1(x_990, x_0);
x_995 = lean::cnstr_get(x_994, 2);
lean::inc(x_995);
if (lean::obj_tag(x_995) == 0)
{
obj* x_997; obj* x_1000; obj* x_1004; 
x_997 = lean::cnstr_get(x_994, 0);
lean::inc(x_997);
lean::dec(x_994);
x_1000 = lean::cnstr_get(x_995, 0);
lean::inc(x_1000);
lean::dec(x_995);
lean::inc(x_1);
x_1004 = l_lean_elaborator_to__pexpr___main(x_997, x_1, x_2);
if (lean::obj_tag(x_1004) == 0)
{
obj* x_1009; obj* x_1011; obj* x_1012; 
lean::dec(x_1000);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1009 = lean::cnstr_get(x_1004, 0);
if (lean::is_exclusive(x_1004)) {
 x_1011 = x_1004;
} else {
 lean::inc(x_1009);
 lean::dec(x_1004);
 x_1011 = lean::box(0);
}
if (lean::is_scalar(x_1011)) {
 x_1012 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1012 = x_1011;
}
lean::cnstr_set(x_1012, 0, x_1009);
return x_1012;
}
else
{
obj* x_1013; obj* x_1016; obj* x_1018; obj* x_1021; obj* x_1024; obj* x_1025; obj* x_1026; obj* x_1027; obj* x_1028; obj* x_1029; 
x_1013 = lean::cnstr_get(x_1004, 0);
lean::inc(x_1013);
lean::dec(x_1004);
x_1016 = lean::cnstr_get(x_1013, 0);
lean::inc(x_1016);
x_1018 = lean::cnstr_get(x_1013, 1);
lean::inc(x_1018);
lean::dec(x_1013);
x_1021 = lean::cnstr_get(x_1000, 2);
lean::inc(x_1021);
lean::dec(x_1000);
x_1024 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1024, 0, x_1021);
x_1025 = lean::box(0);
x_1026 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1027 = l_lean_kvmap_insert__core___main(x_1025, x_1026, x_1024);
x_1028 = lean_expr_mk_mdata(x_1027, x_1016);
x_1029 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1029, 0, x_1028);
lean::cnstr_set(x_1029, 1, x_1018);
x_14 = x_1029;
goto lbl_15;
}
}
else
{
obj* x_1030; obj* x_1033; obj* x_1037; 
x_1030 = lean::cnstr_get(x_994, 0);
lean::inc(x_1030);
lean::dec(x_994);
x_1033 = lean::cnstr_get(x_995, 0);
lean::inc(x_1033);
lean::dec(x_995);
lean::inc(x_1);
x_1037 = l_lean_elaborator_to__pexpr___main(x_1030, x_1, x_2);
if (lean::obj_tag(x_1037) == 0)
{
obj* x_1042; obj* x_1044; obj* x_1045; 
lean::dec(x_1033);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1042 = lean::cnstr_get(x_1037, 0);
if (lean::is_exclusive(x_1037)) {
 x_1044 = x_1037;
} else {
 lean::inc(x_1042);
 lean::dec(x_1037);
 x_1044 = lean::box(0);
}
if (lean::is_scalar(x_1044)) {
 x_1045 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1045 = x_1044;
}
lean::cnstr_set(x_1045, 0, x_1042);
return x_1045;
}
else
{
obj* x_1046; obj* x_1049; obj* x_1051; obj* x_1054; obj* x_1055; obj* x_1056; obj* x_1057; obj* x_1058; obj* x_1059; obj* x_1060; 
x_1046 = lean::cnstr_get(x_1037, 0);
lean::inc(x_1046);
lean::dec(x_1037);
x_1049 = lean::cnstr_get(x_1046, 0);
lean::inc(x_1049);
x_1051 = lean::cnstr_get(x_1046, 1);
lean::inc(x_1051);
lean::dec(x_1046);
x_1054 = l_lean_parser_number_view_to__nat___main(x_1033);
x_1055 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1055, 0, x_1054);
x_1056 = lean::box(0);
x_1057 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1058 = l_lean_kvmap_insert__core___main(x_1056, x_1057, x_1055);
x_1059 = lean_expr_mk_mdata(x_1058, x_1049);
x_1060 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1060, 0, x_1059);
lean::cnstr_set(x_1060, 1, x_1051);
x_14 = x_1060;
goto lbl_15;
}
}
}
}
else
{
obj* x_1062; obj* x_1063; obj* x_1067; obj* x_1068; 
lean::dec(x_9);
x_1062 = l_lean_parser_term_let_has__view;
x_1063 = lean::cnstr_get(x_1062, 0);
lean::inc(x_1063);
lean::dec(x_1062);
lean::inc(x_0);
x_1067 = lean::apply_1(x_1063, x_0);
x_1068 = lean::cnstr_get(x_1067, 1);
lean::inc(x_1068);
if (lean::obj_tag(x_1068) == 0)
{
obj* x_1070; obj* x_1073; 
x_1070 = lean::cnstr_get(x_1068, 0);
lean::inc(x_1070);
lean::dec(x_1068);
x_1073 = lean::cnstr_get(x_1070, 1);
lean::inc(x_1073);
if (lean::obj_tag(x_1073) == 0)
{
obj* x_1075; 
x_1075 = lean::cnstr_get(x_1070, 2);
lean::inc(x_1075);
if (lean::obj_tag(x_1075) == 0)
{
obj* x_1079; obj* x_1082; 
lean::dec(x_1067);
lean::dec(x_1070);
x_1079 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_0);
x_1082 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1079, x_1, x_2);
if (lean::obj_tag(x_1082) == 0)
{
obj* x_1086; obj* x_1088; obj* x_1089; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1086 = lean::cnstr_get(x_1082, 0);
if (lean::is_exclusive(x_1082)) {
 x_1088 = x_1082;
} else {
 lean::inc(x_1086);
 lean::dec(x_1082);
 x_1088 = lean::box(0);
}
if (lean::is_scalar(x_1088)) {
 x_1089 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1089 = x_1088;
}
lean::cnstr_set(x_1089, 0, x_1086);
return x_1089;
}
else
{
obj* x_1090; 
x_1090 = lean::cnstr_get(x_1082, 0);
lean::inc(x_1090);
lean::dec(x_1082);
x_14 = x_1090;
goto lbl_15;
}
}
else
{
obj* x_1093; obj* x_1096; obj* x_1099; obj* x_1103; 
x_1093 = lean::cnstr_get(x_1070, 0);
lean::inc(x_1093);
lean::dec(x_1070);
x_1096 = lean::cnstr_get(x_1075, 0);
lean::inc(x_1096);
lean::dec(x_1075);
x_1099 = lean::cnstr_get(x_1096, 1);
lean::inc(x_1099);
lean::dec(x_1096);
lean::inc(x_1);
x_1103 = l_lean_elaborator_to__pexpr___main(x_1099, x_1, x_2);
if (lean::obj_tag(x_1103) == 0)
{
obj* x_1109; obj* x_1111; obj* x_1112; 
lean::dec(x_1093);
lean::dec(x_1067);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1109 = lean::cnstr_get(x_1103, 0);
if (lean::is_exclusive(x_1103)) {
 x_1111 = x_1103;
} else {
 lean::inc(x_1109);
 lean::dec(x_1103);
 x_1111 = lean::box(0);
}
if (lean::is_scalar(x_1111)) {
 x_1112 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1112 = x_1111;
}
lean::cnstr_set(x_1112, 0, x_1109);
return x_1112;
}
else
{
obj* x_1113; obj* x_1116; obj* x_1118; obj* x_1121; obj* x_1124; 
x_1113 = lean::cnstr_get(x_1103, 0);
lean::inc(x_1113);
lean::dec(x_1103);
x_1116 = lean::cnstr_get(x_1113, 0);
lean::inc(x_1116);
x_1118 = lean::cnstr_get(x_1113, 1);
lean::inc(x_1118);
lean::dec(x_1113);
x_1121 = lean::cnstr_get(x_1067, 3);
lean::inc(x_1121);
lean::inc(x_1);
x_1124 = l_lean_elaborator_to__pexpr___main(x_1121, x_1, x_1118);
if (lean::obj_tag(x_1124) == 0)
{
obj* x_1131; obj* x_1133; obj* x_1134; 
lean::dec(x_1093);
lean::dec(x_1067);
lean::dec(x_1116);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1131 = lean::cnstr_get(x_1124, 0);
if (lean::is_exclusive(x_1124)) {
 x_1133 = x_1124;
} else {
 lean::inc(x_1131);
 lean::dec(x_1124);
 x_1133 = lean::box(0);
}
if (lean::is_scalar(x_1133)) {
 x_1134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1134 = x_1133;
}
lean::cnstr_set(x_1134, 0, x_1131);
return x_1134;
}
else
{
obj* x_1135; obj* x_1138; obj* x_1140; obj* x_1143; obj* x_1147; 
x_1135 = lean::cnstr_get(x_1124, 0);
lean::inc(x_1135);
lean::dec(x_1124);
x_1138 = lean::cnstr_get(x_1135, 0);
lean::inc(x_1138);
x_1140 = lean::cnstr_get(x_1135, 1);
lean::inc(x_1140);
lean::dec(x_1135);
x_1143 = lean::cnstr_get(x_1067, 5);
lean::inc(x_1143);
lean::dec(x_1067);
lean::inc(x_1);
x_1147 = l_lean_elaborator_to__pexpr___main(x_1143, x_1, x_1140);
if (lean::obj_tag(x_1147) == 0)
{
obj* x_1154; obj* x_1156; obj* x_1157; 
lean::dec(x_1093);
lean::dec(x_1116);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1138);
x_1154 = lean::cnstr_get(x_1147, 0);
if (lean::is_exclusive(x_1147)) {
 x_1156 = x_1147;
} else {
 lean::inc(x_1154);
 lean::dec(x_1147);
 x_1156 = lean::box(0);
}
if (lean::is_scalar(x_1156)) {
 x_1157 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1157 = x_1156;
}
lean::cnstr_set(x_1157, 0, x_1154);
return x_1157;
}
else
{
obj* x_1158; obj* x_1161; obj* x_1163; obj* x_1166; obj* x_1167; obj* x_1168; 
x_1158 = lean::cnstr_get(x_1147, 0);
lean::inc(x_1158);
lean::dec(x_1147);
x_1161 = lean::cnstr_get(x_1158, 0);
lean::inc(x_1161);
x_1163 = lean::cnstr_get(x_1158, 1);
lean::inc(x_1163);
lean::dec(x_1158);
x_1166 = l_lean_elaborator_mangle__ident(x_1093);
x_1167 = lean_expr_mk_let(x_1166, x_1116, x_1138, x_1161);
x_1168 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1168, 0, x_1167);
lean::cnstr_set(x_1168, 1, x_1163);
x_14 = x_1168;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1172; obj* x_1175; 
lean::dec(x_1073);
lean::dec(x_1067);
lean::dec(x_1070);
x_1172 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_0);
x_1175 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1172, x_1, x_2);
if (lean::obj_tag(x_1175) == 0)
{
obj* x_1179; obj* x_1181; obj* x_1182; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1179 = lean::cnstr_get(x_1175, 0);
if (lean::is_exclusive(x_1175)) {
 x_1181 = x_1175;
} else {
 lean::inc(x_1179);
 lean::dec(x_1175);
 x_1181 = lean::box(0);
}
if (lean::is_scalar(x_1181)) {
 x_1182 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1182 = x_1181;
}
lean::cnstr_set(x_1182, 0, x_1179);
return x_1182;
}
else
{
obj* x_1183; 
x_1183 = lean::cnstr_get(x_1175, 0);
lean::inc(x_1183);
lean::dec(x_1175);
x_14 = x_1183;
goto lbl_15;
}
}
}
else
{
obj* x_1188; obj* x_1191; 
lean::dec(x_1067);
lean::dec(x_1068);
x_1188 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
lean::inc(x_0);
x_1191 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1188, x_1, x_2);
if (lean::obj_tag(x_1191) == 0)
{
obj* x_1195; obj* x_1197; obj* x_1198; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1195 = lean::cnstr_get(x_1191, 0);
if (lean::is_exclusive(x_1191)) {
 x_1197 = x_1191;
} else {
 lean::inc(x_1195);
 lean::dec(x_1191);
 x_1197 = lean::box(0);
}
if (lean::is_scalar(x_1197)) {
 x_1198 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1198 = x_1197;
}
lean::cnstr_set(x_1198, 0, x_1195);
return x_1198;
}
else
{
obj* x_1199; 
x_1199 = lean::cnstr_get(x_1191, 0);
lean::inc(x_1199);
lean::dec(x_1191);
x_14 = x_1199;
goto lbl_15;
}
}
}
}
else
{
obj* x_1203; obj* x_1204; obj* x_1208; obj* x_1209; obj* x_1212; 
lean::dec(x_9);
x_1203 = l_lean_parser_term_show_has__view;
x_1204 = lean::cnstr_get(x_1203, 0);
lean::inc(x_1204);
lean::dec(x_1203);
lean::inc(x_0);
x_1208 = lean::apply_1(x_1204, x_0);
x_1209 = lean::cnstr_get(x_1208, 1);
lean::inc(x_1209);
lean::inc(x_1);
x_1212 = l_lean_elaborator_to__pexpr___main(x_1209, x_1, x_2);
if (lean::obj_tag(x_1212) == 0)
{
obj* x_1217; obj* x_1219; obj* x_1220; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1208);
x_1217 = lean::cnstr_get(x_1212, 0);
if (lean::is_exclusive(x_1212)) {
 x_1219 = x_1212;
} else {
 lean::inc(x_1217);
 lean::dec(x_1212);
 x_1219 = lean::box(0);
}
if (lean::is_scalar(x_1219)) {
 x_1220 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1220 = x_1219;
}
lean::cnstr_set(x_1220, 0, x_1217);
return x_1220;
}
else
{
obj* x_1221; obj* x_1224; obj* x_1226; obj* x_1229; obj* x_1232; obj* x_1236; 
x_1221 = lean::cnstr_get(x_1212, 0);
lean::inc(x_1221);
lean::dec(x_1212);
x_1224 = lean::cnstr_get(x_1221, 0);
lean::inc(x_1224);
x_1226 = lean::cnstr_get(x_1221, 1);
lean::inc(x_1226);
lean::dec(x_1221);
x_1229 = lean::cnstr_get(x_1208, 3);
lean::inc(x_1229);
lean::dec(x_1208);
x_1232 = lean::cnstr_get(x_1229, 1);
lean::inc(x_1232);
lean::dec(x_1229);
lean::inc(x_1);
x_1236 = l_lean_elaborator_to__pexpr___main(x_1232, x_1, x_1226);
if (lean::obj_tag(x_1236) == 0)
{
obj* x_1241; obj* x_1243; obj* x_1244; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1224);
x_1241 = lean::cnstr_get(x_1236, 0);
if (lean::is_exclusive(x_1236)) {
 x_1243 = x_1236;
} else {
 lean::inc(x_1241);
 lean::dec(x_1236);
 x_1243 = lean::box(0);
}
if (lean::is_scalar(x_1243)) {
 x_1244 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1244 = x_1243;
}
lean::cnstr_set(x_1244, 0, x_1241);
return x_1244;
}
else
{
obj* x_1245; obj* x_1248; obj* x_1250; obj* x_1253; uint8 x_1254; obj* x_1255; obj* x_1256; obj* x_1257; obj* x_1258; obj* x_1259; obj* x_1260; 
x_1245 = lean::cnstr_get(x_1236, 0);
lean::inc(x_1245);
lean::dec(x_1236);
x_1248 = lean::cnstr_get(x_1245, 0);
lean::inc(x_1248);
x_1250 = lean::cnstr_get(x_1245, 1);
lean::inc(x_1250);
lean::dec(x_1245);
x_1253 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1254 = 0;
x_1255 = l_lean_elaborator_to__pexpr___main___closed__38;
x_1256 = lean_expr_mk_lambda(x_1253, x_1254, x_1224, x_1255);
x_1257 = lean_expr_mk_app(x_1256, x_1248);
x_1258 = l_lean_elaborator_to__pexpr___main___closed__39;
x_1259 = l_lean_elaborator_expr_mk__annotation(x_1258, x_1257);
x_1260 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1260, 0, x_1259);
lean::cnstr_set(x_1260, 1, x_1250);
x_14 = x_1260;
goto lbl_15;
}
}
}
}
else
{
obj* x_1262; obj* x_1263; obj* x_1267; obj* x_1268; obj* x_1270; obj* x_1273; 
lean::dec(x_9);
x_1262 = l_lean_parser_term_have_has__view;
x_1263 = lean::cnstr_get(x_1262, 0);
lean::inc(x_1263);
lean::dec(x_1262);
lean::inc(x_0);
x_1267 = lean::apply_1(x_1263, x_0);
x_1270 = lean::cnstr_get(x_1267, 2);
lean::inc(x_1270);
lean::inc(x_1);
x_1273 = l_lean_elaborator_to__pexpr___main(x_1270, x_1, x_2);
if (lean::obj_tag(x_1273) == 0)
{
obj* x_1278; obj* x_1280; obj* x_1281; 
lean::dec(x_1267);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1278 = lean::cnstr_get(x_1273, 0);
if (lean::is_exclusive(x_1273)) {
 x_1280 = x_1273;
} else {
 lean::inc(x_1278);
 lean::dec(x_1273);
 x_1280 = lean::box(0);
}
if (lean::is_scalar(x_1280)) {
 x_1281 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1281 = x_1280;
}
lean::cnstr_set(x_1281, 0, x_1278);
return x_1281;
}
else
{
obj* x_1282; obj* x_1285; obj* x_1287; obj* x_1290; obj* x_1293; 
x_1282 = lean::cnstr_get(x_1273, 0);
lean::inc(x_1282);
lean::dec(x_1273);
x_1285 = lean::cnstr_get(x_1282, 0);
lean::inc(x_1285);
x_1287 = lean::cnstr_get(x_1282, 1);
lean::inc(x_1287);
lean::dec(x_1282);
x_1290 = lean::cnstr_get(x_1267, 5);
lean::inc(x_1290);
lean::inc(x_1);
x_1293 = l_lean_elaborator_to__pexpr___main(x_1290, x_1, x_1287);
if (lean::obj_tag(x_1293) == 0)
{
obj* x_1299; obj* x_1301; obj* x_1302; 
lean::dec(x_1285);
lean::dec(x_1267);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1299 = lean::cnstr_get(x_1293, 0);
if (lean::is_exclusive(x_1293)) {
 x_1301 = x_1293;
} else {
 lean::inc(x_1299);
 lean::dec(x_1293);
 x_1301 = lean::box(0);
}
if (lean::is_scalar(x_1301)) {
 x_1302 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1302 = x_1301;
}
lean::cnstr_set(x_1302, 0, x_1299);
return x_1302;
}
else
{
obj* x_1303; obj* x_1306; obj* x_1308; obj* x_1311; obj* x_1313; obj* x_1314; obj* x_1315; obj* x_1316; obj* x_1317; obj* x_1318; uint8 x_1319; obj* x_1320; obj* x_1321; 
x_1303 = lean::cnstr_get(x_1293, 0);
lean::inc(x_1303);
lean::dec(x_1293);
x_1306 = lean::cnstr_get(x_1303, 0);
lean::inc(x_1306);
x_1308 = lean::cnstr_get(x_1303, 1);
lean::inc(x_1308);
lean::dec(x_1303);
x_1311 = lean::cnstr_get(x_1267, 1);
lean::inc(x_1311);
x_1313 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1314 = l_option_map___rarg(x_1313, x_1311);
x_1315 = l_lean_elaborator_to__pexpr___main___closed__28;
x_1316 = l_option_map___rarg(x_1315, x_1314);
x_1317 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1318 = l_option_get__or__else___main___rarg(x_1316, x_1317);
x_1319 = 0;
x_1320 = lean_expr_mk_lambda(x_1318, x_1319, x_1285, x_1306);
x_1321 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1321, 0, x_1320);
lean::cnstr_set(x_1321, 1, x_1308);
x_1268 = x_1321;
goto lbl_1269;
}
}
lbl_1269:
{
obj* x_1322; 
x_1322 = lean::cnstr_get(x_1267, 3);
lean::inc(x_1322);
lean::dec(x_1267);
if (lean::obj_tag(x_1322) == 0)
{
obj* x_1325; obj* x_1327; obj* x_1330; obj* x_1333; obj* x_1337; 
x_1325 = lean::cnstr_get(x_1268, 0);
lean::inc(x_1325);
x_1327 = lean::cnstr_get(x_1268, 1);
lean::inc(x_1327);
lean::dec(x_1268);
x_1330 = lean::cnstr_get(x_1322, 0);
lean::inc(x_1330);
lean::dec(x_1322);
x_1333 = lean::cnstr_get(x_1330, 1);
lean::inc(x_1333);
lean::dec(x_1330);
lean::inc(x_1);
x_1337 = l_lean_elaborator_to__pexpr___main(x_1333, x_1, x_1327);
if (lean::obj_tag(x_1337) == 0)
{
obj* x_1342; obj* x_1344; obj* x_1345; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1325);
x_1342 = lean::cnstr_get(x_1337, 0);
if (lean::is_exclusive(x_1337)) {
 x_1344 = x_1337;
} else {
 lean::inc(x_1342);
 lean::dec(x_1337);
 x_1344 = lean::box(0);
}
if (lean::is_scalar(x_1344)) {
 x_1345 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1345 = x_1344;
}
lean::cnstr_set(x_1345, 0, x_1342);
return x_1345;
}
else
{
obj* x_1346; obj* x_1349; obj* x_1351; obj* x_1354; obj* x_1355; obj* x_1356; obj* x_1357; 
x_1346 = lean::cnstr_get(x_1337, 0);
lean::inc(x_1346);
lean::dec(x_1337);
x_1349 = lean::cnstr_get(x_1346, 0);
lean::inc(x_1349);
x_1351 = lean::cnstr_get(x_1346, 1);
lean::inc(x_1351);
lean::dec(x_1346);
x_1354 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1355 = l_lean_elaborator_expr_mk__annotation(x_1354, x_1325);
x_1356 = lean_expr_mk_app(x_1355, x_1349);
x_1357 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1357, 0, x_1356);
lean::cnstr_set(x_1357, 1, x_1351);
x_14 = x_1357;
goto lbl_15;
}
}
else
{
obj* x_1358; obj* x_1360; obj* x_1363; obj* x_1366; obj* x_1369; obj* x_1373; 
x_1358 = lean::cnstr_get(x_1268, 0);
lean::inc(x_1358);
x_1360 = lean::cnstr_get(x_1268, 1);
lean::inc(x_1360);
lean::dec(x_1268);
x_1363 = lean::cnstr_get(x_1322, 0);
lean::inc(x_1363);
lean::dec(x_1322);
x_1366 = lean::cnstr_get(x_1363, 1);
lean::inc(x_1366);
lean::dec(x_1363);
x_1369 = lean::cnstr_get(x_1366, 1);
lean::inc(x_1369);
lean::dec(x_1366);
lean::inc(x_1);
x_1373 = l_lean_elaborator_to__pexpr___main(x_1369, x_1, x_1360);
if (lean::obj_tag(x_1373) == 0)
{
obj* x_1378; obj* x_1380; obj* x_1381; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1358);
x_1378 = lean::cnstr_get(x_1373, 0);
if (lean::is_exclusive(x_1373)) {
 x_1380 = x_1373;
} else {
 lean::inc(x_1378);
 lean::dec(x_1373);
 x_1380 = lean::box(0);
}
if (lean::is_scalar(x_1380)) {
 x_1381 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1381 = x_1380;
}
lean::cnstr_set(x_1381, 0, x_1378);
return x_1381;
}
else
{
obj* x_1382; obj* x_1385; obj* x_1387; obj* x_1390; obj* x_1391; obj* x_1392; obj* x_1393; 
x_1382 = lean::cnstr_get(x_1373, 0);
lean::inc(x_1382);
lean::dec(x_1373);
x_1385 = lean::cnstr_get(x_1382, 0);
lean::inc(x_1385);
x_1387 = lean::cnstr_get(x_1382, 1);
lean::inc(x_1387);
lean::dec(x_1382);
x_1390 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1391 = l_lean_elaborator_expr_mk__annotation(x_1390, x_1358);
x_1392 = lean_expr_mk_app(x_1391, x_1385);
x_1393 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1393, 0, x_1392);
lean::cnstr_set(x_1393, 1, x_1387);
x_14 = x_1393;
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
obj* x_1396; 
x_1396 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1396) == 0)
{
obj* x_1398; obj* x_1399; obj* x_1400; 
lean::dec(x_1);
x_1398 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1399 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1399, 0, x_1398);
lean::cnstr_set(x_1399, 1, x_2);
x_1400 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1400, 0, x_1399);
return x_1400;
}
else
{
obj* x_1401; obj* x_1404; obj* x_1407; obj* x_1410; obj* x_1411; obj* x_1412; obj* x_1414; obj* x_1415; obj* x_1416; obj* x_1419; obj* x_1420; obj* x_1421; obj* x_1422; obj* x_1423; obj* x_1424; 
x_1401 = lean::cnstr_get(x_1396, 0);
lean::inc(x_1401);
lean::dec(x_1396);
x_1404 = lean::cnstr_get(x_1, 0);
lean::inc(x_1404);
lean::dec(x_1);
x_1407 = lean::cnstr_get(x_1404, 2);
lean::inc(x_1407);
lean::dec(x_1404);
x_1410 = l_lean_file__map_to__position(x_1407, x_1401);
x_1411 = lean::box(0);
x_1412 = lean::cnstr_get(x_1410, 1);
lean::inc(x_1412);
x_1414 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1415 = l_lean_kvmap_set__nat(x_1411, x_1414, x_1412);
x_1416 = lean::cnstr_get(x_1410, 0);
lean::inc(x_1416);
lean::dec(x_1410);
x_1419 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1420 = l_lean_kvmap_set__nat(x_1415, x_1419, x_1416);
x_1421 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1422 = lean_expr_mk_mdata(x_1420, x_1421);
x_1423 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1423, 0, x_1422);
lean::cnstr_set(x_1423, 1, x_2);
x_1424 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1424, 0, x_1423);
return x_1424;
}
}
else
{
obj* x_1427; obj* x_1428; obj* x_1429; 
lean::dec(x_1);
lean::dec(x_0);
x_1427 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1428 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1428, 0, x_1427);
lean::cnstr_set(x_1428, 1, x_2);
x_1429 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1429, 0, x_1428);
return x_1429;
}
}
}
else
{
obj* x_1431; obj* x_1432; obj* x_1436; obj* x_1437; obj* x_1440; obj* x_1441; obj* x_1442; obj* x_1444; 
lean::dec(x_9);
x_1431 = l_lean_parser_term_anonymous__constructor_has__view;
x_1432 = lean::cnstr_get(x_1431, 0);
lean::inc(x_1432);
lean::dec(x_1431);
lean::inc(x_0);
x_1436 = lean::apply_1(x_1432, x_0);
x_1437 = lean::cnstr_get(x_1436, 1);
lean::inc(x_1437);
lean::dec(x_1436);
x_1440 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_1437);
x_1441 = l_lean_expander_get__opt__type___main___closed__1;
x_1442 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_1441, x_1440);
lean::inc(x_1);
x_1444 = l_lean_elaborator_to__pexpr___main(x_1442, x_1, x_2);
if (lean::obj_tag(x_1444) == 0)
{
obj* x_1448; obj* x_1450; obj* x_1451; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1448 = lean::cnstr_get(x_1444, 0);
if (lean::is_exclusive(x_1444)) {
 x_1450 = x_1444;
} else {
 lean::inc(x_1448);
 lean::dec(x_1444);
 x_1450 = lean::box(0);
}
if (lean::is_scalar(x_1450)) {
 x_1451 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1451 = x_1450;
}
lean::cnstr_set(x_1451, 0, x_1448);
return x_1451;
}
else
{
obj* x_1452; obj* x_1455; obj* x_1457; obj* x_1460; obj* x_1461; obj* x_1462; 
x_1452 = lean::cnstr_get(x_1444, 0);
lean::inc(x_1452);
lean::dec(x_1444);
x_1455 = lean::cnstr_get(x_1452, 0);
lean::inc(x_1455);
x_1457 = lean::cnstr_get(x_1452, 1);
lean::inc(x_1457);
lean::dec(x_1452);
x_1460 = l_lean_elaborator_to__pexpr___main___closed__43;
x_1461 = l_lean_elaborator_expr_mk__annotation(x_1460, x_1455);
x_1462 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1462, 0, x_1461);
lean::cnstr_set(x_1462, 1, x_1457);
x_14 = x_1462;
goto lbl_15;
}
}
}
else
{
obj* x_1464; obj* x_1465; obj* x_1469; obj* x_1470; obj* x_1471; obj* x_1474; obj* x_1476; 
lean::dec(x_9);
x_1464 = l_lean_parser_term_sort__app_has__view;
x_1465 = lean::cnstr_get(x_1464, 0);
lean::inc(x_1465);
lean::dec(x_1464);
lean::inc(x_0);
x_1469 = lean::apply_1(x_1465, x_0);
x_1470 = l_lean_parser_term_sort_has__view;
x_1471 = lean::cnstr_get(x_1470, 0);
lean::inc(x_1471);
lean::dec(x_1470);
x_1474 = lean::cnstr_get(x_1469, 0);
lean::inc(x_1474);
x_1476 = lean::apply_1(x_1471, x_1474);
if (lean::obj_tag(x_1476) == 0)
{
obj* x_1478; obj* x_1482; 
lean::dec(x_1476);
x_1478 = lean::cnstr_get(x_1469, 1);
lean::inc(x_1478);
lean::dec(x_1469);
lean::inc(x_1);
x_1482 = l_lean_elaborator_to__level___main(x_1478, x_1, x_2);
if (lean::obj_tag(x_1482) == 0)
{
obj* x_1486; obj* x_1488; obj* x_1489; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1486 = lean::cnstr_get(x_1482, 0);
if (lean::is_exclusive(x_1482)) {
 x_1488 = x_1482;
} else {
 lean::inc(x_1486);
 lean::dec(x_1482);
 x_1488 = lean::box(0);
}
if (lean::is_scalar(x_1488)) {
 x_1489 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1489 = x_1488;
}
lean::cnstr_set(x_1489, 0, x_1486);
return x_1489;
}
else
{
obj* x_1490; obj* x_1493; obj* x_1495; obj* x_1498; obj* x_1499; 
x_1490 = lean::cnstr_get(x_1482, 0);
lean::inc(x_1490);
lean::dec(x_1482);
x_1493 = lean::cnstr_get(x_1490, 0);
lean::inc(x_1493);
x_1495 = lean::cnstr_get(x_1490, 1);
lean::inc(x_1495);
lean::dec(x_1490);
x_1498 = lean_expr_mk_sort(x_1493);
x_1499 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1499, 0, x_1498);
lean::cnstr_set(x_1499, 1, x_1495);
x_14 = x_1499;
goto lbl_15;
}
}
else
{
obj* x_1501; obj* x_1505; 
lean::dec(x_1476);
x_1501 = lean::cnstr_get(x_1469, 1);
lean::inc(x_1501);
lean::dec(x_1469);
lean::inc(x_1);
x_1505 = l_lean_elaborator_to__level___main(x_1501, x_1, x_2);
if (lean::obj_tag(x_1505) == 0)
{
obj* x_1509; obj* x_1511; obj* x_1512; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1509 = lean::cnstr_get(x_1505, 0);
if (lean::is_exclusive(x_1505)) {
 x_1511 = x_1505;
} else {
 lean::inc(x_1509);
 lean::dec(x_1505);
 x_1511 = lean::box(0);
}
if (lean::is_scalar(x_1511)) {
 x_1512 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1512 = x_1511;
}
lean::cnstr_set(x_1512, 0, x_1509);
return x_1512;
}
else
{
obj* x_1513; obj* x_1516; obj* x_1518; obj* x_1521; obj* x_1522; obj* x_1523; 
x_1513 = lean::cnstr_get(x_1505, 0);
lean::inc(x_1513);
lean::dec(x_1505);
x_1516 = lean::cnstr_get(x_1513, 0);
lean::inc(x_1516);
x_1518 = lean::cnstr_get(x_1513, 1);
lean::inc(x_1518);
lean::dec(x_1513);
x_1521 = level_mk_succ(x_1516);
x_1522 = lean_expr_mk_sort(x_1521);
x_1523 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1523, 0, x_1522);
lean::cnstr_set(x_1523, 1, x_1518);
x_14 = x_1523;
goto lbl_15;
}
}
}
}
else
{
obj* x_1526; obj* x_1527; obj* x_1531; 
lean::dec(x_9);
lean::dec(x_7);
x_1526 = l_lean_parser_term_sort_has__view;
x_1527 = lean::cnstr_get(x_1526, 0);
lean::inc(x_1527);
lean::dec(x_1526);
lean::inc(x_0);
x_1531 = lean::apply_1(x_1527, x_0);
if (lean::obj_tag(x_1531) == 0)
{
lean::dec(x_1531);
if (x_21 == 0)
{
obj* x_1533; 
x_1533 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1533) == 0)
{
obj* x_1535; obj* x_1536; obj* x_1537; 
lean::dec(x_1);
x_1535 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1536 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1536, 0, x_1535);
lean::cnstr_set(x_1536, 1, x_2);
x_1537 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1537, 0, x_1536);
return x_1537;
}
else
{
obj* x_1538; obj* x_1541; obj* x_1544; obj* x_1547; obj* x_1548; obj* x_1549; obj* x_1551; obj* x_1552; obj* x_1553; obj* x_1556; obj* x_1557; obj* x_1558; obj* x_1559; obj* x_1560; obj* x_1561; 
x_1538 = lean::cnstr_get(x_1533, 0);
lean::inc(x_1538);
lean::dec(x_1533);
x_1541 = lean::cnstr_get(x_1, 0);
lean::inc(x_1541);
lean::dec(x_1);
x_1544 = lean::cnstr_get(x_1541, 2);
lean::inc(x_1544);
lean::dec(x_1541);
x_1547 = l_lean_file__map_to__position(x_1544, x_1538);
x_1548 = lean::box(0);
x_1549 = lean::cnstr_get(x_1547, 1);
lean::inc(x_1549);
x_1551 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1552 = l_lean_kvmap_set__nat(x_1548, x_1551, x_1549);
x_1553 = lean::cnstr_get(x_1547, 0);
lean::inc(x_1553);
lean::dec(x_1547);
x_1556 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1557 = l_lean_kvmap_set__nat(x_1552, x_1556, x_1553);
x_1558 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1559 = lean_expr_mk_mdata(x_1557, x_1558);
x_1560 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1560, 0, x_1559);
lean::cnstr_set(x_1560, 1, x_2);
x_1561 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1561, 0, x_1560);
return x_1561;
}
}
else
{
obj* x_1564; obj* x_1565; obj* x_1566; 
lean::dec(x_1);
lean::dec(x_0);
x_1564 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1565 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1565, 0, x_1564);
lean::cnstr_set(x_1565, 1, x_2);
x_1566 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1566, 0, x_1565);
return x_1566;
}
}
else
{
lean::dec(x_1531);
if (x_21 == 0)
{
obj* x_1568; 
x_1568 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1568) == 0)
{
obj* x_1570; obj* x_1571; obj* x_1572; 
lean::dec(x_1);
x_1570 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1571 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1571, 0, x_1570);
lean::cnstr_set(x_1571, 1, x_2);
x_1572 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1572, 0, x_1571);
return x_1572;
}
else
{
obj* x_1573; obj* x_1576; obj* x_1579; obj* x_1582; obj* x_1583; obj* x_1584; obj* x_1586; obj* x_1587; obj* x_1588; obj* x_1591; obj* x_1592; obj* x_1593; obj* x_1594; obj* x_1595; obj* x_1596; 
x_1573 = lean::cnstr_get(x_1568, 0);
lean::inc(x_1573);
lean::dec(x_1568);
x_1576 = lean::cnstr_get(x_1, 0);
lean::inc(x_1576);
lean::dec(x_1);
x_1579 = lean::cnstr_get(x_1576, 2);
lean::inc(x_1579);
lean::dec(x_1576);
x_1582 = l_lean_file__map_to__position(x_1579, x_1573);
x_1583 = lean::box(0);
x_1584 = lean::cnstr_get(x_1582, 1);
lean::inc(x_1584);
x_1586 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1587 = l_lean_kvmap_set__nat(x_1583, x_1586, x_1584);
x_1588 = lean::cnstr_get(x_1582, 0);
lean::inc(x_1588);
lean::dec(x_1582);
x_1591 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1592 = l_lean_kvmap_set__nat(x_1587, x_1591, x_1588);
x_1593 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1594 = lean_expr_mk_mdata(x_1592, x_1593);
x_1595 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1595, 0, x_1594);
lean::cnstr_set(x_1595, 1, x_2);
x_1596 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1596, 0, x_1595);
return x_1596;
}
}
else
{
obj* x_1599; obj* x_1600; obj* x_1601; 
lean::dec(x_1);
lean::dec(x_0);
x_1599 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1600 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1600, 0, x_1599);
lean::cnstr_set(x_1600, 1, x_2);
x_1601 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1601, 0, x_1600);
return x_1601;
}
}
}
}
else
{
obj* x_1603; obj* x_1604; obj* x_1608; obj* x_1609; 
lean::dec(x_9);
x_1603 = l_lean_parser_term_pi_has__view;
x_1604 = lean::cnstr_get(x_1603, 0);
lean::inc(x_1604);
lean::dec(x_1603);
lean::inc(x_0);
x_1608 = lean::apply_1(x_1604, x_0);
x_1609 = lean::cnstr_get(x_1608, 1);
lean::inc(x_1609);
if (lean::obj_tag(x_1609) == 0)
{
obj* x_1613; obj* x_1616; 
lean::dec(x_1609);
lean::dec(x_1608);
x_1613 = l_lean_elaborator_to__pexpr___main___closed__45;
lean::inc(x_1);
lean::inc(x_0);
x_1616 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1613, x_1, x_2);
if (lean::obj_tag(x_1616) == 0)
{
obj* x_1620; obj* x_1622; obj* x_1623; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1620 = lean::cnstr_get(x_1616, 0);
if (lean::is_exclusive(x_1616)) {
 x_1622 = x_1616;
} else {
 lean::inc(x_1620);
 lean::dec(x_1616);
 x_1622 = lean::box(0);
}
if (lean::is_scalar(x_1622)) {
 x_1623 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1623 = x_1622;
}
lean::cnstr_set(x_1623, 0, x_1620);
return x_1623;
}
else
{
obj* x_1624; 
x_1624 = lean::cnstr_get(x_1616, 0);
lean::inc(x_1624);
lean::dec(x_1616);
x_14 = x_1624;
goto lbl_15;
}
}
else
{
obj* x_1627; obj* x_1630; obj* x_1631; obj* x_1633; obj* x_1636; obj* x_1638; obj* x_1642; 
x_1627 = lean::cnstr_get(x_1609, 0);
lean::inc(x_1627);
lean::dec(x_1609);
x_1630 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1627);
x_1631 = lean::cnstr_get(x_1630, 0);
lean::inc(x_1631);
x_1633 = lean::cnstr_get(x_1630, 1);
lean::inc(x_1633);
lean::dec(x_1630);
x_1636 = lean::cnstr_get(x_1633, 0);
lean::inc(x_1636);
x_1638 = lean::cnstr_get(x_1633, 1);
lean::inc(x_1638);
lean::dec(x_1633);
lean::inc(x_1);
x_1642 = l_lean_elaborator_to__pexpr___main(x_1638, x_1, x_2);
if (lean::obj_tag(x_1642) == 0)
{
obj* x_1649; obj* x_1651; obj* x_1652; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1608);
lean::dec(x_1636);
lean::dec(x_1631);
x_1649 = lean::cnstr_get(x_1642, 0);
if (lean::is_exclusive(x_1642)) {
 x_1651 = x_1642;
} else {
 lean::inc(x_1649);
 lean::dec(x_1642);
 x_1651 = lean::box(0);
}
if (lean::is_scalar(x_1651)) {
 x_1652 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1652 = x_1651;
}
lean::cnstr_set(x_1652, 0, x_1649);
return x_1652;
}
else
{
obj* x_1653; obj* x_1656; obj* x_1658; obj* x_1661; obj* x_1665; 
x_1653 = lean::cnstr_get(x_1642, 0);
lean::inc(x_1653);
lean::dec(x_1642);
x_1656 = lean::cnstr_get(x_1653, 0);
lean::inc(x_1656);
x_1658 = lean::cnstr_get(x_1653, 1);
lean::inc(x_1658);
lean::dec(x_1653);
x_1661 = lean::cnstr_get(x_1608, 3);
lean::inc(x_1661);
lean::dec(x_1608);
lean::inc(x_1);
x_1665 = l_lean_elaborator_to__pexpr___main(x_1661, x_1, x_1658);
if (lean::obj_tag(x_1665) == 0)
{
obj* x_1672; obj* x_1674; obj* x_1675; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1636);
lean::dec(x_1631);
lean::dec(x_1656);
x_1672 = lean::cnstr_get(x_1665, 0);
if (lean::is_exclusive(x_1665)) {
 x_1674 = x_1665;
} else {
 lean::inc(x_1672);
 lean::dec(x_1665);
 x_1674 = lean::box(0);
}
if (lean::is_scalar(x_1674)) {
 x_1675 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1675 = x_1674;
}
lean::cnstr_set(x_1675, 0, x_1672);
return x_1675;
}
else
{
obj* x_1676; obj* x_1679; obj* x_1681; obj* x_1684; uint8 x_1685; obj* x_1686; obj* x_1687; 
x_1676 = lean::cnstr_get(x_1665, 0);
lean::inc(x_1676);
lean::dec(x_1665);
x_1679 = lean::cnstr_get(x_1676, 0);
lean::inc(x_1679);
x_1681 = lean::cnstr_get(x_1676, 1);
lean::inc(x_1681);
lean::dec(x_1676);
x_1684 = l_lean_elaborator_mangle__ident(x_1636);
x_1685 = lean::unbox(x_1631);
x_1686 = lean_expr_mk_pi(x_1684, x_1685, x_1656, x_1679);
x_1687 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1687, 0, x_1686);
lean::cnstr_set(x_1687, 1, x_1681);
x_14 = x_1687;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1689; obj* x_1690; obj* x_1694; obj* x_1695; 
lean::dec(x_9);
x_1689 = l_lean_parser_term_lambda_has__view;
x_1690 = lean::cnstr_get(x_1689, 0);
lean::inc(x_1690);
lean::dec(x_1689);
lean::inc(x_0);
x_1694 = lean::apply_1(x_1690, x_0);
x_1695 = lean::cnstr_get(x_1694, 1);
lean::inc(x_1695);
if (lean::obj_tag(x_1695) == 0)
{
obj* x_1699; obj* x_1702; 
lean::dec(x_1695);
lean::dec(x_1694);
x_1699 = l_lean_elaborator_to__pexpr___main___closed__46;
lean::inc(x_1);
lean::inc(x_0);
x_1702 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1699, x_1, x_2);
if (lean::obj_tag(x_1702) == 0)
{
obj* x_1706; obj* x_1708; obj* x_1709; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1706 = lean::cnstr_get(x_1702, 0);
if (lean::is_exclusive(x_1702)) {
 x_1708 = x_1702;
} else {
 lean::inc(x_1706);
 lean::dec(x_1702);
 x_1708 = lean::box(0);
}
if (lean::is_scalar(x_1708)) {
 x_1709 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1709 = x_1708;
}
lean::cnstr_set(x_1709, 0, x_1706);
return x_1709;
}
else
{
obj* x_1710; 
x_1710 = lean::cnstr_get(x_1702, 0);
lean::inc(x_1710);
lean::dec(x_1702);
x_14 = x_1710;
goto lbl_15;
}
}
else
{
obj* x_1713; obj* x_1716; obj* x_1717; obj* x_1719; obj* x_1722; obj* x_1724; obj* x_1728; 
x_1713 = lean::cnstr_get(x_1695, 0);
lean::inc(x_1713);
lean::dec(x_1695);
x_1716 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1713);
x_1717 = lean::cnstr_get(x_1716, 0);
lean::inc(x_1717);
x_1719 = lean::cnstr_get(x_1716, 1);
lean::inc(x_1719);
lean::dec(x_1716);
x_1722 = lean::cnstr_get(x_1719, 0);
lean::inc(x_1722);
x_1724 = lean::cnstr_get(x_1719, 1);
lean::inc(x_1724);
lean::dec(x_1719);
lean::inc(x_1);
x_1728 = l_lean_elaborator_to__pexpr___main(x_1724, x_1, x_2);
if (lean::obj_tag(x_1728) == 0)
{
obj* x_1735; obj* x_1737; obj* x_1738; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1717);
lean::dec(x_1722);
lean::dec(x_1694);
x_1735 = lean::cnstr_get(x_1728, 0);
if (lean::is_exclusive(x_1728)) {
 x_1737 = x_1728;
} else {
 lean::inc(x_1735);
 lean::dec(x_1728);
 x_1737 = lean::box(0);
}
if (lean::is_scalar(x_1737)) {
 x_1738 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1738 = x_1737;
}
lean::cnstr_set(x_1738, 0, x_1735);
return x_1738;
}
else
{
obj* x_1739; obj* x_1742; obj* x_1744; obj* x_1747; obj* x_1751; 
x_1739 = lean::cnstr_get(x_1728, 0);
lean::inc(x_1739);
lean::dec(x_1728);
x_1742 = lean::cnstr_get(x_1739, 0);
lean::inc(x_1742);
x_1744 = lean::cnstr_get(x_1739, 1);
lean::inc(x_1744);
lean::dec(x_1739);
x_1747 = lean::cnstr_get(x_1694, 3);
lean::inc(x_1747);
lean::dec(x_1694);
lean::inc(x_1);
x_1751 = l_lean_elaborator_to__pexpr___main(x_1747, x_1, x_1744);
if (lean::obj_tag(x_1751) == 0)
{
obj* x_1758; obj* x_1760; obj* x_1761; 
lean::dec(x_1742);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1717);
lean::dec(x_1722);
x_1758 = lean::cnstr_get(x_1751, 0);
if (lean::is_exclusive(x_1751)) {
 x_1760 = x_1751;
} else {
 lean::inc(x_1758);
 lean::dec(x_1751);
 x_1760 = lean::box(0);
}
if (lean::is_scalar(x_1760)) {
 x_1761 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1761 = x_1760;
}
lean::cnstr_set(x_1761, 0, x_1758);
return x_1761;
}
else
{
obj* x_1762; obj* x_1765; obj* x_1767; obj* x_1770; uint8 x_1771; obj* x_1772; obj* x_1773; 
x_1762 = lean::cnstr_get(x_1751, 0);
lean::inc(x_1762);
lean::dec(x_1751);
x_1765 = lean::cnstr_get(x_1762, 0);
lean::inc(x_1765);
x_1767 = lean::cnstr_get(x_1762, 1);
lean::inc(x_1767);
lean::dec(x_1762);
x_1770 = l_lean_elaborator_mangle__ident(x_1722);
x_1771 = lean::unbox(x_1717);
x_1772 = lean_expr_mk_lambda(x_1770, x_1771, x_1742, x_1765);
x_1773 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1773, 0, x_1772);
lean::cnstr_set(x_1773, 1, x_1767);
x_14 = x_1773;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1775; obj* x_1776; obj* x_1780; obj* x_1781; obj* x_1784; 
lean::dec(x_9);
x_1775 = l_lean_parser_term_app_has__view;
x_1776 = lean::cnstr_get(x_1775, 0);
lean::inc(x_1776);
lean::dec(x_1775);
lean::inc(x_0);
x_1780 = lean::apply_1(x_1776, x_0);
x_1781 = lean::cnstr_get(x_1780, 0);
lean::inc(x_1781);
lean::inc(x_1);
x_1784 = l_lean_elaborator_to__pexpr___main(x_1781, x_1, x_2);
if (lean::obj_tag(x_1784) == 0)
{
obj* x_1789; obj* x_1791; obj* x_1792; 
lean::dec(x_1780);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1789 = lean::cnstr_get(x_1784, 0);
if (lean::is_exclusive(x_1784)) {
 x_1791 = x_1784;
} else {
 lean::inc(x_1789);
 lean::dec(x_1784);
 x_1791 = lean::box(0);
}
if (lean::is_scalar(x_1791)) {
 x_1792 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1792 = x_1791;
}
lean::cnstr_set(x_1792, 0, x_1789);
return x_1792;
}
else
{
obj* x_1793; obj* x_1796; obj* x_1798; obj* x_1801; obj* x_1805; 
x_1793 = lean::cnstr_get(x_1784, 0);
lean::inc(x_1793);
lean::dec(x_1784);
x_1796 = lean::cnstr_get(x_1793, 0);
lean::inc(x_1796);
x_1798 = lean::cnstr_get(x_1793, 1);
lean::inc(x_1798);
lean::dec(x_1793);
x_1801 = lean::cnstr_get(x_1780, 1);
lean::inc(x_1801);
lean::dec(x_1780);
lean::inc(x_1);
x_1805 = l_lean_elaborator_to__pexpr___main(x_1801, x_1, x_1798);
if (lean::obj_tag(x_1805) == 0)
{
obj* x_1810; obj* x_1812; obj* x_1813; 
lean::dec(x_1796);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1810 = lean::cnstr_get(x_1805, 0);
if (lean::is_exclusive(x_1805)) {
 x_1812 = x_1805;
} else {
 lean::inc(x_1810);
 lean::dec(x_1805);
 x_1812 = lean::box(0);
}
if (lean::is_scalar(x_1812)) {
 x_1813 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1813 = x_1812;
}
lean::cnstr_set(x_1813, 0, x_1810);
return x_1813;
}
else
{
obj* x_1814; obj* x_1817; obj* x_1819; obj* x_1822; obj* x_1823; 
x_1814 = lean::cnstr_get(x_1805, 0);
lean::inc(x_1814);
lean::dec(x_1805);
x_1817 = lean::cnstr_get(x_1814, 0);
lean::inc(x_1817);
x_1819 = lean::cnstr_get(x_1814, 1);
lean::inc(x_1819);
lean::dec(x_1814);
x_1822 = lean_expr_mk_app(x_1796, x_1817);
x_1823 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_1825; obj* x_1826; obj* x_1830; obj* x_1831; 
lean::dec(x_9);
x_1825 = l_lean_parser_ident__univs_has__view;
x_1826 = lean::cnstr_get(x_1825, 0);
lean::inc(x_1826);
lean::dec(x_1825);
lean::inc(x_0);
x_1830 = lean::apply_1(x_1826, x_0);
x_1831 = lean::cnstr_get(x_1830, 1);
lean::inc(x_1831);
if (lean::obj_tag(x_1831) == 0)
{
obj* x_1833; obj* x_1837; obj* x_1838; obj* x_1839; obj* x_1840; obj* x_1843; obj* x_1844; obj* x_1845; obj* x_1846; obj* x_1847; obj* x_1848; uint8 x_1849; 
x_1833 = lean::cnstr_get(x_1830, 0);
lean::inc(x_1833);
lean::dec(x_1830);
lean::inc(x_1833);
x_1837 = l_lean_elaborator_mangle__ident(x_1833);
x_1838 = lean::box(0);
x_1839 = lean_expr_mk_const(x_1837, x_1838);
x_1840 = lean::cnstr_get(x_1833, 3);
lean::inc(x_1840);
lean::dec(x_1833);
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
obj* x_1881; obj* x_1884; obj* x_1887; obj* x_1891; 
x_1881 = lean::cnstr_get(x_1830, 0);
lean::inc(x_1881);
lean::dec(x_1830);
x_1884 = lean::cnstr_get(x_1831, 0);
lean::inc(x_1884);
lean::dec(x_1831);
x_1887 = lean::cnstr_get(x_1884, 1);
lean::inc(x_1887);
lean::dec(x_1884);
lean::inc(x_1);
x_1891 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_1887, x_1, x_2);
if (lean::obj_tag(x_1891) == 0)
{
obj* x_1896; obj* x_1898; obj* x_1899; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1881);
x_1896 = lean::cnstr_get(x_1891, 0);
if (lean::is_exclusive(x_1891)) {
 x_1898 = x_1891;
} else {
 lean::inc(x_1896);
 lean::dec(x_1891);
 x_1898 = lean::box(0);
}
if (lean::is_scalar(x_1898)) {
 x_1899 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1899 = x_1898;
}
lean::cnstr_set(x_1899, 0, x_1896);
return x_1899;
}
else
{
obj* x_1900; obj* x_1903; obj* x_1905; obj* x_1909; obj* x_1910; obj* x_1911; obj* x_1914; obj* x_1915; obj* x_1916; obj* x_1917; obj* x_1918; obj* x_1919; 
x_1900 = lean::cnstr_get(x_1891, 0);
lean::inc(x_1900);
lean::dec(x_1891);
x_1903 = lean::cnstr_get(x_1900, 0);
lean::inc(x_1903);
x_1905 = lean::cnstr_get(x_1900, 1);
lean::inc(x_1905);
lean::dec(x_1900);
lean::inc(x_1881);
x_1909 = l_lean_elaborator_mangle__ident(x_1881);
x_1910 = lean_expr_mk_const(x_1909, x_1903);
x_1911 = lean::cnstr_get(x_1881, 3);
lean::inc(x_1911);
lean::dec(x_1881);
x_1914 = lean::mk_nat_obj(0u);
x_1915 = l_list_enum__from___main___rarg(x_1914, x_1911);
x_1916 = l_lean_elaborator_to__pexpr___main___closed__47;
x_1917 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(x_1916, x_1915);
x_1918 = lean_expr_mk_mdata(x_1917, x_1910);
x_1919 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1919, 0, x_1918);
lean::cnstr_set(x_1919, 1, x_1905);
x_14 = x_1919;
goto lbl_15;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_1923; obj* x_1925; obj* x_1926; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1923 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_1925 = x_12;
} else {
 lean::inc(x_1923);
 lean::dec(x_12);
 x_1925 = lean::box(0);
}
if (lean::is_scalar(x_1925)) {
 x_1926 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1926 = x_1925;
}
lean::cnstr_set(x_1926, 0, x_1923);
return x_1926;
}
else
{
obj* x_1927; obj* x_1929; obj* x_1930; obj* x_1932; obj* x_1935; uint8 x_1936; 
x_1927 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 x_1929 = x_12;
} else {
 lean::inc(x_1927);
 lean::dec(x_12);
 x_1929 = lean::box(0);
}
x_1930 = lean::cnstr_get(x_1927, 0);
lean::inc(x_1930);
x_1932 = lean::cnstr_get(x_1927, 1);
lean::inc(x_1932);
lean::dec(x_1927);
x_1935 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1936 = lean_name_dec_eq(x_7, x_1935);
lean::dec(x_7);
if (x_1936 == 0)
{
obj* x_1938; 
x_1938 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1938) == 0)
{
obj* x_1940; obj* x_1941; 
lean::dec(x_1);
x_1940 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1940, 0, x_1930);
lean::cnstr_set(x_1940, 1, x_1932);
if (lean::is_scalar(x_1929)) {
 x_1941 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1941 = x_1929;
}
lean::cnstr_set(x_1941, 0, x_1940);
return x_1941;
}
else
{
obj* x_1942; obj* x_1945; obj* x_1948; obj* x_1951; obj* x_1952; obj* x_1953; obj* x_1955; obj* x_1956; obj* x_1957; obj* x_1960; obj* x_1961; obj* x_1962; obj* x_1963; obj* x_1964; 
x_1942 = lean::cnstr_get(x_1938, 0);
lean::inc(x_1942);
lean::dec(x_1938);
x_1945 = lean::cnstr_get(x_1, 0);
lean::inc(x_1945);
lean::dec(x_1);
x_1948 = lean::cnstr_get(x_1945, 2);
lean::inc(x_1948);
lean::dec(x_1945);
x_1951 = l_lean_file__map_to__position(x_1948, x_1942);
x_1952 = lean::box(0);
x_1953 = lean::cnstr_get(x_1951, 1);
lean::inc(x_1953);
x_1955 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1956 = l_lean_kvmap_set__nat(x_1952, x_1955, x_1953);
x_1957 = lean::cnstr_get(x_1951, 0);
lean::inc(x_1957);
lean::dec(x_1951);
x_1960 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1961 = l_lean_kvmap_set__nat(x_1956, x_1960, x_1957);
x_1962 = lean_expr_mk_mdata(x_1961, x_1930);
x_1963 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1963, 0, x_1962);
lean::cnstr_set(x_1963, 1, x_1932);
if (lean::is_scalar(x_1929)) {
 x_1964 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1964 = x_1929;
}
lean::cnstr_set(x_1964, 0, x_1963);
return x_1964;
}
}
else
{
obj* x_1967; obj* x_1968; 
lean::dec(x_1);
lean::dec(x_0);
x_1967 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1967, 0, x_1930);
lean::cnstr_set(x_1967, 1, x_1932);
if (lean::is_scalar(x_1929)) {
 x_1968 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1968 = x_1929;
}
lean::cnstr_set(x_1968, 0, x_1967);
return x_1968;
}
}
}
lbl_15:
{
obj* x_1969; obj* x_1971; obj* x_1974; uint8 x_1975; 
x_1969 = lean::cnstr_get(x_14, 0);
lean::inc(x_1969);
x_1971 = lean::cnstr_get(x_14, 1);
lean::inc(x_1971);
lean::dec(x_14);
x_1974 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1975 = lean_name_dec_eq(x_7, x_1974);
lean::dec(x_7);
if (x_1975 == 0)
{
obj* x_1977; 
x_1977 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1977) == 0)
{
obj* x_1979; obj* x_1980; 
lean::dec(x_1);
x_1979 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1979, 0, x_1969);
lean::cnstr_set(x_1979, 1, x_1971);
x_1980 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1980, 0, x_1979);
return x_1980;
}
else
{
obj* x_1981; obj* x_1984; obj* x_1987; obj* x_1990; obj* x_1991; obj* x_1992; obj* x_1994; obj* x_1995; obj* x_1996; obj* x_1999; obj* x_2000; obj* x_2001; obj* x_2002; obj* x_2003; 
x_1981 = lean::cnstr_get(x_1977, 0);
lean::inc(x_1981);
lean::dec(x_1977);
x_1984 = lean::cnstr_get(x_1, 0);
lean::inc(x_1984);
lean::dec(x_1);
x_1987 = lean::cnstr_get(x_1984, 2);
lean::inc(x_1987);
lean::dec(x_1984);
x_1990 = l_lean_file__map_to__position(x_1987, x_1981);
x_1991 = lean::box(0);
x_1992 = lean::cnstr_get(x_1990, 1);
lean::inc(x_1992);
x_1994 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1995 = l_lean_kvmap_set__nat(x_1991, x_1994, x_1992);
x_1996 = lean::cnstr_get(x_1990, 0);
lean::inc(x_1996);
lean::dec(x_1990);
x_1999 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2000 = l_lean_kvmap_set__nat(x_1995, x_1999, x_1996);
x_2001 = lean_expr_mk_mdata(x_2000, x_1969);
x_2002 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2002, 0, x_2001);
lean::cnstr_set(x_2002, 1, x_1971);
x_2003 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2003, 0, x_2002);
return x_2003;
}
}
else
{
obj* x_2006; obj* x_2007; 
lean::dec(x_1);
lean::dec(x_0);
x_2006 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2006, 0, x_1969);
lean::cnstr_set(x_2006, 1, x_1971);
x_2007 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2007, 0, x_2006);
return x_2007;
}
}
lbl_17:
{
obj* x_2008; 
x_2008 = lean::cnstr_get(x_16, 0);
lean::inc(x_2008);
if (lean::obj_tag(x_2008) == 0)
{
obj* x_2011; obj* x_2014; obj* x_2017; 
lean::dec(x_9);
x_2011 = lean::cnstr_get(x_16, 1);
lean::inc(x_2011);
lean::dec(x_16);
x_2014 = l_lean_elaborator_to__pexpr___main___closed__5;
lean::inc(x_1);
lean::inc(x_0);
x_2017 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2014, x_1, x_2011);
if (lean::obj_tag(x_2017) == 0)
{
obj* x_2021; obj* x_2023; obj* x_2024; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_2021 = lean::cnstr_get(x_2017, 0);
if (lean::is_exclusive(x_2017)) {
 x_2023 = x_2017;
} else {
 lean::inc(x_2021);
 lean::dec(x_2017);
 x_2023 = lean::box(0);
}
if (lean::is_scalar(x_2023)) {
 x_2024 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2024 = x_2023;
}
lean::cnstr_set(x_2024, 0, x_2021);
return x_2024;
}
else
{
obj* x_2025; 
x_2025 = lean::cnstr_get(x_2017, 0);
lean::inc(x_2025);
lean::dec(x_2017);
x_14 = x_2025;
goto lbl_15;
}
}
else
{
obj* x_2028; obj* x_2031; obj* x_2033; obj* x_2036; obj* x_2037; obj* x_2038; obj* x_2039; obj* x_2040; obj* x_2041; obj* x_2042; obj* x_2043; obj* x_2044; 
x_2028 = lean::cnstr_get(x_16, 1);
lean::inc(x_2028);
lean::dec(x_16);
x_2031 = lean::cnstr_get(x_2008, 0);
lean::inc(x_2031);
x_2033 = lean::cnstr_get(x_2008, 1);
lean::inc(x_2033);
lean::dec(x_2008);
x_2036 = lean::box(0);
x_2037 = lean::mk_nat_obj(0u);
x_2038 = l_list_length__aux___main___rarg(x_9, x_2037);
x_2039 = l_lean_elaborator_to__pexpr___main___closed__6;
x_2040 = l_lean_kvmap_set__nat(x_2036, x_2039, x_2038);
x_2041 = l_list_reverse___rarg(x_2033);
x_2042 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_2031, x_2041);
x_2043 = lean_expr_mk_mdata(x_2040, x_2042);
x_2044 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2044, 0, x_2043);
lean::cnstr_set(x_2044, 1, x_2028);
x_14 = x_2044;
goto lbl_15;
}
}
}
default:
{
obj* x_2045; 
x_2045 = lean::box(0);
x_3 = x_2045;
goto lbl_4;
}
}
lbl_4:
{
obj* x_2048; obj* x_2049; obj* x_2050; obj* x_2051; obj* x_2052; obj* x_2054; 
lean::dec(x_3);
lean::inc(x_0);
x_2048 = l_lean_parser_syntax_to__format___main(x_0);
x_2049 = lean::mk_nat_obj(80u);
x_2050 = l_lean_format_pretty(x_2048, x_2049);
x_2051 = l_lean_elaborator_to__pexpr___main___closed__1;
x_2052 = lean::string_append(x_2051, x_2050);
lean::dec(x_2050);
x_2054 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2052, x_1, x_2);
return x_2054;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
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
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_48; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_62; obj* x_63; obj* x_65; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; 
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
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
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
if (lean::obj_tag(x_78) == 0)
{
obj* x_82; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_3);
lean::dec(x_55);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
lean::dec(x_77);
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
x_97 = l_list_append___rarg(x_82, x_95);
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
x_111 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_114; obj* x_117; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_133; obj* x_134; obj* x_136; obj* x_137; obj* x_138; obj* x_140; obj* x_141; obj* x_143; obj* x_146; obj* x_148; obj* x_149; obj* x_151; obj* x_153; obj* x_156; obj* x_158; obj* x_160; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
lean::dec(x_45);
x_114 = lean::cnstr_get(x_77, 1);
lean::inc(x_114);
lean::dec(x_77);
x_117 = lean::cnstr_get(x_78, 0);
lean::inc(x_117);
lean::dec(x_78);
x_120 = lean::cnstr_get(x_3, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_3, 1);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_3, 2);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_3, 3);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_55, 0);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_117, 2);
lean::inc(x_130);
x_132 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
x_133 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(x_132, x_130);
x_134 = lean::cnstr_get(x_117, 3);
lean::inc(x_134);
x_136 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1;
x_137 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(x_136, x_134);
x_138 = lean::cnstr_get(x_117, 4);
lean::inc(x_138);
x_140 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(x_138);
x_141 = lean::cnstr_get(x_55, 4);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_55, 5);
lean::inc(x_143);
lean::dec(x_55);
x_146 = lean::cnstr_get(x_117, 5);
lean::inc(x_146);
x_148 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_148, 0, x_128);
lean::cnstr_set(x_148, 1, x_133);
lean::cnstr_set(x_148, 2, x_137);
lean::cnstr_set(x_148, 3, x_140);
lean::cnstr_set(x_148, 4, x_141);
lean::cnstr_set(x_148, 5, x_143);
lean::cnstr_set(x_148, 6, x_146);
x_149 = lean::cnstr_get(x_3, 5);
lean::inc(x_149);
x_151 = lean::cnstr_get(x_3, 6);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_3, 7);
lean::inc(x_153);
lean::dec(x_3);
x_156 = lean::cnstr_get(x_117, 0);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_117, 1);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_117, 6);
lean::inc(x_160);
lean::dec(x_117);
x_163 = l_list_append___rarg(x_114, x_149);
x_164 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_164, 0, x_120);
lean::cnstr_set(x_164, 1, x_122);
lean::cnstr_set(x_164, 2, x_124);
lean::cnstr_set(x_164, 3, x_126);
lean::cnstr_set(x_164, 4, x_148);
lean::cnstr_set(x_164, 5, x_163);
lean::cnstr_set(x_164, 6, x_151);
lean::cnstr_set(x_164, 7, x_153);
lean::cnstr_set(x_164, 8, x_156);
lean::cnstr_set(x_164, 9, x_158);
lean::cnstr_set(x_164, 10, x_160);
x_165 = lean::box(0);
x_166 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_166, 0, x_165);
lean::cnstr_set(x_166, 1, x_164);
if (lean::is_scalar(x_42)) {
 x_167 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_167 = x_42;
}
lean::cnstr_set(x_167, 0, x_166);
return x_167;
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
obj* x_21; obj* x_24; obj* x_26; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_11);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_34 = x_29;
} else {
 lean::inc(x_32);
 lean::dec(x_29);
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
lean::dec(x_36);
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
x_45 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_27; obj* x_30; obj* x_32; obj* x_35; 
x_27 = lean::cnstr_get(x_18, 0);
lean::inc(x_27);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
lean::dec(x_27);
x_35 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(x_9, x_1, x_32);
if (lean::obj_tag(x_35) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_30);
x_39 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_41 = x_35;
} else {
 lean::inc(x_39);
 lean::dec(x_35);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_39);
return x_42;
}
else
{
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_51; obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_43 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_45 = x_35;
} else {
 lean::inc(x_43);
 lean::dec(x_35);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_43, 1);
lean::inc(x_48);
lean::dec(x_43);
x_51 = lean::cnstr_get(x_12, 0);
lean::inc(x_51);
lean::dec(x_12);
x_54 = lean::cnstr_get(x_51, 2);
lean::inc(x_54);
lean::dec(x_51);
x_57 = l_lean_expr_mk__capp(x_54, x_30);
if (lean::is_scalar(x_11)) {
 x_58 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_58 = x_11;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_46);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_45;
}
lean::cnstr_set(x_60, 0, x_59);
return x_60;
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_elaborator_mk__eqns___closed__1;
x_17 = l_lean_expr_mk__capp(x_16, x_11);
x_18 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("private");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = 1;
x_5 = l_lean_kvmap_set__bool(x_0, x_3, x_4);
return x_5;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("protected");
x_3 = lean_name_mk_string(x_1, x_2);
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
obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_76; obj* x_77; obj* x_78; 
x_68 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_70 = x_62;
} else {
 lean::inc(x_68);
 lean::dec(x_62);
 x_70 = lean::box(0);
}
x_71 = lean::cnstr_get(x_68, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
lean::dec(x_68);
x_76 = lean_expr_mk_mdata(x_61, x_71);
x_77 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_99; obj* x_100; obj* x_101; 
x_91 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_93 = x_85;
} else {
 lean::inc(x_91);
 lean::dec(x_85);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_91, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_91, 1);
lean::inc(x_96);
lean::dec(x_91);
x_99 = lean_expr_mk_mdata(x_61, x_94);
x_100 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_18; obj* x_20; obj* x_24; 
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
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
lean::dec(x_15);
lean::inc(x_1);
x_24 = l_lean_elaborator_to__pexpr___main(x_20, x_1, x_2);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_13);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_18);
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
obj* x_34; obj* x_37; obj* x_39; obj* x_42; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(x_9, x_1, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_37);
lean::dec(x_18);
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
obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_59; uint8 x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_51 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
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
x_59 = l_lean_elaborator_mangle__ident(x_18);
x_60 = lean::unbox(x_13);
lean::inc(x_59);
x_62 = lean_expr_local(x_59, x_59, x_37, x_60);
if (lean::is_scalar(x_11)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_11;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_54);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_56);
if (lean::is_scalar(x_53)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_53;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_elaborator_mk__eqns___closed__1;
x_17 = l_lean_expr_mk__capp(x_16, x_11);
x_18 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_21; obj* x_24; obj* x_26; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_11);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_34 = x_29;
} else {
 lean::inc(x_32);
 lean::dec(x_29);
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
lean::dec(x_36);
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
x_45 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_27; obj* x_30; obj* x_32; obj* x_35; obj* x_39; 
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
lean::dec(x_17);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
lean::dec(x_27);
x_35 = lean::cnstr_get(x_9, 3);
lean::inc(x_35);
lean::dec(x_9);
lean::inc(x_2);
x_39 = l_lean_elaborator_to__pexpr___main(x_35, x_2, x_32);
if (lean::obj_tag(x_39) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_30);
x_45 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_47 = x_39;
} else {
 lean::inc(x_45);
 lean::dec(x_39);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_60; 
x_49 = lean::cnstr_get(x_39, 0);
lean::inc(x_49);
lean::dec(x_39);
x_52 = lean::cnstr_get(x_0, 0);
lean::inc(x_52);
x_54 = l_lean_elaborator_mangle__ident(x_52);
x_55 = lean::cnstr_get(x_49, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_49, 1);
lean::inc(x_57);
lean::dec(x_49);
x_60 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_0, x_11, x_2, x_57);
if (lean::obj_tag(x_60) == 0)
{
obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_13);
lean::dec(x_30);
lean::dec(x_54);
lean::dec(x_55);
x_65 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_67 = x_60;
} else {
 lean::inc(x_65);
 lean::dec(x_60);
 x_67 = lean::box(0);
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
obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_69 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_71 = x_60;
} else {
 lean::inc(x_69);
 lean::dec(x_60);
 x_71 = lean::box(0);
}
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_30);
lean::cnstr_set(x_77, 1, x_55);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_54);
lean::cnstr_set(x_78, 1, x_77);
if (lean::is_scalar(x_13)) {
 x_79 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_79 = x_13;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_72);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_74);
if (lean::is_scalar(x_71)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_71;
}
lean::cnstr_set(x_81, 0, x_80);
return x_81;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("command");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("defs");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_lean_kvmap_set__name(x_0, x_3, x_5);
return x_6;
}
}
obj* l_lean_elaborator_elab__def__like(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 3);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_15; obj* x_16; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_15 = l_lean_elaborator_elab__def__like___closed__1;
x_16 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_15, x_4, x_5);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_27; obj* x_31; 
x_17 = lean::cnstr_get(x_2, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_2, 2);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_2, 4);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_6, 1);
lean::inc(x_24);
lean::dec(x_6);
x_27 = lean::cnstr_get(x_8, 0);
lean::inc(x_27);
lean::dec(x_8);
lean::inc(x_4);
x_31 = l_lean_elaborator_decl__modifiers__to__pexpr(x_1, x_4, x_5);
if (lean::obj_tag(x_31) == 0)
{
obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_21);
lean::dec(x_24);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_19);
lean::dec(x_27);
x_40 = lean::cnstr_get(x_31, 0);
if (lean::is_exclusive(x_31)) {
 x_42 = x_31;
} else {
 lean::inc(x_40);
 lean::dec(x_31);
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
obj* x_44; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_44 = lean::cnstr_get(x_31, 0);
lean::inc(x_44);
lean::dec(x_31);
x_47 = lean::cnstr_get(x_44, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_44, 1);
lean::inc(x_49);
lean::dec(x_44);
x_52 = lean::box(0);
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_3);
x_54 = lean_expr_mk_lit(x_53);
if (lean::obj_tag(x_17) == 0)
{
obj* x_58; obj* x_60; 
x_58 = l_lean_expander_get__opt__type___main(x_24);
lean::inc(x_4);
x_60 = l_lean_elaborator_to__pexpr___main(x_58, x_4, x_49);
if (lean::obj_tag(x_17) == 0)
{
if (lean::obj_tag(x_60) == 0)
{
obj* x_68; obj* x_70; obj* x_71; 
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_27);
lean::dec(x_47);
lean::dec(x_54);
x_68 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_70 = x_60;
} else {
 lean::inc(x_68);
 lean::dec(x_60);
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
x_72 = lean::cnstr_get(x_60, 0);
lean::inc(x_72);
lean::dec(x_60);
x_55 = x_52;
x_56 = x_72;
goto lbl_57;
}
}
else
{
if (lean::obj_tag(x_60) == 0)
{
obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_27);
lean::dec(x_47);
lean::dec(x_54);
x_82 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_84 = x_60;
} else {
 lean::inc(x_82);
 lean::dec(x_60);
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
obj* x_86; obj* x_89; obj* x_92; obj* x_95; 
x_86 = lean::cnstr_get(x_17, 0);
lean::inc(x_86);
lean::dec(x_17);
x_89 = lean::cnstr_get(x_60, 0);
lean::inc(x_89);
lean::dec(x_60);
x_92 = lean::cnstr_get(x_86, 1);
lean::inc(x_92);
lean::dec(x_86);
x_95 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(x_92);
x_55 = x_95;
x_56 = x_89;
goto lbl_57;
}
}
}
else
{
obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_116; obj* x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_129; obj* x_130; obj* x_132; obj* x_134; obj* x_136; obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_146; 
x_96 = lean::cnstr_get(x_17, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_49, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_49, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_49, 2);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_49, 3);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_49, 4);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_106, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_106, 1);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_96, 1);
lean::inc(x_112);
lean::dec(x_96);
lean::inc(x_112);
x_116 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(x_112);
x_117 = l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(x_110, x_116);
x_118 = lean::cnstr_get(x_106, 2);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_106, 3);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_106, 4);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_106, 5);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_106, 6);
lean::inc(x_126);
lean::dec(x_106);
x_129 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_129, 0, x_108);
lean::cnstr_set(x_129, 1, x_117);
lean::cnstr_set(x_129, 2, x_118);
lean::cnstr_set(x_129, 3, x_120);
lean::cnstr_set(x_129, 4, x_122);
lean::cnstr_set(x_129, 5, x_124);
lean::cnstr_set(x_129, 6, x_126);
x_130 = lean::cnstr_get(x_49, 5);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_49, 6);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_49, 7);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_49, 8);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_49, 9);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_49, 10);
lean::inc(x_140);
lean::dec(x_49);
x_143 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_143, 0, x_98);
lean::cnstr_set(x_143, 1, x_100);
lean::cnstr_set(x_143, 2, x_102);
lean::cnstr_set(x_143, 3, x_104);
lean::cnstr_set(x_143, 4, x_129);
lean::cnstr_set(x_143, 5, x_130);
lean::cnstr_set(x_143, 6, x_132);
lean::cnstr_set(x_143, 7, x_134);
lean::cnstr_set(x_143, 8, x_136);
lean::cnstr_set(x_143, 9, x_138);
lean::cnstr_set(x_143, 10, x_140);
x_144 = l_lean_expander_get__opt__type___main(x_24);
lean::inc(x_4);
x_146 = l_lean_elaborator_to__pexpr___main(x_144, x_4, x_143);
if (lean::obj_tag(x_17) == 0)
{
lean::dec(x_112);
if (lean::obj_tag(x_146) == 0)
{
obj* x_155; obj* x_157; obj* x_158; 
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_27);
lean::dec(x_47);
lean::dec(x_54);
x_155 = lean::cnstr_get(x_146, 0);
if (lean::is_exclusive(x_146)) {
 x_157 = x_146;
} else {
 lean::inc(x_155);
 lean::dec(x_146);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_155);
return x_158;
}
else
{
obj* x_159; 
x_159 = lean::cnstr_get(x_146, 0);
lean::inc(x_159);
lean::dec(x_146);
x_55 = x_52;
x_56 = x_159;
goto lbl_57;
}
}
else
{
lean::dec(x_17);
if (lean::obj_tag(x_146) == 0)
{
obj* x_171; obj* x_173; obj* x_174; 
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_112);
lean::dec(x_27);
lean::dec(x_47);
lean::dec(x_54);
x_171 = lean::cnstr_get(x_146, 0);
if (lean::is_exclusive(x_146)) {
 x_173 = x_146;
} else {
 lean::inc(x_171);
 lean::dec(x_146);
 x_173 = lean::box(0);
}
if (lean::is_scalar(x_173)) {
 x_174 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_174 = x_173;
}
lean::cnstr_set(x_174, 0, x_171);
return x_174;
}
else
{
obj* x_175; obj* x_178; 
x_175 = lean::cnstr_get(x_146, 0);
lean::inc(x_175);
lean::dec(x_146);
x_178 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(x_112);
x_55 = x_178;
x_56 = x_175;
goto lbl_57;
}
}
}
lbl_57:
{
obj* x_179; obj* x_181; obj* x_184; obj* x_185; obj* x_187; uint8 x_188; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
x_179 = lean::cnstr_get(x_56, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_56, 1);
lean::inc(x_181);
lean::dec(x_56);
x_184 = l_lean_elaborator_names__to__pexpr(x_55);
x_185 = lean::cnstr_get(x_19, 0);
lean::inc(x_185);
x_187 = l_lean_elaborator_mangle__ident(x_185);
x_188 = 4;
lean::inc(x_179);
lean::inc(x_187);
x_191 = lean_expr_local(x_187, x_187, x_179, x_188);
x_192 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_192, 0, x_191);
lean::cnstr_set(x_192, 1, x_52);
x_193 = l_lean_elaborator_mk__eqns___closed__1;
x_194 = l_lean_expr_mk__capp(x_193, x_192);
switch (lean::obj_tag(x_21)) {
case 0:
{
obj* x_199; obj* x_202; obj* x_206; 
lean::dec(x_179);
lean::dec(x_19);
x_199 = lean::cnstr_get(x_21, 0);
lean::inc(x_199);
lean::dec(x_21);
x_202 = lean::cnstr_get(x_199, 1);
lean::inc(x_202);
lean::dec(x_199);
lean::inc(x_4);
x_206 = l_lean_elaborator_to__pexpr___main(x_202, x_4, x_181);
if (lean::obj_tag(x_206) == 0)
{
obj* x_214; obj* x_216; obj* x_217; 
lean::dec(x_184);
lean::dec(x_194);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_27);
lean::dec(x_47);
lean::dec(x_54);
x_214 = lean::cnstr_get(x_206, 0);
if (lean::is_exclusive(x_206)) {
 x_216 = x_206;
} else {
 lean::inc(x_214);
 lean::dec(x_206);
 x_216 = lean::box(0);
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_217 = x_216;
}
lean::cnstr_set(x_217, 0, x_214);
return x_217;
}
else
{
obj* x_218; 
x_218 = lean::cnstr_get(x_206, 0);
lean::inc(x_218);
lean::dec(x_206);
x_195 = x_218;
goto lbl_196;
}
}
case 1:
{
obj* x_223; obj* x_224; 
lean::dec(x_21);
lean::dec(x_19);
x_223 = l_lean_elaborator_mk__eqns(x_179, x_52);
x_224 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_224, 0, x_223);
lean::cnstr_set(x_224, 1, x_181);
x_195 = x_224;
goto lbl_196;
}
default:
{
obj* x_225; obj* x_229; 
x_225 = lean::cnstr_get(x_21, 0);
lean::inc(x_225);
lean::dec(x_21);
lean::inc(x_4);
x_229 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_19, x_225, x_4, x_181);
if (lean::obj_tag(x_229) == 0)
{
obj* x_238; obj* x_240; obj* x_241; 
lean::dec(x_184);
lean::dec(x_194);
lean::dec(x_179);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_27);
lean::dec(x_47);
lean::dec(x_54);
x_238 = lean::cnstr_get(x_229, 0);
if (lean::is_exclusive(x_229)) {
 x_240 = x_229;
} else {
 lean::inc(x_238);
 lean::dec(x_229);
 x_240 = lean::box(0);
}
if (lean::is_scalar(x_240)) {
 x_241 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_241 = x_240;
}
lean::cnstr_set(x_241, 0, x_238);
return x_241;
}
else
{
obj* x_242; obj* x_245; obj* x_247; obj* x_250; obj* x_251; 
x_242 = lean::cnstr_get(x_229, 0);
lean::inc(x_242);
lean::dec(x_229);
x_245 = lean::cnstr_get(x_242, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_242, 1);
lean::inc(x_247);
lean::dec(x_242);
x_250 = l_lean_elaborator_mk__eqns(x_179, x_245);
x_251 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_251, 0, x_250);
lean::cnstr_set(x_251, 1, x_247);
x_195 = x_251;
goto lbl_196;
}
}
}
lbl_196:
{
obj* x_252; obj* x_254; obj* x_258; 
x_252 = lean::cnstr_get(x_195, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_195, 1);
lean::inc(x_254);
lean::dec(x_195);
lean::inc(x_4);
x_258 = l_lean_elaborator_simple__binders__to__pexpr(x_27, x_4, x_254);
if (lean::obj_tag(x_258) == 0)
{
obj* x_266; obj* x_268; obj* x_269; 
lean::dec(x_184);
lean::dec(x_194);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_252);
lean::dec(x_47);
lean::dec(x_54);
x_266 = lean::cnstr_get(x_258, 0);
if (lean::is_exclusive(x_258)) {
 x_268 = x_258;
} else {
 lean::inc(x_266);
 lean::dec(x_258);
 x_268 = lean::box(0);
}
if (lean::is_scalar(x_268)) {
 x_269 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_269 = x_268;
}
lean::cnstr_set(x_269, 0, x_266);
return x_269;
}
else
{
obj* x_270; obj* x_273; obj* x_275; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; 
x_270 = lean::cnstr_get(x_258, 0);
lean::inc(x_270);
lean::dec(x_258);
x_273 = lean::cnstr_get(x_270, 0);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_270, 1);
lean::inc(x_275);
lean::dec(x_270);
x_278 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_278, 0, x_252);
lean::cnstr_set(x_278, 1, x_52);
x_279 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_279, 0, x_273);
lean::cnstr_set(x_279, 1, x_278);
x_280 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_280, 0, x_194);
lean::cnstr_set(x_280, 1, x_279);
x_281 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_281, 0, x_184);
lean::cnstr_set(x_281, 1, x_280);
x_282 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_282, 0, x_54);
lean::cnstr_set(x_282, 1, x_281);
x_283 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_283, 0, x_47);
lean::cnstr_set(x_283, 1, x_282);
x_284 = l_lean_expr_mk__capp(x_193, x_283);
x_285 = l_lean_elaborator_elab__def__like___closed__2;
x_286 = lean_expr_mk_mdata(x_285, x_284);
x_287 = l_lean_elaborator_old__elab__command(x_0, x_286, x_4, x_275);
return x_287;
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
obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
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
if (lean::obj_tag(x_18) == 0)
{
obj* x_23; obj* x_26; 
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_18);
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
obj* x_38; 
x_38 = lean::cnstr_get(x_18, 0);
lean::inc(x_38);
lean::dec(x_18);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; 
x_41 = lean::cnstr_get(x_16, 1);
lean::inc(x_41);
lean::dec(x_16);
if (lean::obj_tag(x_41) == 0)
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
x_60 = lean::cnstr_get(x_41, 0);
lean::inc(x_60);
lean::dec(x_41);
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
obj* x_77; obj* x_80; obj* x_82; obj* x_85; obj* x_88; uint8 x_89; obj* x_91; obj* x_92; 
x_77 = lean::cnstr_get(x_67, 0);
lean::inc(x_77);
lean::dec(x_67);
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
lean::dec(x_77);
x_85 = lean::cnstr_get(x_9, 1);
lean::inc(x_85);
lean::dec(x_9);
x_88 = l_lean_elaborator_mangle__ident(x_85);
x_89 = 0;
lean::inc(x_88);
x_91 = lean_expr_local(x_88, x_88, x_80, x_89);
x_92 = lean::alloc_cnstr(0, 2, 0);
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
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_38);
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
obj* x_111; obj* x_113; obj* x_116; 
x_111 = lean::cnstr_get(x_14, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_14, 1);
lean::inc(x_113);
lean::dec(x_14);
x_116 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_11, x_2, x_113);
if (lean::obj_tag(x_116) == 0)
{
obj* x_119; obj* x_121; obj* x_122; 
lean::dec(x_13);
lean::dec(x_111);
x_119 = lean::cnstr_get(x_116, 0);
if (lean::is_exclusive(x_116)) {
 x_121 = x_116;
} else {
 lean::inc(x_119);
 lean::dec(x_116);
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
obj* x_123; obj* x_125; obj* x_126; obj* x_128; obj* x_131; obj* x_132; obj* x_133; 
x_123 = lean::cnstr_get(x_116, 0);
if (lean::is_exclusive(x_116)) {
 x_125 = x_116;
} else {
 lean::inc(x_123);
 lean::dec(x_116);
 x_125 = lean::box(0);
}
x_126 = lean::cnstr_get(x_123, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_123, 1);
lean::inc(x_128);
lean::dec(x_123);
if (lean::is_scalar(x_13)) {
 x_131 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_131 = x_13;
}
lean::cnstr_set(x_131, 0, x_111);
lean::cnstr_set(x_131, 1, x_126);
x_132 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_128);
if (lean::is_scalar(x_125)) {
 x_133 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_133 = x_125;
}
lean::cnstr_set(x_133, 0, x_132);
return x_133;
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
obj* x_24; obj* x_27; obj* x_29; obj* x_32; 
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_9, x_1, x_29);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_11);
lean::dec(x_27);
x_35 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_37 = x_32;
} else {
 lean::inc(x_35);
 lean::dec(x_32);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_41 = x_32;
} else {
 lean::inc(x_39);
 lean::dec(x_32);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
lean::dec(x_39);
if (lean::is_scalar(x_11)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_11;
}
lean::cnstr_set(x_47, 0, x_27);
lean::cnstr_set(x_47, 1, x_42);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
obj* x_75; obj* x_77; obj* x_80; obj* x_82; obj* x_85; obj* x_87; obj* x_90; obj* x_92; 
x_75 = lean::cnstr_get(x_14, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_14, 1);
lean::inc(x_77);
lean::dec(x_14);
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
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_82);
lean::dec(x_80);
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_99);
return x_102;
}
else
{
obj* x_103; obj* x_106; obj* x_108; obj* x_111; 
x_103 = lean::cnstr_get(x_92, 0);
lean::inc(x_103);
lean::dec(x_92);
x_106 = lean::cnstr_get(x_103, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_103, 1);
lean::inc(x_108);
lean::dec(x_103);
x_111 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_11, x_2, x_108);
if (lean::obj_tag(x_111) == 0)
{
obj* x_116; obj* x_118; obj* x_119; 
lean::dec(x_13);
lean::dec(x_82);
lean::dec(x_80);
lean::dec(x_106);
x_116 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_118 = x_111;
} else {
 lean::inc(x_116);
 lean::dec(x_111);
 x_118 = lean::box(0);
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
obj* x_120; obj* x_122; obj* x_123; obj* x_125; obj* x_128; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_134; obj* x_135; obj* x_136; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_120 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_122 = x_111;
} else {
 lean::inc(x_120);
 lean::dec(x_111);
 x_122 = lean::box(0);
}
x_123 = lean::cnstr_get(x_120, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_120, 1);
lean::inc(x_125);
lean::dec(x_120);
x_128 = l_lean_elaborator_mk__eqns___closed__1;
x_129 = l_lean_elaborator_dummy;
x_130 = lean::unbox(x_80);
x_131 = lean_expr_local(x_128, x_128, x_129, x_130);
x_132 = lean::cnstr_get(x_82, 0);
lean::inc(x_132);
x_134 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(x_132);
x_135 = l_lean_elaborator_names__to__pexpr(x_134);
x_136 = lean::cnstr_get(x_82, 1);
lean::inc(x_136);
lean::dec(x_82);
x_139 = l_lean_elaborator_infer__mod__to__pexpr(x_136);
x_140 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_13;
}
lean::cnstr_set(x_141, 0, x_106);
lean::cnstr_set(x_141, 1, x_140);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_139);
lean::cnstr_set(x_142, 1, x_141);
x_143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_143, 0, x_135);
lean::cnstr_set(x_143, 1, x_142);
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_131);
lean::cnstr_set(x_144, 1, x_143);
x_145 = l_lean_expr_mk__capp(x_128, x_144);
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_123);
x_147 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_125);
if (lean::is_scalar(x_122)) {
 x_148 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_148 = x_122;
}
lean::cnstr_set(x_148, 0, x_147);
return x_148;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string(".");
x_2 = lean::box(0);
x_3 = l_lean_name_to__string__with__sep___main(x_1, x_2);
x_4 = l_lean_parser_substring_of__string(x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_4);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_5);
lean::cnstr_set(x_6, 4, x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
return x_7;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("command");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("constant");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_lean_kvmap_set__name(x_0, x_3, x_5);
return x_6;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("command");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("inductives");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_lean_kvmap_set__name(x_0, x_3, x_5);
return x_6;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("command");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("structure");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_lean_kvmap_set__name(x_0, x_3, x_5);
return x_6;
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
obj* x_15; obj* x_18; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_21; obj* x_24; obj* x_25; 
lean::dec(x_18);
x_21 = lean::cnstr_get(x_12, 0);
lean::inc(x_21);
lean::dec(x_12);
x_24 = lean::mk_nat_obj(1u);
x_25 = l_lean_elaborator_elab__def__like(x_0, x_21, x_15, x_24, x_1, x_2);
x_5 = x_25;
goto lbl_6;
}
case 1:
{
obj* x_27; obj* x_30; obj* x_31; 
lean::dec(x_18);
x_27 = lean::cnstr_get(x_12, 0);
lean::inc(x_27);
lean::dec(x_12);
x_30 = lean::mk_nat_obj(5u);
x_31 = l_lean_elaborator_elab__def__like(x_0, x_27, x_15, x_30, x_1, x_2);
x_5 = x_31;
goto lbl_6;
}
default:
{
obj* x_33; obj* x_36; obj* x_37; 
lean::dec(x_18);
x_33 = lean::cnstr_get(x_12, 0);
lean::inc(x_33);
lean::dec(x_12);
x_36 = lean::mk_nat_obj(0u);
x_37 = l_lean_elaborator_elab__def__like(x_0, x_33, x_15, x_36, x_1, x_2);
x_5 = x_37;
goto lbl_6;
}
}
}
case 1:
{
obj* x_38; obj* x_41; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_38 = lean::cnstr_get(x_13, 0);
lean::inc(x_38);
lean::dec(x_13);
x_41 = lean::cnstr_get(x_12, 0);
lean::inc(x_41);
lean::dec(x_12);
x_44 = lean::box(0);
x_45 = lean::cnstr_get(x_38, 1);
lean::inc(x_45);
x_47 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
x_48 = l_option_get__or__else___main___rarg(x_45, x_47);
x_49 = lean::cnstr_get(x_38, 2);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_49, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_49, 1);
lean::inc(x_53);
lean::dec(x_49);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_53);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_51);
lean::cnstr_set(x_57, 1, x_56);
x_58 = lean::cnstr_get(x_38, 3);
lean::inc(x_58);
lean::dec(x_38);
x_61 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
x_62 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_44);
lean::cnstr_set(x_62, 2, x_48);
lean::cnstr_set(x_62, 3, x_57);
lean::cnstr_set(x_62, 4, x_58);
x_63 = lean::mk_nat_obj(3u);
x_64 = l_lean_elaborator_elab__def__like(x_0, x_41, x_62, x_63, x_1, x_2);
x_5 = x_64;
goto lbl_6;
}
case 2:
{
obj* x_65; obj* x_68; obj* x_71; obj* x_72; obj* x_74; obj* x_76; obj* x_79; obj* x_80; obj* x_81; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_65 = lean::cnstr_get(x_13, 0);
lean::inc(x_65);
lean::dec(x_13);
x_68 = lean::cnstr_get(x_12, 0);
lean::inc(x_68);
lean::dec(x_12);
x_71 = lean::box(0);
x_72 = lean::cnstr_get(x_65, 1);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_72, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_72, 1);
lean::inc(x_76);
lean::dec(x_72);
x_79 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_79, 0, x_76);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_74);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::cnstr_get(x_65, 2);
lean::inc(x_81);
lean::dec(x_65);
x_84 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
x_85 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
x_86 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_71);
lean::cnstr_set(x_86, 2, x_85);
lean::cnstr_set(x_86, 3, x_80);
lean::cnstr_set(x_86, 4, x_81);
x_87 = lean::mk_nat_obj(2u);
x_88 = l_lean_elaborator_elab__def__like(x_0, x_68, x_86, x_87, x_1, x_2);
x_5 = x_88;
goto lbl_6;
}
case 3:
{
obj* x_89; obj* x_92; obj* x_94; 
x_89 = lean::cnstr_get(x_13, 0);
lean::inc(x_89);
lean::dec(x_13);
x_92 = lean::cnstr_get(x_89, 2);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_92, 0);
lean::inc(x_94);
if (lean::obj_tag(x_94) == 0)
{
obj* x_100; obj* x_101; 
lean::dec(x_12);
lean::dec(x_92);
lean::dec(x_94);
lean::dec(x_89);
x_100 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_101 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_100, x_1, x_2);
x_5 = x_101;
goto lbl_6;
}
else
{
obj* x_102; 
x_102 = lean::cnstr_get(x_94, 0);
lean::inc(x_102);
lean::dec(x_94);
if (lean::obj_tag(x_102) == 0)
{
obj* x_105; obj* x_108; obj* x_111; obj* x_115; 
x_105 = lean::cnstr_get(x_89, 1);
lean::inc(x_105);
lean::dec(x_89);
x_108 = lean::cnstr_get(x_92, 1);
lean::inc(x_108);
lean::dec(x_92);
x_111 = lean::cnstr_get(x_12, 0);
lean::inc(x_111);
lean::dec(x_12);
lean::inc(x_1);
x_115 = l_lean_elaborator_decl__modifiers__to__pexpr(x_111, x_1, x_2);
if (lean::obj_tag(x_115) == 0)
{
obj* x_120; obj* x_122; obj* x_123; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_105);
lean::dec(x_108);
x_120 = lean::cnstr_get(x_115, 0);
if (lean::is_exclusive(x_115)) {
 x_122 = x_115;
} else {
 lean::inc(x_120);
 lean::dec(x_115);
 x_122 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_120);
x_5 = x_123;
goto lbl_6;
}
else
{
obj* x_124; obj* x_127; obj* x_129; obj* x_132; obj* x_136; 
x_124 = lean::cnstr_get(x_115, 0);
lean::inc(x_124);
lean::dec(x_115);
x_127 = lean::cnstr_get(x_124, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_124, 1);
lean::inc(x_129);
lean::dec(x_124);
x_132 = lean::cnstr_get(x_108, 1);
lean::inc(x_132);
lean::dec(x_108);
lean::inc(x_1);
x_136 = l_lean_elaborator_to__pexpr___main(x_132, x_1, x_129);
if (lean::obj_tag(x_136) == 0)
{
obj* x_141; obj* x_143; obj* x_144; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_127);
lean::dec(x_105);
x_141 = lean::cnstr_get(x_136, 0);
if (lean::is_exclusive(x_136)) {
 x_143 = x_136;
} else {
 lean::inc(x_141);
 lean::dec(x_136);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_141);
x_5 = x_144;
goto lbl_6;
}
else
{
obj* x_145; obj* x_148; obj* x_150; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
x_145 = lean::cnstr_get(x_136, 0);
lean::inc(x_145);
lean::dec(x_136);
x_148 = lean::cnstr_get(x_145, 0);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_145, 1);
lean::inc(x_150);
lean::dec(x_145);
x_153 = lean::box(0);
x_154 = l_lean_elaborator_ident__univ__params__to__pexpr(x_105);
x_155 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_155, 0, x_148);
lean::cnstr_set(x_155, 1, x_153);
x_156 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_156, 0, x_154);
lean::cnstr_set(x_156, 1, x_155);
x_157 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_157, 0, x_127);
lean::cnstr_set(x_157, 1, x_156);
x_158 = l_lean_elaborator_mk__eqns___closed__1;
x_159 = l_lean_expr_mk__capp(x_158, x_157);
x_160 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3;
x_161 = lean_expr_mk_mdata(x_160, x_159);
x_162 = l_lean_elaborator_old__elab__command(x_0, x_161, x_1, x_150);
x_5 = x_162;
goto lbl_6;
}
}
}
else
{
obj* x_167; obj* x_168; 
lean::dec(x_12);
lean::dec(x_92);
lean::dec(x_102);
lean::dec(x_89);
x_167 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_168 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_167, x_1, x_2);
x_5 = x_168;
goto lbl_6;
}
}
}
case 4:
{
obj* x_169; obj* x_172; 
x_169 = lean::cnstr_get(x_13, 0);
lean::inc(x_169);
lean::dec(x_13);
x_172 = lean::cnstr_get(x_169, 0);
lean::inc(x_172);
if (lean::obj_tag(x_172) == 0)
{
obj* x_174; obj* x_176; 
x_174 = lean::cnstr_get(x_169, 4);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_174, 0);
lean::inc(x_176);
if (lean::obj_tag(x_176) == 0)
{
obj* x_182; obj* x_183; 
lean::dec(x_176);
lean::dec(x_174);
lean::dec(x_169);
lean::dec(x_12);
x_182 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_183 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_182, x_1, x_2);
x_5 = x_183;
goto lbl_6;
}
else
{
obj* x_184; obj* x_186; obj* x_188; obj* x_191; obj* x_194; obj* x_197; obj* x_202; 
x_184 = lean::cnstr_get(x_169, 2);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_169, 3);
lean::inc(x_186);
x_188 = lean::cnstr_get(x_169, 6);
lean::inc(x_188);
lean::dec(x_169);
x_191 = lean::cnstr_get(x_174, 1);
lean::inc(x_191);
lean::dec(x_174);
x_194 = lean::cnstr_get(x_176, 0);
lean::inc(x_194);
lean::dec(x_176);
x_197 = lean::cnstr_get(x_12, 0);
lean::inc(x_197);
lean::dec(x_12);
lean::inc(x_1);
lean::inc(x_197);
x_202 = l_lean_elaborator_decl__modifiers__to__pexpr(x_197, x_1, x_2);
if (lean::obj_tag(x_202) == 0)
{
obj* x_211; obj* x_213; obj* x_214; 
lean::dec(x_197);
lean::dec(x_191);
lean::dec(x_188);
lean::dec(x_194);
lean::dec(x_186);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_184);
x_211 = lean::cnstr_get(x_202, 0);
if (lean::is_exclusive(x_202)) {
 x_213 = x_202;
} else {
 lean::inc(x_211);
 lean::dec(x_202);
 x_213 = lean::box(0);
}
if (lean::is_scalar(x_213)) {
 x_214 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_214 = x_213;
}
lean::cnstr_set(x_214, 0, x_211);
x_5 = x_214;
goto lbl_6;
}
else
{
obj* x_215; obj* x_218; obj* x_220; obj* x_223; obj* x_224; obj* x_226; 
x_215 = lean::cnstr_get(x_202, 0);
lean::inc(x_215);
lean::dec(x_202);
x_218 = lean::cnstr_get(x_215, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_215, 1);
lean::inc(x_220);
lean::dec(x_215);
x_223 = lean::box(0);
x_226 = lean::cnstr_get(x_197, 1);
lean::inc(x_226);
lean::dec(x_197);
if (lean::obj_tag(x_226) == 0)
{
x_224 = x_223;
goto lbl_225;
}
else
{
obj* x_229; obj* x_232; 
x_229 = lean::cnstr_get(x_226, 0);
lean::inc(x_229);
lean::dec(x_226);
x_232 = lean::cnstr_get(x_229, 1);
lean::inc(x_232);
lean::dec(x_229);
x_224 = x_232;
goto lbl_225;
}
lbl_225:
{
obj* x_236; 
lean::inc(x_1);
x_236 = l_lean_elaborator_attrs__to__pexpr(x_224, x_1, x_220);
if (lean::obj_tag(x_236) == 0)
{
obj* x_245; obj* x_247; obj* x_248; 
lean::dec(x_191);
lean::dec(x_188);
lean::dec(x_194);
lean::dec(x_186);
lean::dec(x_218);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_184);
x_245 = lean::cnstr_get(x_236, 0);
if (lean::is_exclusive(x_236)) {
 x_247 = x_236;
} else {
 lean::inc(x_245);
 lean::dec(x_236);
 x_247 = lean::box(0);
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_245);
x_5 = x_248;
goto lbl_6;
}
else
{
obj* x_249; obj* x_252; obj* x_254; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; 
x_249 = lean::cnstr_get(x_236, 0);
lean::inc(x_249);
lean::dec(x_236);
x_252 = lean::cnstr_get(x_249, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_249, 1);
lean::inc(x_254);
lean::dec(x_249);
x_257 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_257, 0, x_252);
lean::cnstr_set(x_257, 1, x_223);
x_258 = l_lean_elaborator_mk__eqns___closed__1;
x_259 = l_lean_expr_mk__capp(x_258, x_257);
if (lean::obj_tag(x_184) == 0)
{
obj* x_263; obj* x_265; 
x_263 = l_lean_expander_get__opt__type___main(x_191);
lean::inc(x_1);
x_265 = l_lean_elaborator_to__pexpr___main(x_263, x_1, x_254);
if (lean::obj_tag(x_184) == 0)
{
if (lean::obj_tag(x_265) == 0)
{
obj* x_273; obj* x_275; obj* x_276; 
lean::dec(x_188);
lean::dec(x_194);
lean::dec(x_186);
lean::dec(x_218);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_259);
x_273 = lean::cnstr_get(x_265, 0);
if (lean::is_exclusive(x_265)) {
 x_275 = x_265;
} else {
 lean::inc(x_273);
 lean::dec(x_265);
 x_275 = lean::box(0);
}
if (lean::is_scalar(x_275)) {
 x_276 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_276 = x_275;
}
lean::cnstr_set(x_276, 0, x_273);
x_5 = x_276;
goto lbl_6;
}
else
{
obj* x_277; 
x_277 = lean::cnstr_get(x_265, 0);
lean::inc(x_277);
lean::dec(x_265);
x_260 = x_223;
x_261 = x_277;
goto lbl_262;
}
}
else
{
if (lean::obj_tag(x_265) == 0)
{
obj* x_287; obj* x_289; obj* x_290; 
lean::dec(x_188);
lean::dec(x_194);
lean::dec(x_186);
lean::dec(x_218);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_259);
x_287 = lean::cnstr_get(x_265, 0);
if (lean::is_exclusive(x_265)) {
 x_289 = x_265;
} else {
 lean::inc(x_287);
 lean::dec(x_265);
 x_289 = lean::box(0);
}
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_287);
x_5 = x_290;
goto lbl_6;
}
else
{
obj* x_291; obj* x_294; obj* x_297; obj* x_300; 
x_291 = lean::cnstr_get(x_184, 0);
lean::inc(x_291);
lean::dec(x_184);
x_294 = lean::cnstr_get(x_265, 0);
lean::inc(x_294);
lean::dec(x_265);
x_297 = lean::cnstr_get(x_291, 1);
lean::inc(x_297);
lean::dec(x_291);
x_300 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_297);
x_260 = x_300;
x_261 = x_294;
goto lbl_262;
}
}
}
else
{
obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_311; obj* x_313; obj* x_315; obj* x_317; obj* x_321; obj* x_322; obj* x_323; obj* x_325; obj* x_327; obj* x_329; obj* x_331; obj* x_334; obj* x_335; obj* x_337; obj* x_339; obj* x_341; obj* x_343; obj* x_345; obj* x_348; obj* x_349; obj* x_351; 
x_301 = lean::cnstr_get(x_184, 0);
lean::inc(x_301);
x_303 = lean::cnstr_get(x_254, 0);
lean::inc(x_303);
x_305 = lean::cnstr_get(x_254, 1);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_254, 2);
lean::inc(x_307);
x_309 = lean::cnstr_get(x_254, 3);
lean::inc(x_309);
x_311 = lean::cnstr_get(x_254, 4);
lean::inc(x_311);
x_313 = lean::cnstr_get(x_311, 0);
lean::inc(x_313);
x_315 = lean::cnstr_get(x_311, 1);
lean::inc(x_315);
x_317 = lean::cnstr_get(x_301, 1);
lean::inc(x_317);
lean::dec(x_301);
lean::inc(x_317);
x_321 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(x_317);
x_322 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__5(x_315, x_321);
x_323 = lean::cnstr_get(x_311, 2);
lean::inc(x_323);
x_325 = lean::cnstr_get(x_311, 3);
lean::inc(x_325);
x_327 = lean::cnstr_get(x_311, 4);
lean::inc(x_327);
x_329 = lean::cnstr_get(x_311, 5);
lean::inc(x_329);
x_331 = lean::cnstr_get(x_311, 6);
lean::inc(x_331);
lean::dec(x_311);
x_334 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_334, 0, x_313);
lean::cnstr_set(x_334, 1, x_322);
lean::cnstr_set(x_334, 2, x_323);
lean::cnstr_set(x_334, 3, x_325);
lean::cnstr_set(x_334, 4, x_327);
lean::cnstr_set(x_334, 5, x_329);
lean::cnstr_set(x_334, 6, x_331);
x_335 = lean::cnstr_get(x_254, 5);
lean::inc(x_335);
x_337 = lean::cnstr_get(x_254, 6);
lean::inc(x_337);
x_339 = lean::cnstr_get(x_254, 7);
lean::inc(x_339);
x_341 = lean::cnstr_get(x_254, 8);
lean::inc(x_341);
x_343 = lean::cnstr_get(x_254, 9);
lean::inc(x_343);
x_345 = lean::cnstr_get(x_254, 10);
lean::inc(x_345);
lean::dec(x_254);
x_348 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_348, 0, x_303);
lean::cnstr_set(x_348, 1, x_305);
lean::cnstr_set(x_348, 2, x_307);
lean::cnstr_set(x_348, 3, x_309);
lean::cnstr_set(x_348, 4, x_334);
lean::cnstr_set(x_348, 5, x_335);
lean::cnstr_set(x_348, 6, x_337);
lean::cnstr_set(x_348, 7, x_339);
lean::cnstr_set(x_348, 8, x_341);
lean::cnstr_set(x_348, 9, x_343);
lean::cnstr_set(x_348, 10, x_345);
x_349 = l_lean_expander_get__opt__type___main(x_191);
lean::inc(x_1);
x_351 = l_lean_elaborator_to__pexpr___main(x_349, x_1, x_348);
if (lean::obj_tag(x_184) == 0)
{
lean::dec(x_317);
if (lean::obj_tag(x_351) == 0)
{
obj* x_360; obj* x_362; obj* x_363; 
lean::dec(x_188);
lean::dec(x_194);
lean::dec(x_186);
lean::dec(x_218);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_259);
x_360 = lean::cnstr_get(x_351, 0);
if (lean::is_exclusive(x_351)) {
 x_362 = x_351;
} else {
 lean::inc(x_360);
 lean::dec(x_351);
 x_362 = lean::box(0);
}
if (lean::is_scalar(x_362)) {
 x_363 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_363 = x_362;
}
lean::cnstr_set(x_363, 0, x_360);
x_5 = x_363;
goto lbl_6;
}
else
{
obj* x_364; 
x_364 = lean::cnstr_get(x_351, 0);
lean::inc(x_364);
lean::dec(x_351);
x_260 = x_223;
x_261 = x_364;
goto lbl_262;
}
}
else
{
lean::dec(x_184);
if (lean::obj_tag(x_351) == 0)
{
obj* x_376; obj* x_378; obj* x_379; 
lean::dec(x_188);
lean::dec(x_194);
lean::dec(x_186);
lean::dec(x_218);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_259);
lean::dec(x_317);
x_376 = lean::cnstr_get(x_351, 0);
if (lean::is_exclusive(x_351)) {
 x_378 = x_351;
} else {
 lean::inc(x_376);
 lean::dec(x_351);
 x_378 = lean::box(0);
}
if (lean::is_scalar(x_378)) {
 x_379 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_379 = x_378;
}
lean::cnstr_set(x_379, 0, x_376);
x_5 = x_379;
goto lbl_6;
}
else
{
obj* x_380; obj* x_383; 
x_380 = lean::cnstr_get(x_351, 0);
lean::inc(x_380);
lean::dec(x_351);
x_383 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(x_317);
x_260 = x_383;
x_261 = x_380;
goto lbl_262;
}
}
}
lbl_262:
{
obj* x_384; obj* x_386; obj* x_390; 
x_384 = lean::cnstr_get(x_261, 0);
lean::inc(x_384);
x_386 = lean::cnstr_get(x_261, 1);
lean::inc(x_386);
lean::dec(x_261);
lean::inc(x_1);
x_390 = l_lean_elaborator_simple__binders__to__pexpr(x_194, x_1, x_386);
if (lean::obj_tag(x_390) == 0)
{
obj* x_399; obj* x_401; obj* x_402; 
lean::dec(x_188);
lean::dec(x_186);
lean::dec(x_218);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_259);
lean::dec(x_260);
lean::dec(x_384);
x_399 = lean::cnstr_get(x_390, 0);
if (lean::is_exclusive(x_390)) {
 x_401 = x_390;
} else {
 lean::inc(x_399);
 lean::dec(x_390);
 x_401 = lean::box(0);
}
if (lean::is_scalar(x_401)) {
 x_402 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_402 = x_401;
}
lean::cnstr_set(x_402, 0, x_399);
x_5 = x_402;
goto lbl_6;
}
else
{
obj* x_403; obj* x_406; obj* x_408; obj* x_414; 
x_403 = lean::cnstr_get(x_390, 0);
lean::inc(x_403);
lean::dec(x_390);
x_406 = lean::cnstr_get(x_403, 0);
lean::inc(x_406);
x_408 = lean::cnstr_get(x_403, 1);
lean::inc(x_408);
lean::dec(x_403);
lean::inc(x_1);
lean::inc(x_188);
lean::inc(x_0);
x_414 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_188, x_1, x_408);
if (lean::obj_tag(x_414) == 0)
{
obj* x_424; obj* x_426; obj* x_427; 
lean::dec(x_188);
lean::dec(x_186);
lean::dec(x_218);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_259);
lean::dec(x_406);
lean::dec(x_260);
lean::dec(x_384);
x_424 = lean::cnstr_get(x_414, 0);
if (lean::is_exclusive(x_414)) {
 x_426 = x_414;
} else {
 lean::inc(x_424);
 lean::dec(x_414);
 x_426 = lean::box(0);
}
if (lean::is_scalar(x_426)) {
 x_427 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_427 = x_426;
}
lean::cnstr_set(x_427, 0, x_424);
x_5 = x_427;
goto lbl_6;
}
else
{
obj* x_428; obj* x_431; obj* x_433; obj* x_436; obj* x_437; obj* x_440; uint8 x_441; obj* x_443; obj* x_444; obj* x_445; obj* x_446; obj* x_447; obj* x_448; obj* x_449; obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; 
x_428 = lean::cnstr_get(x_414, 0);
lean::inc(x_428);
lean::dec(x_414);
x_431 = lean::cnstr_get(x_428, 0);
lean::inc(x_431);
x_433 = lean::cnstr_get(x_428, 1);
lean::inc(x_433);
lean::dec(x_428);
x_436 = l_lean_elaborator_names__to__pexpr(x_260);
x_437 = lean::cnstr_get(x_186, 0);
lean::inc(x_437);
lean::dec(x_186);
x_440 = l_lean_elaborator_mangle__ident(x_437);
x_441 = 0;
lean::inc(x_440);
x_443 = lean_expr_local(x_440, x_440, x_384, x_441);
x_444 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_444, 0, x_443);
lean::cnstr_set(x_444, 1, x_223);
x_445 = l_lean_expr_mk__capp(x_258, x_444);
x_446 = l_lean_expr_mk__capp(x_258, x_431);
x_447 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_447, 0, x_446);
lean::cnstr_set(x_447, 1, x_223);
x_448 = l_lean_expr_mk__capp(x_258, x_447);
x_449 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(x_188);
x_450 = l_lean_expr_mk__capp(x_258, x_449);
x_451 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_451, 0, x_450);
lean::cnstr_set(x_451, 1, x_223);
x_452 = l_lean_expr_mk__capp(x_258, x_451);
x_453 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_453, 0, x_452);
lean::cnstr_set(x_453, 1, x_223);
x_454 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_454, 0, x_448);
lean::cnstr_set(x_454, 1, x_453);
x_455 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_455, 0, x_406);
lean::cnstr_set(x_455, 1, x_454);
x_456 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_456, 0, x_445);
lean::cnstr_set(x_456, 1, x_455);
x_457 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_457, 0, x_436);
lean::cnstr_set(x_457, 1, x_456);
x_458 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_458, 0, x_259);
lean::cnstr_set(x_458, 1, x_457);
x_459 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_459, 0, x_218);
lean::cnstr_set(x_459, 1, x_458);
x_460 = l_lean_expr_mk__capp(x_258, x_459);
x_461 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
x_462 = lean_expr_mk_mdata(x_461, x_460);
x_463 = l_lean_elaborator_old__elab__command(x_0, x_462, x_1, x_433);
x_5 = x_463;
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
obj* x_467; obj* x_468; 
lean::dec(x_172);
lean::dec(x_169);
lean::dec(x_12);
x_467 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_468 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_467, x_1, x_2);
x_5 = x_468;
goto lbl_6;
}
}
default:
{
obj* x_469; obj* x_472; 
x_469 = lean::cnstr_get(x_13, 0);
lean::inc(x_469);
lean::dec(x_13);
x_472 = lean::cnstr_get(x_469, 0);
lean::inc(x_472);
if (lean::obj_tag(x_472) == 0)
{
obj* x_475; obj* x_477; 
lean::dec(x_472);
x_475 = lean::cnstr_get(x_469, 3);
lean::inc(x_475);
x_477 = lean::cnstr_get(x_475, 0);
lean::inc(x_477);
if (lean::obj_tag(x_477) == 0)
{
obj* x_483; obj* x_484; 
lean::dec(x_469);
lean::dec(x_12);
lean::dec(x_477);
lean::dec(x_475);
x_483 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_484 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_483, x_1, x_2);
x_5 = x_484;
goto lbl_6;
}
else
{
obj* x_485; obj* x_487; obj* x_489; obj* x_491; obj* x_493; obj* x_496; obj* x_499; obj* x_502; obj* x_506; 
x_485 = lean::cnstr_get(x_469, 1);
lean::inc(x_485);
x_487 = lean::cnstr_get(x_469, 2);
lean::inc(x_487);
x_489 = lean::cnstr_get(x_469, 4);
lean::inc(x_489);
x_491 = lean::cnstr_get(x_469, 6);
lean::inc(x_491);
x_493 = lean::cnstr_get(x_469, 7);
lean::inc(x_493);
lean::dec(x_469);
x_496 = lean::cnstr_get(x_475, 1);
lean::inc(x_496);
lean::dec(x_475);
x_499 = lean::cnstr_get(x_477, 0);
lean::inc(x_499);
lean::dec(x_477);
x_502 = lean::cnstr_get(x_12, 0);
lean::inc(x_502);
lean::dec(x_12);
lean::inc(x_1);
x_506 = l_lean_elaborator_decl__modifiers__to__pexpr(x_502, x_1, x_2);
if (lean::obj_tag(x_506) == 0)
{
obj* x_516; obj* x_518; obj* x_519; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_499);
lean::dec(x_491);
lean::dec(x_489);
lean::dec(x_496);
lean::dec(x_493);
lean::dec(x_487);
lean::dec(x_485);
x_516 = lean::cnstr_get(x_506, 0);
if (lean::is_exclusive(x_506)) {
 x_518 = x_506;
} else {
 lean::inc(x_516);
 lean::dec(x_506);
 x_518 = lean::box(0);
}
if (lean::is_scalar(x_518)) {
 x_519 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_519 = x_518;
}
lean::cnstr_set(x_519, 0, x_516);
x_5 = x_519;
goto lbl_6;
}
else
{
obj* x_520; obj* x_523; obj* x_525; obj* x_528; obj* x_529; obj* x_530; 
x_520 = lean::cnstr_get(x_506, 0);
lean::inc(x_520);
lean::dec(x_506);
x_523 = lean::cnstr_get(x_520, 0);
lean::inc(x_523);
x_525 = lean::cnstr_get(x_520, 1);
lean::inc(x_525);
lean::dec(x_520);
x_528 = lean::box(0);
if (lean::obj_tag(x_485) == 0)
{
obj* x_532; obj* x_534; 
x_532 = l_lean_expander_get__opt__type___main(x_496);
lean::inc(x_1);
x_534 = l_lean_elaborator_to__pexpr___main(x_532, x_1, x_525);
if (lean::obj_tag(x_485) == 0)
{
if (lean::obj_tag(x_534) == 0)
{
obj* x_543; obj* x_545; obj* x_546; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_499);
lean::dec(x_491);
lean::dec(x_489);
lean::dec(x_493);
lean::dec(x_487);
lean::dec(x_523);
x_543 = lean::cnstr_get(x_534, 0);
if (lean::is_exclusive(x_534)) {
 x_545 = x_534;
} else {
 lean::inc(x_543);
 lean::dec(x_534);
 x_545 = lean::box(0);
}
if (lean::is_scalar(x_545)) {
 x_546 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_546 = x_545;
}
lean::cnstr_set(x_546, 0, x_543);
x_5 = x_546;
goto lbl_6;
}
else
{
obj* x_547; 
x_547 = lean::cnstr_get(x_534, 0);
lean::inc(x_547);
lean::dec(x_534);
x_529 = x_528;
x_530 = x_547;
goto lbl_531;
}
}
else
{
if (lean::obj_tag(x_534) == 0)
{
obj* x_558; obj* x_560; obj* x_561; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_499);
lean::dec(x_491);
lean::dec(x_489);
lean::dec(x_493);
lean::dec(x_487);
lean::dec(x_523);
x_558 = lean::cnstr_get(x_534, 0);
if (lean::is_exclusive(x_534)) {
 x_560 = x_534;
} else {
 lean::inc(x_558);
 lean::dec(x_534);
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
obj* x_562; obj* x_565; obj* x_568; obj* x_571; 
x_562 = lean::cnstr_get(x_485, 0);
lean::inc(x_562);
lean::dec(x_485);
x_565 = lean::cnstr_get(x_534, 0);
lean::inc(x_565);
lean::dec(x_534);
x_568 = lean::cnstr_get(x_562, 1);
lean::inc(x_568);
lean::dec(x_562);
x_571 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(x_568);
x_529 = x_571;
x_530 = x_565;
goto lbl_531;
}
}
}
else
{
obj* x_572; obj* x_574; obj* x_576; obj* x_578; obj* x_580; obj* x_582; obj* x_584; obj* x_586; obj* x_588; obj* x_592; obj* x_593; obj* x_594; obj* x_596; obj* x_598; obj* x_600; obj* x_602; obj* x_605; obj* x_606; obj* x_608; obj* x_610; obj* x_612; obj* x_614; obj* x_616; obj* x_619; obj* x_620; obj* x_622; 
x_572 = lean::cnstr_get(x_485, 0);
lean::inc(x_572);
x_574 = lean::cnstr_get(x_525, 0);
lean::inc(x_574);
x_576 = lean::cnstr_get(x_525, 1);
lean::inc(x_576);
x_578 = lean::cnstr_get(x_525, 2);
lean::inc(x_578);
x_580 = lean::cnstr_get(x_525, 3);
lean::inc(x_580);
x_582 = lean::cnstr_get(x_525, 4);
lean::inc(x_582);
x_584 = lean::cnstr_get(x_582, 0);
lean::inc(x_584);
x_586 = lean::cnstr_get(x_582, 1);
lean::inc(x_586);
x_588 = lean::cnstr_get(x_572, 1);
lean::inc(x_588);
lean::dec(x_572);
lean::inc(x_588);
x_592 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(x_588);
x_593 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(x_586, x_592);
x_594 = lean::cnstr_get(x_582, 2);
lean::inc(x_594);
x_596 = lean::cnstr_get(x_582, 3);
lean::inc(x_596);
x_598 = lean::cnstr_get(x_582, 4);
lean::inc(x_598);
x_600 = lean::cnstr_get(x_582, 5);
lean::inc(x_600);
x_602 = lean::cnstr_get(x_582, 6);
lean::inc(x_602);
lean::dec(x_582);
x_605 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_605, 0, x_584);
lean::cnstr_set(x_605, 1, x_593);
lean::cnstr_set(x_605, 2, x_594);
lean::cnstr_set(x_605, 3, x_596);
lean::cnstr_set(x_605, 4, x_598);
lean::cnstr_set(x_605, 5, x_600);
lean::cnstr_set(x_605, 6, x_602);
x_606 = lean::cnstr_get(x_525, 5);
lean::inc(x_606);
x_608 = lean::cnstr_get(x_525, 6);
lean::inc(x_608);
x_610 = lean::cnstr_get(x_525, 7);
lean::inc(x_610);
x_612 = lean::cnstr_get(x_525, 8);
lean::inc(x_612);
x_614 = lean::cnstr_get(x_525, 9);
lean::inc(x_614);
x_616 = lean::cnstr_get(x_525, 10);
lean::inc(x_616);
lean::dec(x_525);
x_619 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_619, 0, x_574);
lean::cnstr_set(x_619, 1, x_576);
lean::cnstr_set(x_619, 2, x_578);
lean::cnstr_set(x_619, 3, x_580);
lean::cnstr_set(x_619, 4, x_605);
lean::cnstr_set(x_619, 5, x_606);
lean::cnstr_set(x_619, 6, x_608);
lean::cnstr_set(x_619, 7, x_610);
lean::cnstr_set(x_619, 8, x_612);
lean::cnstr_set(x_619, 9, x_614);
lean::cnstr_set(x_619, 10, x_616);
x_620 = l_lean_expander_get__opt__type___main(x_496);
lean::inc(x_1);
x_622 = l_lean_elaborator_to__pexpr___main(x_620, x_1, x_619);
if (lean::obj_tag(x_485) == 0)
{
lean::dec(x_588);
if (lean::obj_tag(x_622) == 0)
{
obj* x_632; obj* x_634; obj* x_635; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_499);
lean::dec(x_491);
lean::dec(x_489);
lean::dec(x_493);
lean::dec(x_487);
lean::dec(x_523);
x_632 = lean::cnstr_get(x_622, 0);
if (lean::is_exclusive(x_622)) {
 x_634 = x_622;
} else {
 lean::inc(x_632);
 lean::dec(x_622);
 x_634 = lean::box(0);
}
if (lean::is_scalar(x_634)) {
 x_635 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_635 = x_634;
}
lean::cnstr_set(x_635, 0, x_632);
x_5 = x_635;
goto lbl_6;
}
else
{
obj* x_636; 
x_636 = lean::cnstr_get(x_622, 0);
lean::inc(x_636);
lean::dec(x_622);
x_529 = x_528;
x_530 = x_636;
goto lbl_531;
}
}
else
{
lean::dec(x_485);
if (lean::obj_tag(x_622) == 0)
{
obj* x_649; obj* x_651; obj* x_652; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_499);
lean::dec(x_491);
lean::dec(x_489);
lean::dec(x_493);
lean::dec(x_487);
lean::dec(x_523);
lean::dec(x_588);
x_649 = lean::cnstr_get(x_622, 0);
if (lean::is_exclusive(x_622)) {
 x_651 = x_622;
} else {
 lean::inc(x_649);
 lean::dec(x_622);
 x_651 = lean::box(0);
}
if (lean::is_scalar(x_651)) {
 x_652 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_652 = x_651;
}
lean::cnstr_set(x_652, 0, x_649);
x_5 = x_652;
goto lbl_6;
}
else
{
obj* x_653; obj* x_656; 
x_653 = lean::cnstr_get(x_622, 0);
lean::inc(x_653);
lean::dec(x_622);
x_656 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(x_588);
x_529 = x_656;
x_530 = x_653;
goto lbl_531;
}
}
}
lbl_531:
{
obj* x_657; obj* x_659; obj* x_663; 
x_657 = lean::cnstr_get(x_530, 0);
lean::inc(x_657);
x_659 = lean::cnstr_get(x_530, 1);
lean::inc(x_659);
lean::dec(x_530);
lean::inc(x_1);
x_663 = l_lean_elaborator_simple__binders__to__pexpr(x_499, x_1, x_659);
if (lean::obj_tag(x_663) == 0)
{
obj* x_673; obj* x_675; obj* x_676; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_491);
lean::dec(x_489);
lean::dec(x_493);
lean::dec(x_487);
lean::dec(x_523);
lean::dec(x_529);
lean::dec(x_657);
x_673 = lean::cnstr_get(x_663, 0);
if (lean::is_exclusive(x_663)) {
 x_675 = x_663;
} else {
 lean::inc(x_673);
 lean::dec(x_663);
 x_675 = lean::box(0);
}
if (lean::is_scalar(x_675)) {
 x_676 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_676 = x_675;
}
lean::cnstr_set(x_676, 0, x_673);
x_5 = x_676;
goto lbl_6;
}
else
{
obj* x_677; obj* x_680; obj* x_682; obj* x_685; obj* x_686; obj* x_689; obj* x_690; uint8 x_691; obj* x_693; obj* x_694; 
x_677 = lean::cnstr_get(x_663, 0);
lean::inc(x_677);
lean::dec(x_663);
x_680 = lean::cnstr_get(x_677, 0);
lean::inc(x_680);
x_682 = lean::cnstr_get(x_677, 1);
lean::inc(x_682);
lean::dec(x_677);
x_685 = l_lean_elaborator_names__to__pexpr(x_529);
x_686 = lean::cnstr_get(x_487, 0);
lean::inc(x_686);
lean::dec(x_487);
x_689 = l_lean_elaborator_mangle__ident(x_686);
x_690 = l_lean_elaborator_dummy;
x_691 = 0;
lean::inc(x_689);
x_693 = lean_expr_local(x_689, x_689, x_690, x_691);
if (lean::obj_tag(x_489) == 0)
{
x_694 = x_528;
goto lbl_695;
}
else
{
obj* x_696; obj* x_699; 
x_696 = lean::cnstr_get(x_489, 0);
lean::inc(x_696);
lean::dec(x_489);
x_699 = lean::cnstr_get(x_696, 1);
lean::inc(x_699);
lean::dec(x_696);
x_694 = x_699;
goto lbl_695;
}
lbl_695:
{
obj* x_703; 
lean::inc(x_1);
x_703 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_694, x_1, x_682);
if (lean::obj_tag(x_703) == 0)
{
obj* x_713; obj* x_715; obj* x_716; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_491);
lean::dec(x_493);
lean::dec(x_523);
lean::dec(x_680);
lean::dec(x_685);
lean::dec(x_693);
lean::dec(x_657);
x_713 = lean::cnstr_get(x_703, 0);
if (lean::is_exclusive(x_703)) {
 x_715 = x_703;
} else {
 lean::inc(x_713);
 lean::dec(x_703);
 x_715 = lean::box(0);
}
if (lean::is_scalar(x_715)) {
 x_716 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_716 = x_715;
}
lean::cnstr_set(x_716, 0, x_713);
x_5 = x_716;
goto lbl_6;
}
else
{
obj* x_717; obj* x_720; obj* x_722; obj* x_725; obj* x_726; obj* x_729; obj* x_730; 
x_717 = lean::cnstr_get(x_703, 0);
lean::inc(x_717);
lean::dec(x_703);
x_720 = lean::cnstr_get(x_717, 0);
lean::inc(x_720);
x_722 = lean::cnstr_get(x_717, 1);
lean::inc(x_722);
lean::dec(x_717);
x_725 = l_lean_elaborator_mk__eqns___closed__1;
x_726 = l_lean_expr_mk__capp(x_725, x_720);
lean::inc(x_1);
lean::inc(x_0);
x_729 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_493, x_1, x_722);
if (lean::obj_tag(x_491) == 0)
{
obj* x_732; 
x_732 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7;
x_730 = x_732;
goto lbl_731;
}
else
{
obj* x_733; obj* x_735; obj* x_738; 
x_733 = lean::cnstr_get(x_491, 0);
lean::inc(x_733);
x_735 = lean::cnstr_get(x_733, 0);
lean::inc(x_735);
lean::dec(x_733);
x_738 = l_lean_elaborator_mangle__ident(x_735);
x_730 = x_738;
goto lbl_731;
}
lbl_731:
{
obj* x_740; 
lean::inc(x_730);
x_740 = lean_expr_local(x_730, x_730, x_690, x_691);
if (lean::obj_tag(x_491) == 0)
{
if (lean::obj_tag(x_729) == 0)
{
obj* x_750; obj* x_752; obj* x_753; 
lean::dec(x_726);
lean::dec(x_740);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_523);
lean::dec(x_680);
lean::dec(x_685);
lean::dec(x_693);
lean::dec(x_657);
x_750 = lean::cnstr_get(x_729, 0);
if (lean::is_exclusive(x_729)) {
 x_752 = x_729;
} else {
 lean::inc(x_750);
 lean::dec(x_729);
 x_752 = lean::box(0);
}
if (lean::is_scalar(x_752)) {
 x_753 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_753 = x_752;
}
lean::cnstr_set(x_753, 0, x_750);
x_5 = x_753;
goto lbl_6;
}
else
{
obj* x_754; obj* x_757; obj* x_759; obj* x_762; obj* x_763; obj* x_764; obj* x_765; obj* x_766; obj* x_767; obj* x_768; obj* x_769; obj* x_770; obj* x_771; obj* x_772; obj* x_773; obj* x_774; obj* x_775; obj* x_776; 
x_754 = lean::cnstr_get(x_729, 0);
lean::inc(x_754);
lean::dec(x_729);
x_757 = lean::cnstr_get(x_754, 0);
lean::inc(x_757);
x_759 = lean::cnstr_get(x_754, 1);
lean::inc(x_759);
lean::dec(x_754);
x_762 = l_lean_expr_mk__capp(x_725, x_757);
x_763 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_763, 0, x_762);
lean::cnstr_set(x_763, 1, x_528);
x_764 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5;
x_765 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_765, 0, x_764);
lean::cnstr_set(x_765, 1, x_763);
x_766 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_766, 0, x_740);
lean::cnstr_set(x_766, 1, x_765);
x_767 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_767, 0, x_657);
lean::cnstr_set(x_767, 1, x_766);
x_768 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_768, 0, x_726);
lean::cnstr_set(x_768, 1, x_767);
x_769 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_769, 0, x_680);
lean::cnstr_set(x_769, 1, x_768);
x_770 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_770, 0, x_693);
lean::cnstr_set(x_770, 1, x_769);
x_771 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_771, 0, x_685);
lean::cnstr_set(x_771, 1, x_770);
x_772 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_772, 0, x_523);
lean::cnstr_set(x_772, 1, x_771);
x_773 = l_lean_expr_mk__capp(x_725, x_772);
x_774 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
x_775 = lean_expr_mk_mdata(x_774, x_773);
x_776 = l_lean_elaborator_old__elab__command(x_0, x_775, x_1, x_759);
x_5 = x_776;
goto lbl_6;
}
}
else
{
if (lean::obj_tag(x_729) == 0)
{
obj* x_787; obj* x_789; obj* x_790; 
lean::dec(x_726);
lean::dec(x_740);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_491);
lean::dec(x_523);
lean::dec(x_680);
lean::dec(x_685);
lean::dec(x_693);
lean::dec(x_657);
x_787 = lean::cnstr_get(x_729, 0);
if (lean::is_exclusive(x_729)) {
 x_789 = x_729;
} else {
 lean::inc(x_787);
 lean::dec(x_729);
 x_789 = lean::box(0);
}
if (lean::is_scalar(x_789)) {
 x_790 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_790 = x_789;
}
lean::cnstr_set(x_790, 0, x_787);
x_5 = x_790;
goto lbl_6;
}
else
{
obj* x_791; obj* x_794; obj* x_797; obj* x_799; obj* x_802; obj* x_805; obj* x_806; obj* x_807; obj* x_808; obj* x_809; obj* x_810; obj* x_811; obj* x_812; obj* x_813; obj* x_814; obj* x_815; obj* x_816; obj* x_817; obj* x_818; obj* x_819; 
x_791 = lean::cnstr_get(x_491, 0);
lean::inc(x_791);
lean::dec(x_491);
x_794 = lean::cnstr_get(x_729, 0);
lean::inc(x_794);
lean::dec(x_729);
x_797 = lean::cnstr_get(x_794, 0);
lean::inc(x_797);
x_799 = lean::cnstr_get(x_794, 1);
lean::inc(x_799);
lean::dec(x_794);
x_802 = lean::cnstr_get(x_791, 1);
lean::inc(x_802);
lean::dec(x_791);
x_805 = l_lean_elaborator_infer__mod__to__pexpr(x_802);
x_806 = l_lean_expr_mk__capp(x_725, x_797);
x_807 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_807, 0, x_806);
lean::cnstr_set(x_807, 1, x_528);
x_808 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_808, 0, x_805);
lean::cnstr_set(x_808, 1, x_807);
x_809 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_809, 0, x_740);
lean::cnstr_set(x_809, 1, x_808);
x_810 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_810, 0, x_657);
lean::cnstr_set(x_810, 1, x_809);
x_811 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_811, 0, x_726);
lean::cnstr_set(x_811, 1, x_810);
x_812 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_812, 0, x_680);
lean::cnstr_set(x_812, 1, x_811);
x_813 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_813, 0, x_693);
lean::cnstr_set(x_813, 1, x_812);
x_814 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_814, 0, x_685);
lean::cnstr_set(x_814, 1, x_813);
x_815 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_815, 0, x_523);
lean::cnstr_set(x_815, 1, x_814);
x_816 = l_lean_expr_mk__capp(x_725, x_815);
x_817 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
x_818 = lean_expr_mk_mdata(x_817, x_816);
x_819 = l_lean_elaborator_old__elab__command(x_0, x_818, x_1, x_799);
x_5 = x_819;
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
obj* x_823; obj* x_824; 
lean::dec(x_469);
lean::dec(x_472);
lean::dec(x_12);
x_823 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_824 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_823, x_1, x_2);
x_5 = x_824;
goto lbl_6;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_826; obj* x_828; obj* x_829; 
lean::dec(x_3);
x_826 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_828 = x_5;
} else {
 lean::inc(x_826);
 lean::dec(x_5);
 x_828 = lean::box(0);
}
if (lean::is_scalar(x_828)) {
 x_829 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_829 = x_828;
}
lean::cnstr_set(x_829, 0, x_826);
return x_829;
}
else
{
obj* x_830; obj* x_832; obj* x_833; obj* x_836; obj* x_838; obj* x_840; obj* x_842; obj* x_844; obj* x_846; obj* x_848; obj* x_850; obj* x_852; obj* x_854; obj* x_857; obj* x_858; obj* x_859; obj* x_860; 
x_830 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_832 = x_5;
} else {
 lean::inc(x_830);
 lean::dec(x_5);
 x_832 = lean::box(0);
}
x_833 = lean::cnstr_get(x_830, 1);
lean::inc(x_833);
lean::dec(x_830);
x_836 = lean::cnstr_get(x_833, 0);
lean::inc(x_836);
x_838 = lean::cnstr_get(x_833, 1);
lean::inc(x_838);
x_840 = lean::cnstr_get(x_833, 2);
lean::inc(x_840);
x_842 = lean::cnstr_get(x_833, 3);
lean::inc(x_842);
x_844 = lean::cnstr_get(x_833, 5);
lean::inc(x_844);
x_846 = lean::cnstr_get(x_833, 6);
lean::inc(x_846);
x_848 = lean::cnstr_get(x_833, 7);
lean::inc(x_848);
x_850 = lean::cnstr_get(x_833, 8);
lean::inc(x_850);
x_852 = lean::cnstr_get(x_833, 9);
lean::inc(x_852);
x_854 = lean::cnstr_get(x_833, 10);
lean::inc(x_854);
lean::dec(x_833);
x_857 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_857, 0, x_836);
lean::cnstr_set(x_857, 1, x_838);
lean::cnstr_set(x_857, 2, x_840);
lean::cnstr_set(x_857, 3, x_842);
lean::cnstr_set(x_857, 4, x_3);
lean::cnstr_set(x_857, 5, x_844);
lean::cnstr_set(x_857, 6, x_846);
lean::cnstr_set(x_857, 7, x_848);
lean::cnstr_set(x_857, 8, x_850);
lean::cnstr_set(x_857, 9, x_852);
lean::cnstr_set(x_857, 10, x_854);
x_858 = lean::box(0);
x_859 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_859, 0, x_858);
lean::cnstr_set(x_859, 1, x_857);
if (lean::is_scalar(x_832)) {
 x_860 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_860 = x_832;
}
lean::cnstr_set(x_860, 0, x_859);
return x_860;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_22; obj* x_25; obj* x_27; uint8 x_28; 
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
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
lean::dec(x_17);
x_27 = l_lean_expander_binding__annotation__update;
x_28 = l_lean_parser_syntax_is__of__kind___main(x_27, x_22);
if (x_28 == 0)
{
uint8 x_31; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_20);
x_31 = 1;
x_32 = lean::box(x_31);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_2);
x_11 = x_33;
goto lbl_12;
}
else
{
obj* x_34; 
x_34 = lean::box(0);
x_25 = x_34;
goto lbl_26;
}
lbl_12:
{
obj* x_35; obj* x_37; obj* x_40; 
x_35 = lean::cnstr_get(x_11, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_11, 1);
lean::inc(x_37);
lean::dec(x_11);
x_40 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_8, x_1, x_37);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_35);
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
uint8 x_48; 
x_48 = lean::unbox(x_35);
if (x_48 == 0)
{
obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_59; obj* x_60; 
lean::dec(x_6);
lean::dec(x_10);
x_51 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_53 = x_40;
} else {
 lean::inc(x_51);
 lean::dec(x_40);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_54);
lean::cnstr_set(x_59, 1, x_56);
if (lean::is_scalar(x_53)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_53;
}
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
else
{
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_69; obj* x_70; obj* x_71; 
x_61 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_63 = x_40;
} else {
 lean::inc(x_61);
 lean::dec(x_40);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
lean::dec(x_61);
if (lean::is_scalar(x_10)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_10;
}
lean::cnstr_set(x_69, 0, x_6);
lean::cnstr_set(x_69, 1, x_64);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_66);
if (lean::is_scalar(x_63)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_63;
}
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
}
}
lbl_26:
{
obj* x_73; obj* x_74; obj* x_76; obj* x_80; 
lean::dec(x_25);
x_73 = l_lean_elaborator_mangle__ident(x_20);
x_74 = lean::cnstr_get(x_2, 4);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_74, 2);
lean::inc(x_76);
lean::inc(x_73);
lean::inc(x_76);
x_80 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_76, x_73);
if (lean::obj_tag(x_80) == 0)
{
obj* x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_94; 
lean::dec(x_15);
lean::dec(x_74);
lean::dec(x_76);
x_84 = lean::box(0);
x_85 = l_lean_name_to__string___closed__1;
lean::inc(x_73);
x_87 = l_lean_name_to__string__with__sep___main(x_85, x_73);
x_88 = l_lean_parser_substring_of__string(x_87);
x_89 = lean::box(0);
x_90 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_90, 0, x_84);
lean::cnstr_set(x_90, 1, x_88);
lean::cnstr_set(x_90, 2, x_73);
lean::cnstr_set(x_90, 3, x_89);
lean::cnstr_set(x_90, 4, x_89);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
x_92 = l_string_join___closed__1;
lean::inc(x_1);
x_94 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_91, x_92, x_1, x_2);
if (lean::obj_tag(x_94) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_1);
x_99 = lean::cnstr_get(x_94, 0);
if (lean::is_exclusive(x_94)) {
 x_101 = x_94;
} else {
 lean::inc(x_99);
 lean::dec(x_94);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_99);
return x_102;
}
else
{
obj* x_103; obj* x_106; uint8 x_109; obj* x_110; obj* x_111; 
x_103 = lean::cnstr_get(x_94, 0);
lean::inc(x_103);
lean::dec(x_94);
x_106 = lean::cnstr_get(x_103, 1);
lean::inc(x_106);
lean::dec(x_103);
x_109 = 0;
x_110 = lean::box(x_109);
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_106);
x_11 = x_111;
goto lbl_12;
}
}
else
{
obj* x_112; obj* x_115; obj* x_118; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_135; uint8 x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_148; obj* x_149; obj* x_151; obj* x_153; obj* x_155; obj* x_157; obj* x_159; obj* x_162; uint8 x_163; obj* x_164; obj* x_165; 
x_112 = lean::cnstr_get(x_80, 0);
lean::inc(x_112);
lean::dec(x_80);
x_115 = lean::cnstr_get(x_112, 1);
lean::inc(x_115);
lean::dec(x_112);
x_118 = lean::cnstr_get(x_2, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_2, 1);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_2, 2);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_2, 3);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_74, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_74, 1);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_115, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_115, 1);
lean::inc(x_132);
lean::dec(x_115);
x_135 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_135, 0, x_130);
lean::cnstr_set(x_135, 1, x_132);
x_136 = lean::unbox(x_15);
lean::cnstr_set_scalar(x_135, sizeof(void*)*2, x_136);
x_137 = x_135;
x_138 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(x_76, x_73, x_137);
x_139 = lean::cnstr_get(x_74, 3);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_74, 4);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_74, 5);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_74, 6);
lean::inc(x_145);
lean::dec(x_74);
x_148 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_148, 0, x_126);
lean::cnstr_set(x_148, 1, x_128);
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
lean::cnstr_set(x_162, 0, x_118);
lean::cnstr_set(x_162, 1, x_120);
lean::cnstr_set(x_162, 2, x_122);
lean::cnstr_set(x_162, 3, x_124);
lean::cnstr_set(x_162, 4, x_148);
lean::cnstr_set(x_162, 5, x_149);
lean::cnstr_set(x_162, 6, x_151);
lean::cnstr_set(x_162, 7, x_153);
lean::cnstr_set(x_162, 8, x_155);
lean::cnstr_set(x_162, 9, x_157);
lean::cnstr_set(x_162, 10, x_159);
x_163 = 0;
x_164 = lean::box(x_163);
x_165 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("command");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("variables");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_lean_kvmap_set__name(x_0, x_3, x_5);
return x_6;
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
obj* x_23; obj* x_26; obj* x_28; obj* x_32; 
x_23 = lean::cnstr_get(x_16, 0);
lean::inc(x_23);
lean::dec(x_16);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
lean::dec(x_23);
lean::inc(x_1);
x_32 = l_lean_elaborator_simple__binders__to__pexpr(x_26, x_1, x_28);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_37 = x_32;
} else {
 lean::inc(x_35);
 lean::dec(x_32);
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
obj* x_39; obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_32, 0);
lean::inc(x_39);
lean::dec(x_32);
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
lean::dec(x_39);
x_47 = l_lean_elaborator_variables_elaborate___closed__2;
x_48 = lean_expr_mk_mdata(x_47, x_42);
x_49 = l_lean_elaborator_old__elab__command(x_0, x_48, x_1, x_44);
return x_49;
}
}
}
else
{
obj* x_50; obj* x_54; 
x_50 = lean::cnstr_get(x_9, 0);
lean::inc(x_50);
lean::dec(x_9);
lean::inc(x_1);
x_54 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_50, x_1, x_2);
if (lean::obj_tag(x_54) == 0)
{
obj* x_57; obj* x_59; obj* x_60; 
lean::dec(x_1);
lean::dec(x_0);
x_57 = lean::cnstr_get(x_54, 0);
if (lean::is_exclusive(x_54)) {
 x_59 = x_54;
} else {
 lean::inc(x_57);
 lean::dec(x_54);
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
obj* x_61; obj* x_64; obj* x_66; obj* x_70; 
x_61 = lean::cnstr_get(x_54, 0);
lean::inc(x_61);
lean::dec(x_54);
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
lean::dec(x_61);
lean::inc(x_1);
x_70 = l_lean_elaborator_simple__binders__to__pexpr(x_64, x_1, x_66);
if (lean::obj_tag(x_70) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_1);
lean::dec(x_0);
x_73 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_75 = x_70;
} else {
 lean::inc(x_73);
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
obj* x_77; obj* x_80; obj* x_82; obj* x_85; obj* x_86; obj* x_87; 
x_77 = lean::cnstr_get(x_70, 0);
lean::inc(x_77);
lean::dec(x_70);
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
lean::dec(x_77);
x_85 = l_lean_elaborator_variables_elaborate___closed__2;
x_86 = lean_expr_mk_mdata(x_85, x_80);
x_87 = l_lean_elaborator_old__elab__command(x_0, x_86, x_1, x_82);
return x_87;
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
obj* x_3; obj* x_4; obj* x_8; obj* x_9; 
x_3 = l_lean_parser_module_header_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
lean::inc(x_0);
x_8 = lean::apply_1(x_4, x_0);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_8);
x_12 = l_lean_elaborator_module_header_elaborate___closed__1;
x_13 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_12, x_1, x_2);
return x_13;
}
else
{
obj* x_15; 
lean::dec(x_9);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
lean::dec(x_8);
if (lean::obj_tag(x_15) == 0)
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
lean::dec(x_15);
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
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_13 = l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1;
return x_13;
}
else
{
obj* x_14; obj* x_17; obj* x_20; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_49; 
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_5, 3);
lean::inc(x_17);
lean::dec(x_5);
x_20 = lean::cnstr_get(x_8, 0);
lean::inc(x_20);
lean::dec(x_8);
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
x_34 = l_lean_elaborator_prec__to__nat___main(x_17);
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
x_1 = x_14;
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
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_7, 0);
lean::inc(x_35);
lean::dec(x_7);
x_38 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(x_4);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_6);
lean::dec(x_35);
x_41 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_43 = x_38;
} else {
 lean::inc(x_41);
 lean::dec(x_38);
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
obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_47 = x_38;
} else {
 lean::inc(x_45);
 lean::dec(x_38);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_6;
}
lean::cnstr_set(x_48, 0, x_35);
lean::cnstr_set(x_48, 1, x_45);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_47;
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
obj* x_56; 
x_56 = lean::cnstr_get(x_52, 0);
lean::inc(x_56);
lean::dec(x_52);
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_60; 
lean::dec(x_56);
x_60 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
x_50 = x_60;
goto lbl_51;
}
case 1:
{
obj* x_62; 
lean::dec(x_56);
x_62 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2;
x_50 = x_62;
goto lbl_51;
}
default:
{
obj* x_63; obj* x_66; 
x_63 = lean::cnstr_get(x_56, 0);
lean::inc(x_63);
lean::dec(x_56);
x_66 = lean::cnstr_get(x_63, 1);
lean::inc(x_66);
lean::dec(x_63);
if (lean::obj_tag(x_66) == 0)
{
obj* x_69; 
x_69 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3;
x_50 = x_69;
goto lbl_51;
}
else
{
obj* x_70; obj* x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_72 = x_66;
} else {
 lean::inc(x_70);
 lean::dec(x_66);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
switch (lean::obj_tag(x_73)) {
case 0:
{
obj* x_76; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_76 = lean::cnstr_get(x_73, 0);
lean::inc(x_76);
lean::dec(x_73);
x_79 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_76);
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_80, 0, x_79);
if (lean::is_scalar(x_72)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_72;
}
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
x_50 = x_82;
goto lbl_51;
}
case 2:
{
obj* x_83; obj* x_86; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_83 = lean::cnstr_get(x_73, 0);
lean::inc(x_83);
lean::dec(x_73);
x_86 = lean::cnstr_get(x_83, 2);
lean::inc(x_86);
lean::dec(x_83);
x_89 = l_lean_elaborator_prec__to__nat___main(x_86);
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_90, 0, x_89);
if (lean::is_scalar(x_72)) {
 x_91 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_91 = x_72;
}
lean::cnstr_set(x_91, 0, x_90);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
x_50 = x_92;
goto lbl_51;
}
default:
{
obj* x_95; 
lean::dec(x_73);
lean::dec(x_72);
x_95 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
x_50 = x_95;
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
obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_9);
x_97 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_99 = x_50;
} else {
 lean::inc(x_97);
 lean::dec(x_50);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_97);
x_7 = x_100;
goto lbl_8;
}
else
{
obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_101 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_103 = x_50;
} else {
 lean::inc(x_101);
 lean::dec(x_50);
 x_103 = lean::box(0);
}
x_104 = l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(x_101);
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_9);
lean::cnstr_set(x_105, 1, x_104);
if (lean::is_scalar(x_103)) {
 x_106 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_106 = x_103;
}
lean::cnstr_set(x_106, 0, x_105);
x_7 = x_106;
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
obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_24; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
lean::dec(x_14);
x_18 = l_lean_parser_command_reserve__notation_has__view;
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_7);
lean::inc(x_2);
x_24 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_22, x_15, x_2, x_3);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_9);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_29 = x_24;
} else {
 lean::inc(x_27);
 lean::dec(x_24);
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
obj* x_31; obj* x_34; obj* x_36; 
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
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
obj* x_18; obj* x_21; obj* x_22; obj* x_25; obj* x_27; 
lean::dec(x_7);
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
lean::dec(x_16);
x_21 = l_lean_parser_command_notation_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
x_25 = lean::apply_1(x_22, x_12);
lean::inc(x_2);
x_27 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_25, x_18, x_2, x_3);
if (lean::obj_tag(x_27) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_9);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_32 = x_27;
} else {
 lean::inc(x_30);
 lean::dec(x_27);
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
obj* x_34; obj* x_37; obj* x_39; 
x_34 = lean::cnstr_get(x_27, 0);
lean::inc(x_34);
lean::dec(x_27);
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
obj* x_43; obj* x_46; obj* x_50; 
x_43 = lean::cnstr_get(x_16, 0);
lean::inc(x_43);
lean::dec(x_16);
x_46 = lean::cnstr_get(x_7, 0);
lean::inc(x_46);
lean::dec(x_7);
lean::inc(x_12);
x_50 = l_lean_elaborator_command__parser__config_register__notation__parser(x_46, x_12, x_43);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_54; obj* x_55; obj* x_58; obj* x_60; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
lean::dec(x_50);
x_54 = l_lean_parser_command_notation_has__view;
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
lean::dec(x_54);
x_58 = lean::apply_1(x_55, x_12);
lean::inc(x_2);
x_60 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_58, x_51, x_2, x_3);
if (lean::obj_tag(x_60) == 0)
{
obj* x_63; obj* x_65; obj* x_66; 
lean::dec(x_9);
lean::dec(x_2);
x_63 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_65 = x_60;
} else {
 lean::inc(x_63);
 lean::dec(x_60);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_63);
return x_66;
}
else
{
obj* x_67; obj* x_70; obj* x_72; 
x_67 = lean::cnstr_get(x_60, 0);
lean::inc(x_67);
lean::dec(x_60);
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
obj* x_77; 
lean::dec(x_12);
x_77 = lean::cnstr_get(x_50, 0);
lean::inc(x_77);
lean::dec(x_50);
x_0 = x_77;
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
obj* x_20; obj* x_23; obj* x_25; obj* x_28; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
lean::dec(x_11);
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
lean::dec(x_20);
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
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_30);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_28);
x_42 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_44 = x_36;
} else {
 lean::inc(x_42);
 lean::dec(x_36);
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
obj* x_46; obj* x_48; obj* x_49; obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_46 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_48 = x_36;
} else {
 lean::inc(x_46);
 lean::dec(x_36);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
lean::dec(x_46);
x_52 = lean::cnstr_get(x_1, 2);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_1, 3);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_1, 5);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_2, 1);
lean::inc(x_58);
lean::dec(x_2);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_49);
lean::cnstr_set(x_61, 1, x_58);
x_62 = lean::cnstr_get(x_1, 7);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_1, 8);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_1, 9);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_1, 10);
lean::inc(x_68);
lean::dec(x_1);
x_71 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_71, 0, x_6);
lean::cnstr_set(x_71, 1, x_28);
lean::cnstr_set(x_71, 2, x_52);
lean::cnstr_set(x_71, 3, x_54);
lean::cnstr_set(x_71, 4, x_30);
lean::cnstr_set(x_71, 5, x_56);
lean::cnstr_set(x_71, 6, x_61);
lean::cnstr_set(x_71, 7, x_62);
lean::cnstr_set(x_71, 8, x_64);
lean::cnstr_set(x_71, 9, x_66);
lean::cnstr_set(x_71, 10, x_68);
x_72 = lean::box(0);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_71);
if (lean::is_scalar(x_48)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_48;
}
lean::cnstr_set(x_74, 0, x_73);
return x_74;
}
}
}
}
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
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
x_27 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
return x_0;
}
else
{
obj* x_5; obj* x_7; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_18; obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_12 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_14 = x_3;
} else {
 lean::inc(x_12);
 lean::dec(x_3);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_5, 1);
lean::inc(x_15);
lean::dec(x_5);
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_7, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_7, 2);
lean::inc(x_22);
lean::dec(x_7);
x_25 = l_lean_elaborator_postprocess__notation__spec___closed__1;
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_18);
lean::cnstr_set(x_26, 1, x_20);
lean::cnstr_set(x_26, 2, x_22);
lean::cnstr_set(x_26, 3, x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_15);
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_12);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_1);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
else
{
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_3);
return x_0;
}
}
}
else
{
lean::dec(x_1);
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
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
lean::dec(x_0);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_20; uint8 x_21; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::dec(x_7);
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
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; 
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_2);
x_20 = lean::box(0);
return x_20;
}
else
{
obj* x_21; obj* x_24; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_36; 
x_21 = lean::cnstr_get(x_2, 1);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_11, 3);
lean::inc(x_24);
lean::dec(x_11);
x_27 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_29 = x_13;
} else {
 lean::inc(x_27);
 lean::dec(x_13);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_21, 0);
lean::inc(x_30);
x_36 = lean::cnstr_get(x_30, 1);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_44; 
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_21);
lean::dec(x_24);
lean::dec(x_27);
x_44 = lean::box(0);
x_7 = x_44;
goto lbl_8;
}
else
{
obj* x_45; obj* x_47; obj* x_50; obj* x_53; obj* x_54; obj* x_57; uint8 x_58; 
x_45 = lean::cnstr_get(x_30, 3);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_36, 0);
lean::inc(x_47);
lean::dec(x_36);
x_50 = lean::cnstr_get(x_27, 1);
lean::inc(x_50);
lean::dec(x_27);
x_53 = l_string_trim(x_50);
x_54 = lean::cnstr_get(x_47, 1);
lean::inc(x_54);
lean::dec(x_47);
x_57 = l_string_trim(x_54);
x_58 = lean::string_dec_eq(x_53, x_57);
lean::dec(x_57);
lean::dec(x_53);
if (x_58 == 0)
{
obj* x_67; 
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_21);
lean::dec(x_24);
lean::dec(x_45);
x_67 = lean::box(0);
x_7 = x_67;
goto lbl_8;
}
else
{
uint8 x_68; 
x_68 = l_lean_elaborator_match__precedence___main(x_24, x_45);
if (x_68 == 0)
{
obj* x_73; 
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_21);
x_73 = lean::box(0);
x_7 = x_73;
goto lbl_8;
}
else
{
obj* x_74; 
x_74 = lean::box(0);
x_34 = x_74;
goto lbl_35;
}
}
}
lbl_33:
{
if (lean::obj_tag(x_32) == 0)
{
obj* x_76; 
lean::dec(x_30);
x_76 = lean::box(0);
x_7 = x_76;
goto lbl_8;
}
else
{
obj* x_77; obj* x_79; obj* x_80; obj* x_81; 
x_77 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_79 = x_32;
} else {
 lean::inc(x_77);
 lean::dec(x_32);
 x_79 = lean::box(0);
}
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_30);
lean::cnstr_set(x_80, 1, x_77);
if (lean::is_scalar(x_79)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_79;
}
lean::cnstr_set(x_81, 0, x_80);
x_7 = x_81;
goto lbl_8;
}
}
lbl_35:
{
obj* x_83; 
lean::dec(x_34);
x_83 = lean::cnstr_get(x_9, 1);
lean::inc(x_83);
lean::dec(x_9);
if (lean::obj_tag(x_83) == 0)
{
obj* x_86; 
x_86 = lean::cnstr_get(x_21, 1);
lean::inc(x_86);
lean::dec(x_21);
if (lean::obj_tag(x_86) == 0)
{
obj* x_89; 
if (lean::is_scalar(x_29)) {
 x_89 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_89 = x_29;
}
lean::cnstr_set(x_89, 0, x_86);
x_32 = x_89;
goto lbl_33;
}
else
{
obj* x_92; 
lean::dec(x_29);
lean::dec(x_86);
x_92 = lean::box(0);
x_32 = x_92;
goto lbl_33;
}
}
else
{
obj* x_94; obj* x_96; 
lean::dec(x_29);
x_94 = lean::cnstr_get(x_83, 0);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_set(x_83, 0, lean::box(0));
 x_96 = x_83;
} else {
 lean::inc(x_94);
 lean::dec(x_83);
 x_96 = lean::box(0);
}
switch (lean::obj_tag(x_94)) {
case 0:
{
obj* x_97; 
x_97 = lean::cnstr_get(x_21, 1);
lean::inc(x_97);
lean::dec(x_21);
if (lean::obj_tag(x_97) == 0)
{
obj* x_102; 
lean::dec(x_94);
lean::dec(x_96);
x_102 = lean::box(0);
x_32 = x_102;
goto lbl_33;
}
else
{
obj* x_103; 
x_103 = lean::cnstr_get(x_97, 0);
lean::inc(x_103);
switch (lean::obj_tag(x_103)) {
case 0:
{
obj* x_105; obj* x_108; obj* x_111; obj* x_114; uint8 x_117; 
x_105 = lean::cnstr_get(x_94, 0);
lean::inc(x_105);
lean::dec(x_94);
x_108 = lean::cnstr_get(x_103, 0);
lean::inc(x_108);
lean::dec(x_103);
x_111 = lean::cnstr_get(x_105, 1);
lean::inc(x_111);
lean::dec(x_105);
x_114 = lean::cnstr_get(x_108, 1);
lean::inc(x_114);
lean::dec(x_108);
x_117 = l_lean_elaborator_match__precedence___main(x_111, x_114);
if (x_117 == 0)
{
obj* x_120; 
lean::dec(x_97);
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
lean::cnstr_set(x_121, 0, x_97);
x_32 = x_121;
goto lbl_33;
}
}
default:
{
obj* x_126; 
lean::dec(x_97);
lean::dec(x_103);
lean::dec(x_94);
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
obj* x_127; 
x_127 = lean::cnstr_get(x_21, 1);
lean::inc(x_127);
lean::dec(x_21);
if (lean::obj_tag(x_127) == 0)
{
obj* x_132; 
lean::dec(x_94);
lean::dec(x_96);
x_132 = lean::box(0);
x_32 = x_132;
goto lbl_33;
}
else
{
obj* x_133; 
x_133 = lean::cnstr_get(x_127, 0);
lean::inc(x_133);
switch (lean::obj_tag(x_133)) {
case 1:
{
obj* x_135; obj* x_138; obj* x_141; obj* x_144; uint8 x_147; 
x_135 = lean::cnstr_get(x_94, 0);
lean::inc(x_135);
lean::dec(x_94);
x_138 = lean::cnstr_get(x_133, 0);
lean::inc(x_138);
lean::dec(x_133);
x_141 = lean::cnstr_get(x_135, 1);
lean::inc(x_141);
lean::dec(x_135);
x_144 = lean::cnstr_get(x_138, 1);
lean::inc(x_144);
lean::dec(x_138);
x_147 = l_lean_elaborator_match__precedence___main(x_141, x_144);
if (x_147 == 0)
{
obj* x_150; 
lean::dec(x_96);
lean::dec(x_127);
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
lean::cnstr_set(x_151, 0, x_127);
x_32 = x_151;
goto lbl_33;
}
}
default:
{
obj* x_156; 
lean::dec(x_94);
lean::dec(x_96);
lean::dec(x_133);
lean::dec(x_127);
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
x_162 = lean::cnstr_get(x_21, 1);
lean::inc(x_162);
lean::dec(x_21);
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
obj* x_169; 
x_169 = lean::cnstr_get(x_162, 0);
lean::inc(x_169);
lean::dec(x_162);
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
obj* x_187; 
lean::dec(x_181);
x_187 = lean::box(0);
x_160 = x_187;
goto lbl_161;
}
else
{
obj* x_188; obj* x_190; 
x_188 = lean::cnstr_get(x_185, 0);
if (lean::is_exclusive(x_185)) {
 lean::cnstr_set(x_185, 0, lean::box(0));
 x_190 = x_185;
} else {
 lean::inc(x_188);
 lean::dec(x_185);
 x_190 = lean::box(0);
}
switch (lean::obj_tag(x_188)) {
case 0:
{
obj* x_192; 
lean::dec(x_188);
if (lean::is_scalar(x_190)) {
 x_192 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_192 = x_190;
}
lean::cnstr_set(x_192, 0, x_181);
x_160 = x_192;
goto lbl_161;
}
default:
{
obj* x_196; 
lean::dec(x_190);
lean::dec(x_188);
lean::dec(x_181);
x_196 = lean::box(0);
x_160 = x_196;
goto lbl_161;
}
}
}
}
else
{
obj* x_197; 
x_197 = lean::cnstr_get(x_179, 0);
lean::inc(x_197);
lean::dec(x_179);
switch (lean::obj_tag(x_197)) {
case 0:
{
obj* x_200; obj* x_203; obj* x_206; 
x_200 = lean::cnstr_get(x_197, 0);
lean::inc(x_200);
lean::dec(x_197);
x_203 = lean::cnstr_get(x_172, 1);
lean::inc(x_203);
lean::dec(x_172);
x_206 = l_option_map___rarg(x_177, x_203);
if (lean::obj_tag(x_206) == 0)
{
obj* x_209; 
lean::dec(x_175);
lean::dec(x_200);
x_209 = lean::box(0);
x_160 = x_209;
goto lbl_161;
}
else
{
obj* x_210; obj* x_212; 
x_210 = lean::cnstr_get(x_206, 0);
if (lean::is_exclusive(x_206)) {
 lean::cnstr_set(x_206, 0, lean::box(0));
 x_212 = x_206;
} else {
 lean::inc(x_210);
 lean::dec(x_206);
 x_212 = lean::box(0);
}
switch (lean::obj_tag(x_210)) {
case 0:
{
obj* x_213; obj* x_216; obj* x_217; uint8 x_218; 
x_213 = lean::cnstr_get(x_210, 0);
lean::inc(x_213);
lean::dec(x_210);
x_216 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_200);
x_217 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_213);
x_218 = lean::nat_dec_eq(x_216, x_217);
lean::dec(x_217);
lean::dec(x_216);
if (x_218 == 0)
{
obj* x_223; 
lean::dec(x_212);
lean::dec(x_175);
x_223 = lean::box(0);
x_160 = x_223;
goto lbl_161;
}
else
{
obj* x_224; 
if (lean::is_scalar(x_212)) {
 x_224 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_224 = x_212;
}
lean::cnstr_set(x_224, 0, x_175);
x_160 = x_224;
goto lbl_161;
}
}
default:
{
obj* x_229; 
lean::dec(x_212);
lean::dec(x_210);
lean::dec(x_175);
lean::dec(x_200);
x_229 = lean::box(0);
x_160 = x_229;
goto lbl_161;
}
}
}
}
default:
{
obj* x_233; 
lean::dec(x_175);
lean::dec(x_172);
lean::dec(x_197);
x_233 = lean::box(0);
x_160 = x_233;
goto lbl_161;
}
}
}
}
default:
{
obj* x_238; 
lean::dec(x_157);
lean::dec(x_159);
lean::dec(x_169);
lean::dec(x_96);
x_238 = lean::box(0);
x_32 = x_238;
goto lbl_33;
}
}
}
lbl_161:
{
if (lean::obj_tag(x_160) == 0)
{
obj* x_242; 
lean::dec(x_157);
lean::dec(x_159);
lean::dec(x_96);
x_242 = lean::box(0);
x_32 = x_242;
goto lbl_33;
}
else
{
obj* x_243; obj* x_245; obj* x_246; obj* x_249; obj* x_250; obj* x_251; obj* x_252; 
x_243 = lean::cnstr_get(x_160, 0);
if (lean::is_exclusive(x_160)) {
 x_245 = x_160;
} else {
 lean::inc(x_243);
 lean::dec(x_160);
 x_245 = lean::box(0);
}
x_246 = lean::cnstr_get(x_157, 0);
lean::inc(x_246);
lean::dec(x_157);
x_249 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_249, 0, x_246);
lean::cnstr_set(x_249, 1, x_243);
if (lean::is_scalar(x_159)) {
 x_250 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_250 = x_159;
}
lean::cnstr_set(x_250, 0, x_249);
if (lean::is_scalar(x_245)) {
 x_251 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_251 = x_245;
}
lean::cnstr_set(x_251, 0, x_250);
if (lean::is_scalar(x_96)) {
 x_252 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_252 = x_96;
}
lean::cnstr_set(x_252, 0, x_251);
x_32 = x_252;
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
obj* x_255; 
lean::dec(x_6);
lean::dec(x_4);
x_255 = lean::box(0);
return x_255;
}
else
{
obj* x_256; obj* x_259; 
x_256 = lean::cnstr_get(x_7, 0);
lean::inc(x_256);
lean::dec(x_7);
x_259 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(x_4);
if (lean::obj_tag(x_259) == 0)
{
obj* x_262; 
lean::dec(x_256);
lean::dec(x_6);
x_262 = lean::box(0);
return x_262;
}
else
{
obj* x_263; obj* x_265; obj* x_266; obj* x_267; 
x_263 = lean::cnstr_get(x_259, 0);
if (lean::is_exclusive(x_259)) {
 x_265 = x_259;
} else {
 lean::inc(x_263);
 lean::dec(x_259);
 x_265 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_266 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_266 = x_6;
}
lean::cnstr_set(x_266, 0, x_256);
lean::cnstr_set(x_266, 1, x_263);
if (lean::is_scalar(x_265)) {
 x_267 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_267 = x_265;
}
lean::cnstr_set(x_267, 0, x_266);
return x_267;
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
obj* x_24; 
x_24 = lean::cnstr_get(x_7, 1);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_1);
x_27 = lean::cnstr_get(x_7, 0);
lean::inc(x_27);
lean::dec(x_7);
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 3);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 4);
lean::inc(x_36);
lean::dec(x_0);
x_39 = l_lean_elaborator_postprocess__notation__spec(x_27);
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
lean::dec(x_7);
lean::dec(x_24);
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
obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_76; obj* x_77; obj* x_78; 
x_56 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_58 = x_51;
} else {
 lean::inc(x_56);
 lean::dec(x_51);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_56, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_56, 1);
lean::inc(x_61);
lean::dec(x_56);
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
x_77 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_54; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::dec(x_10);
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
x_53 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_31; obj* x_34; obj* x_35; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
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
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_55);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
lbl_9:
{
obj* x_61; 
lean::dec(x_8);
lean::inc(x_1);
x_61 = l_lean_elaborator_notation_elaborate__aux(x_7, x_1, x_2);
if (lean::obj_tag(x_61) == 0)
{
obj* x_63; obj* x_65; obj* x_66; 
lean::dec(x_1);
x_63 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_65 = x_61;
} else {
 lean::inc(x_63);
 lean::dec(x_61);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_63);
return x_66;
}
else
{
obj* x_67; obj* x_70; obj* x_72; obj* x_77; 
x_67 = lean::cnstr_get(x_61, 0);
lean::inc(x_67);
lean::dec(x_61);
x_70 = lean::cnstr_get(x_67, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_67, 1);
lean::inc(x_72);
lean::dec(x_67);
lean::inc(x_1);
lean::inc(x_70);
x_77 = l_lean_elaborator_register__notation__macro(x_70, x_1, x_72);
if (lean::obj_tag(x_77) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_1);
lean::dec(x_70);
x_80 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_82 = x_77;
} else {
 lean::inc(x_80);
 lean::dec(x_77);
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
obj* x_84; 
x_84 = lean::cnstr_get(x_70, 0);
lean::inc(x_84);
lean::dec(x_70);
if (lean::obj_tag(x_84) == 0)
{
obj* x_87; obj* x_90; obj* x_92; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_119; obj* x_120; 
x_87 = lean::cnstr_get(x_77, 0);
lean::inc(x_87);
lean::dec(x_77);
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_87, 1);
lean::inc(x_92);
lean::dec(x_87);
x_95 = lean::cnstr_get(x_92, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_92, 1);
lean::inc(x_97);
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_90);
lean::cnstr_set(x_99, 1, x_97);
x_100 = lean::cnstr_get(x_92, 2);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_92, 3);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_92, 4);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_92, 5);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_92, 6);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_92, 7);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_92, 8);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_92, 9);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_92, 10);
lean::inc(x_116);
lean::dec(x_92);
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
obj* x_122; obj* x_125; obj* x_127; obj* x_130; obj* x_132; obj* x_134; obj* x_136; obj* x_138; obj* x_140; obj* x_142; obj* x_143; obj* x_145; obj* x_147; obj* x_149; obj* x_151; obj* x_153; obj* x_156; obj* x_157; obj* x_159; obj* x_161; obj* x_163; obj* x_165; obj* x_167; obj* x_170; obj* x_171; 
lean::dec(x_84);
x_122 = lean::cnstr_get(x_77, 0);
lean::inc(x_122);
lean::dec(x_77);
x_125 = lean::cnstr_get(x_122, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_122, 1);
lean::inc(x_127);
lean::dec(x_122);
x_130 = lean::cnstr_get(x_127, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_127, 1);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_127, 2);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_127, 3);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_127, 4);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_138, 0);
lean::inc(x_140);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_125);
lean::cnstr_set(x_142, 1, x_140);
x_143 = lean::cnstr_get(x_138, 1);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_138, 2);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_138, 3);
lean::inc(x_147);
x_149 = lean::cnstr_get(x_138, 4);
lean::inc(x_149);
x_151 = lean::cnstr_get(x_138, 5);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_138, 6);
lean::inc(x_153);
lean::dec(x_138);
x_156 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_156, 0, x_142);
lean::cnstr_set(x_156, 1, x_143);
lean::cnstr_set(x_156, 2, x_145);
lean::cnstr_set(x_156, 3, x_147);
lean::cnstr_set(x_156, 4, x_149);
lean::cnstr_set(x_156, 5, x_151);
lean::cnstr_set(x_156, 6, x_153);
x_157 = lean::cnstr_get(x_127, 5);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_127, 6);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_127, 7);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_127, 8);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_127, 9);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_127, 10);
lean::inc(x_167);
lean::dec(x_127);
x_170 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_170, 0, x_130);
lean::cnstr_set(x_170, 1, x_132);
lean::cnstr_set(x_170, 2, x_134);
lean::cnstr_set(x_170, 3, x_136);
lean::cnstr_set(x_170, 4, x_156);
lean::cnstr_set(x_170, 5, x_157);
lean::cnstr_set(x_170, 6, x_159);
lean::cnstr_set(x_170, 7, x_161);
lean::cnstr_set(x_170, 8, x_163);
lean::cnstr_set(x_170, 9, x_165);
lean::cnstr_set(x_170, 10, x_167);
x_171 = l_lean_elaborator_update__parser__config(x_1, x_170);
return x_171;
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
obj* x_7; obj* x_9; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; 
x_11 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_13 = x_0;
} else {
 lean::inc(x_11);
 lean::dec(x_0);
 x_13 = lean::box(0);
}
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
lean::dec(x_13);
lean::dec(x_1);
lean::dec(x_11);
x_31 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
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
obj* x_35; obj* x_38; obj* x_40; obj* x_43; 
x_35 = lean::cnstr_get(x_27, 0);
lean::inc(x_35);
lean::dec(x_27);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
x_43 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_11, x_1, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_13);
lean::dec(x_38);
x_46 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_48 = x_43;
} else {
 lean::inc(x_46);
 lean::dec(x_43);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_46);
return x_49;
}
else
{
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_60; 
x_50 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_52 = x_43;
} else {
 lean::inc(x_50);
 lean::dec(x_43);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
lean::dec(x_50);
if (lean::is_scalar(x_13)) {
 x_58 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_58 = x_13;
}
lean::cnstr_set(x_58, 0, x_38);
lean::cnstr_set(x_58, 1, x_53);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_52;
}
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
obj* x_61; 
x_61 = lean::cnstr_get(x_9, 1);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_64; obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_7);
x_64 = lean::cnstr_get(x_0, 1);
lean::inc(x_64);
lean::dec(x_0);
x_67 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_release(x_9, 1);
 x_69 = x_9;
} else {
 lean::inc(x_67);
 lean::dec(x_9);
 x_69 = lean::box(0);
}
x_70 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_64, x_1, x_2);
if (lean::obj_tag(x_70) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_67);
lean::dec(x_69);
x_73 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_75 = x_70;
} else {
 lean::inc(x_73);
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
obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_77 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_79 = x_70;
} else {
 lean::inc(x_77);
 lean::dec(x_70);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
lean::dec(x_77);
x_85 = lean::box(0);
x_86 = lean_expr_mk_const(x_67, x_85);
if (lean::is_scalar(x_69)) {
 x_87 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_87 = x_69;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_80);
x_88 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_91; obj* x_92; obj* x_95; obj* x_96; obj* x_98; 
lean::dec(x_9);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_91 = x_61;
} else {
 lean::dec(x_61);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_0, 1);
lean::inc(x_92);
lean::dec(x_0);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_7);
x_96 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
lean::inc(x_1);
x_98 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_95, x_96, x_1, x_2);
if (lean::obj_tag(x_98) == 0)
{
obj* x_102; obj* x_104; obj* x_105; 
lean::dec(x_1);
lean::dec(x_91);
lean::dec(x_92);
x_102 = lean::cnstr_get(x_98, 0);
if (lean::is_exclusive(x_98)) {
 x_104 = x_98;
} else {
 lean::inc(x_102);
 lean::dec(x_98);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_102);
return x_105;
}
else
{
obj* x_106; obj* x_109; obj* x_111; obj* x_114; 
x_106 = lean::cnstr_get(x_98, 0);
lean::inc(x_106);
lean::dec(x_98);
x_109 = lean::cnstr_get(x_106, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_106, 1);
lean::inc(x_111);
lean::dec(x_106);
x_114 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_92, x_1, x_111);
if (lean::obj_tag(x_114) == 0)
{
obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_109);
lean::dec(x_91);
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
obj* x_121; obj* x_123; obj* x_124; obj* x_126; obj* x_129; obj* x_130; obj* x_131; 
x_121 = lean::cnstr_get(x_114, 0);
if (lean::is_exclusive(x_114)) {
 x_123 = x_114;
} else {
 lean::inc(x_121);
 lean::dec(x_114);
 x_123 = lean::box(0);
}
x_124 = lean::cnstr_get(x_121, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_121, 1);
lean::inc(x_126);
lean::dec(x_121);
if (lean::is_scalar(x_91)) {
 x_129 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_129 = x_91;
}
lean::cnstr_set(x_129, 0, x_109);
lean::cnstr_set(x_129, 1, x_124);
x_130 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_126);
if (lean::is_scalar(x_123)) {
 x_131 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_131 = x_123;
}
lean::cnstr_set(x_131, 0, x_130);
return x_131;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("command");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("attribute");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_lean_kvmap_set__name(x_0, x_3, x_5);
return x_6;
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
obj* x_20; obj* x_23; obj* x_25; obj* x_28; obj* x_31; 
x_20 = lean::cnstr_get(x_12, 0);
lean::inc(x_20);
lean::dec(x_12);
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
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_23);
x_36 = lean::cnstr_get(x_31, 0);
if (lean::is_exclusive(x_31)) {
 x_38 = x_31;
} else {
 lean::inc(x_36);
 lean::dec(x_31);
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
obj* x_40; obj* x_43; obj* x_45; obj* x_48; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_40 = lean::cnstr_get(x_31, 0);
lean::inc(x_40);
lean::dec(x_31);
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
x_48 = lean::cnstr_get(x_8, 0);
lean::inc(x_48);
lean::dec(x_8);
x_51 = l_option_is__some___main___rarg(x_48);
x_52 = l_lean_elaborator_attribute_elaborate___closed__1;
x_53 = l_lean_elaborator_attribute_elaborate___closed__2;
x_54 = l_lean_kvmap_set__bool(x_52, x_53, x_51);
x_55 = l_lean_elaborator_mk__eqns___closed__1;
x_56 = l_lean_expr_mk__capp(x_55, x_43);
x_57 = lean_expr_mk_app(x_23, x_56);
x_58 = lean_expr_mk_mdata(x_54, x_57);
x_59 = l_lean_elaborator_old__elab__command(x_0, x_58, x_1, x_45);
return x_59;
}
}
}
}
obj* _init_l_lean_elaborator_check_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("command");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("#check");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_lean_kvmap_set__name(x_0, x_3, x_5);
return x_6;
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::dec(x_10);
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
x_53 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("command");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("init_quot");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_lean_kvmap_set__name(x_0, x_3, x_5);
x_7 = l_lean_elaborator_dummy;
x_8 = lean_expr_mk_mdata(x_6, x_7);
return x_8;
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
obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_4 = l_lean_parser_command_set__option_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_8, 2);
lean::inc(x_9);
switch (lean::obj_tag(x_9)) {
case 0:
{
obj* x_11; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_18; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_56; uint8 x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_11);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
lean::dec(x_8);
x_18 = lean::cnstr_get(x_15, 2);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_2, 4);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_21, 6);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_2, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_2, 2);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_2, 3);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_21, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_21, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_21, 2);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_21, 3);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_21, 4);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_21, 5);
lean::inc(x_43);
lean::dec(x_21);
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
x_59 = 1;
x_60 = l_lean_kvmap_set__bool(x_23, x_18, x_59);
x_61 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_61, 0, x_33);
lean::cnstr_set(x_61, 1, x_35);
lean::cnstr_set(x_61, 2, x_37);
lean::cnstr_set(x_61, 3, x_39);
lean::cnstr_set(x_61, 4, x_41);
lean::cnstr_set(x_61, 5, x_43);
lean::cnstr_set(x_61, 6, x_60);
x_62 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_62, 0, x_25);
lean::cnstr_set(x_62, 1, x_27);
lean::cnstr_set(x_62, 2, x_29);
lean::cnstr_set(x_62, 3, x_31);
lean::cnstr_set(x_62, 4, x_61);
lean::cnstr_set(x_62, 5, x_46);
lean::cnstr_set(x_62, 6, x_48);
lean::cnstr_set(x_62, 7, x_50);
lean::cnstr_set(x_62, 8, x_52);
lean::cnstr_set(x_62, 9, x_54);
lean::cnstr_set(x_62, 10, x_56);
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
obj* x_67; obj* x_70; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; uint8 x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_11);
x_67 = lean::cnstr_get(x_8, 1);
lean::inc(x_67);
lean::dec(x_8);
x_70 = lean::cnstr_get(x_67, 2);
lean::inc(x_70);
lean::dec(x_67);
x_73 = lean::cnstr_get(x_2, 4);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_73, 6);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_2, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_2, 1);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_2, 2);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_2, 3);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_73, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_73, 1);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_73, 2);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_73, 3);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_73, 4);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_73, 5);
lean::inc(x_95);
lean::dec(x_73);
x_98 = lean::cnstr_get(x_2, 5);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_2, 6);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_2, 7);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_2, 8);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_2, 9);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_2, 10);
lean::inc(x_108);
lean::dec(x_2);
x_111 = 0;
x_112 = l_lean_kvmap_set__bool(x_75, x_70, x_111);
x_113 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_113, 0, x_85);
lean::cnstr_set(x_113, 1, x_87);
lean::cnstr_set(x_113, 2, x_89);
lean::cnstr_set(x_113, 3, x_91);
lean::cnstr_set(x_113, 4, x_93);
lean::cnstr_set(x_113, 5, x_95);
lean::cnstr_set(x_113, 6, x_112);
x_114 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_114, 0, x_77);
lean::cnstr_set(x_114, 1, x_79);
lean::cnstr_set(x_114, 2, x_81);
lean::cnstr_set(x_114, 3, x_83);
lean::cnstr_set(x_114, 4, x_113);
lean::cnstr_set(x_114, 5, x_98);
lean::cnstr_set(x_114, 6, x_100);
lean::cnstr_set(x_114, 7, x_102);
lean::cnstr_set(x_114, 8, x_104);
lean::cnstr_set(x_114, 9, x_106);
lean::cnstr_set(x_114, 10, x_108);
x_115 = lean::box(0);
x_116 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_114);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_116);
return x_117;
}
}
case 1:
{
obj* x_118; obj* x_121; obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_134; obj* x_136; obj* x_138; obj* x_140; obj* x_142; obj* x_144; obj* x_146; obj* x_149; obj* x_151; obj* x_153; obj* x_155; obj* x_157; obj* x_159; obj* x_162; obj* x_165; 
x_118 = lean::cnstr_get(x_8, 1);
lean::inc(x_118);
lean::dec(x_8);
x_121 = lean::cnstr_get(x_118, 2);
lean::inc(x_121);
lean::dec(x_118);
x_124 = lean::cnstr_get(x_2, 4);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_124, 6);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_2, 0);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_2, 1);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_2, 2);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_2, 3);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_124, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_124, 1);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_124, 2);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_124, 3);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_124, 4);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_124, 5);
lean::inc(x_146);
lean::dec(x_124);
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
x_162 = lean::cnstr_get(x_9, 0);
lean::inc(x_162);
lean::dec(x_9);
x_165 = l_lean_parser_string__lit_view_value(x_162);
if (lean::obj_tag(x_165) == 0)
{
obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_121);
x_167 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_167, 0, x_136);
lean::cnstr_set(x_167, 1, x_138);
lean::cnstr_set(x_167, 2, x_140);
lean::cnstr_set(x_167, 3, x_142);
lean::cnstr_set(x_167, 4, x_144);
lean::cnstr_set(x_167, 5, x_146);
lean::cnstr_set(x_167, 6, x_126);
x_168 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_168, 0, x_128);
lean::cnstr_set(x_168, 1, x_130);
lean::cnstr_set(x_168, 2, x_132);
lean::cnstr_set(x_168, 3, x_134);
lean::cnstr_set(x_168, 4, x_167);
lean::cnstr_set(x_168, 5, x_149);
lean::cnstr_set(x_168, 6, x_151);
lean::cnstr_set(x_168, 7, x_153);
lean::cnstr_set(x_168, 8, x_155);
lean::cnstr_set(x_168, 9, x_157);
lean::cnstr_set(x_168, 10, x_159);
x_169 = lean::box(0);
x_170 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_168);
x_171 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_171, 0, x_170);
return x_171;
}
else
{
obj* x_172; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; 
x_172 = lean::cnstr_get(x_165, 0);
lean::inc(x_172);
lean::dec(x_165);
x_175 = l_lean_kvmap_set__string(x_126, x_121, x_172);
x_176 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_176, 0, x_136);
lean::cnstr_set(x_176, 1, x_138);
lean::cnstr_set(x_176, 2, x_140);
lean::cnstr_set(x_176, 3, x_142);
lean::cnstr_set(x_176, 4, x_144);
lean::cnstr_set(x_176, 5, x_146);
lean::cnstr_set(x_176, 6, x_175);
x_177 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_177, 0, x_128);
lean::cnstr_set(x_177, 1, x_130);
lean::cnstr_set(x_177, 2, x_132);
lean::cnstr_set(x_177, 3, x_134);
lean::cnstr_set(x_177, 4, x_176);
lean::cnstr_set(x_177, 5, x_149);
lean::cnstr_set(x_177, 6, x_151);
lean::cnstr_set(x_177, 7, x_153);
lean::cnstr_set(x_177, 8, x_155);
lean::cnstr_set(x_177, 9, x_157);
lean::cnstr_set(x_177, 10, x_159);
x_178 = lean::box(0);
x_179 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_179, 0, x_178);
lean::cnstr_set(x_179, 1, x_177);
x_180 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_180, 0, x_179);
return x_180;
}
}
default:
{
obj* x_181; obj* x_184; obj* x_187; obj* x_189; obj* x_191; obj* x_193; obj* x_195; obj* x_197; obj* x_199; obj* x_201; obj* x_203; obj* x_205; obj* x_207; obj* x_209; obj* x_212; obj* x_214; obj* x_216; obj* x_218; obj* x_220; obj* x_222; obj* x_225; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; 
x_181 = lean::cnstr_get(x_8, 1);
lean::inc(x_181);
lean::dec(x_8);
x_184 = lean::cnstr_get(x_181, 2);
lean::inc(x_184);
lean::dec(x_181);
x_187 = lean::cnstr_get(x_2, 4);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_187, 6);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_2, 0);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_2, 1);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_2, 2);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_2, 3);
lean::inc(x_197);
x_199 = lean::cnstr_get(x_187, 0);
lean::inc(x_199);
x_201 = lean::cnstr_get(x_187, 1);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_187, 2);
lean::inc(x_203);
x_205 = lean::cnstr_get(x_187, 3);
lean::inc(x_205);
x_207 = lean::cnstr_get(x_187, 4);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_187, 5);
lean::inc(x_209);
lean::dec(x_187);
x_212 = lean::cnstr_get(x_2, 5);
lean::inc(x_212);
x_214 = lean::cnstr_get(x_2, 6);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_2, 7);
lean::inc(x_216);
x_218 = lean::cnstr_get(x_2, 8);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_2, 9);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_2, 10);
lean::inc(x_222);
lean::dec(x_2);
x_225 = lean::cnstr_get(x_9, 0);
lean::inc(x_225);
lean::dec(x_9);
x_228 = l_lean_parser_number_view_to__nat___main(x_225);
x_229 = l_lean_kvmap_set__nat(x_189, x_184, x_228);
x_230 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_230, 0, x_199);
lean::cnstr_set(x_230, 1, x_201);
lean::cnstr_set(x_230, 2, x_203);
lean::cnstr_set(x_230, 3, x_205);
lean::cnstr_set(x_230, 4, x_207);
lean::cnstr_set(x_230, 5, x_209);
lean::cnstr_set(x_230, 6, x_229);
x_231 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_231, 0, x_191);
lean::cnstr_set(x_231, 1, x_193);
lean::cnstr_set(x_231, 2, x_195);
lean::cnstr_set(x_231, 3, x_197);
lean::cnstr_set(x_231, 4, x_230);
lean::cnstr_set(x_231, 5, x_212);
lean::cnstr_set(x_231, 6, x_214);
lean::cnstr_set(x_231, 7, x_216);
lean::cnstr_set(x_231, 8, x_218);
lean::cnstr_set(x_231, 9, x_220);
lean::cnstr_set(x_231, 10, x_222);
x_232 = lean::box(0);
x_233 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_231);
x_234 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_234, 0, x_233);
return x_234;
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
obj* x_4; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1;
x_10 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_0, x_9, x_1, x_2, x_6);
return x_10;
}
else
{
obj* x_12; obj* x_15; obj* x_18; obj* x_21; 
lean::dec(x_0);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(x_18, x_1, x_2, x_12);
return x_21;
}
}
}
obj* l_lean_elaborator_no__kind_elaborate___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = l_lean_parser_syntax_as__node___main(x_3);
x_10 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_5; obj* x_7; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
lean::inc(x_5);
x_11 = l_lean_parser_syntax_as__node___main(x_5);
x_12 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1;
x_13 = l_option_map___rarg(x_12, x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_5);
x_15 = lean::box(0);
lean::inc(x_1);
lean::inc(x_0);
x_18 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_15, x_0, x_1, x_7);
x_19 = lean::box(x_2);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 5, 4);
lean::closure_set(x_20, 0, x_19);
lean::closure_set(x_20, 1, x_3);
lean::closure_set(x_20, 2, x_0);
lean::closure_set(x_20, 3, x_1);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_21, 0, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_22, 0, x_18);
lean::closure_set(x_22, 1, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_26; uint8 x_27; 
x_23 = lean::cnstr_get(x_13, 0);
lean::inc(x_23);
lean::dec(x_13);
x_26 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2;
x_27 = lean_name_dec_eq(x_23, x_26);
if (x_27 == 0)
{
obj* x_28; uint8 x_29; 
x_28 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3;
x_29 = lean_name_dec_eq(x_23, x_28);
lean::dec(x_23);
if (x_29 == 0)
{
obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_5);
x_32 = lean::box(0);
lean::inc(x_1);
lean::inc(x_0);
x_35 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_32, x_0, x_1, x_7);
x_36 = lean::box(x_2);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 5, 4);
lean::closure_set(x_37, 0, x_36);
lean::closure_set(x_37, 1, x_3);
lean::closure_set(x_37, 2, x_0);
lean::closure_set(x_37, 3, x_1);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_38, 0, x_37);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_39, 0, x_35);
lean::closure_set(x_39, 1, x_38);
return x_39;
}
else
{
lean::dec(x_3);
if (x_2 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_7);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_47, 0, x_46);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4;
x_49 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_5, x_48, x_0, x_1, x_7);
return x_49;
}
}
}
else
{
lean::dec(x_23);
lean::dec(x_3);
if (x_2 == 0)
{
obj* x_52; obj* x_53; 
x_52 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5;
x_53 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_5, x_52, x_0, x_1, x_7);
return x_53;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_57 = lean::box(0);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_7);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_60, 0, x_59);
return x_60;
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
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::apply_1(x_0, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
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
x_21 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_24; 
x_24 = lean::box(0);
x_10 = x_24;
goto lbl_11;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_26; 
lean::dec(x_15);
x_26 = lean::box(0);
x_10 = x_26;
goto lbl_11;
}
else
{
obj* x_27; obj* x_30; uint8 x_32; 
x_27 = lean::cnstr_get(x_15, 0);
lean::inc(x_27);
lean::dec(x_15);
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
x_32 = lean_name_dec_eq(x_27, x_30);
lean::dec(x_30);
lean::dec(x_27);
if (x_32 == 0)
{
obj* x_35; 
x_35 = lean::box(0);
x_10 = x_35;
goto lbl_11;
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_41 = lean::box(0);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_7);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_44, 0, x_43);
return x_44;
}
}
}
lbl_11:
{
obj* x_46; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_10);
x_46 = l_lean_parser_command_end_has__view;
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
lean::dec(x_46);
x_50 = lean::apply_1(x_47, x_5);
x_51 = l_lean_elaborator_end__scope___lambda__2___closed__1;
x_52 = lean::string_append(x_51, x_0);
lean::dec(x_0);
x_54 = l_lean_elaborator_end__scope___lambda__2___closed__2;
x_55 = lean::string_append(x_52, x_54);
x_56 = lean::box(0);
x_57 = l_option_get__or__else___main___rarg(x_1, x_56);
x_58 = l_lean_name_to__string___closed__1;
x_59 = l_lean_name_to__string__with__sep___main(x_58, x_57);
x_60 = lean::string_append(x_55, x_59);
lean::dec(x_59);
x_62 = l_char_has__repr___closed__1;
x_63 = lean::string_append(x_60, x_62);
x_64 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_50, x_63, x_2, x_3, x_7);
return x_64;
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
obj* x_1; obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_1, 4);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_2; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
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
x_28 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
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
x_58 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
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
x_65 = lean::box(0);
x_66 = l_list_foldl___main___at_lean_elaborator_elaborators___spec__5(x_65, x_64);
return x_66;
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
obj* x_60; obj* x_63; obj* x_66; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_4);
lean::dec(x_0);
x_60 = lean::cnstr_get(x_9, 0);
lean::inc(x_60);
lean::dec(x_9);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
x_66 = lean::cnstr_get(x_63, 0);
lean::inc(x_66);
lean::dec(x_63);
x_69 = lean::box(0);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_66);
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
obj* x_21; obj* x_24; obj* x_26; obj* x_29; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(x_9, x_1, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_11);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_34 = x_29;
} else {
 lean::inc(x_32);
 lean::dec(x_29);
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
lean::dec(x_36);
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
x_45 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_15 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_17 = x_8;
} else {
 lean::inc(x_15);
 lean::dec(x_8);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
lean::dec(x_15);
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
x_37 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_51 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_53 = x_44;
} else {
 lean::inc(x_51);
 lean::dec(x_44);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
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
x_66 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
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
obj* x_5; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
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
obj* x_18; obj* x_21; obj* x_24; 
lean::dec(x_1);
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 1);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
lean::dec(x_5);
x_24 = lean::apply_3(x_21, x_2, x_3, x_18);
return x_24;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("trace");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("as_messages");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = l_lean_options_mk;
x_8 = 1;
x_9 = l_lean_kvmap_set__bool(x_7, x_6, x_8);
x_10 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1;
x_11 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2;
x_12 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_10);
lean::cnstr_set(x_12, 2, x_11);
lean::cnstr_set(x_12, 3, x_1);
lean::cnstr_set(x_12, 4, x_0);
lean::cnstr_set(x_12, 5, x_0);
lean::cnstr_set(x_12, 6, x_9);
return x_12;
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
