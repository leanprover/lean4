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
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_token__map_insert___rarg(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
obj* l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_current__command___boxed(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5;
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6;
obj* l_lean_elaborator_locally___rarg___lambda__2(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___boxed(obj*, obj*, obj*);
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
obj* l_lean_elaborator_locally___rarg___lambda__3___boxed(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_sort(obj*);
obj* l_lean_elaborator_run___lambda__2(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20___boxed(obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1(obj*, obj*);
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1(obj*);
obj* l_lean_elaborator_attrs__to__pexpr(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__except___rarg(obj*);
obj* l_lean_elaborator_elaborator__t_monad__reader(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__reader___rarg(obj*);
extern obj* l_lean_parser_command_attribute_has__view;
obj* l_lean_elaborator_namespace_elaborate(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(obj*);
obj* l_lean_elaborator_match__spec___closed__1;
obj* l_lean_elaborator_resolve__context___main___closed__1;
obj* l_lean_elaborator_init__quot_elaborate___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___rarg(obj*, obj*);
extern obj* l_lean_parser_level_leading_has__view;
extern obj* l_lean_parser_command_reserve__notation_has__view;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate___closed__1;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1(obj*, obj*);
obj* l_list_foldl___main___at_lean_expr_mk__app___spec__1(obj*, obj*);
obj* l_lean_elaborator_run___lambda__5(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_run___closed__2;
obj* l_lean_elaborator_end__scope___lambda__3___closed__1;
obj* l_lean_elaborator_resolve__context___main___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_set__option_elaborate___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_command_declaration;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
obj* l_lean_elaborator_to__level(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__reader__adapter___rarg(obj*);
obj* l_lean_elaborator_get__namespace(obj*);
obj* l_lean_elaborator_level__add(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__7;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14(obj*, obj*, obj*);
extern obj* l_lean_parser_command_export_has__view;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__33;
obj* l_lean_elaborator_to__pexpr___main___closed__1;
obj* l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(obj*, obj*);
obj* l_lean_elaborator_elaborator__config__coe__frontend__config___boxed(obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1;
obj* l_lean_elaborator_include_elaborate(obj*, obj*, obj*);
uint8 l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___lambda__1___closed__1;
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_list_filter__map___main___rarg(obj*, obj*);
extern obj* l_lean_parser_term_match_has__view;
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___boxed(obj*, obj*);
obj* l_lean_elaborator_run___lambda__5___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_level__get__app__args(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3;
extern obj* l_lean_parser_command_open;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2;
obj* l_lean_elaborator_elaborator__config__coe__frontend__config(obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___closed__1;
obj* l_lean_elaborator_elaborator__coe__coelaborator(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__26;
obj* l_lean_kvmap_set__string(obj*, obj*, obj*);
obj* l_lean_parser_term_get__leading___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1;
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(obj*, obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__15(obj*, obj*);
obj* l_lean_elaborator_notation_elaborate__aux___closed__1;
obj* l_lean_elaborator_mk__eqns___closed__2;
obj* l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1(obj*, obj*);
obj* l_reader__t_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___lambda__3(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__reader__adapter___boxed(obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___boxed(obj*, obj*, obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_lean_elaborator_run___lambda__4(obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__31;
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_register__notation__macro(obj*, obj*, obj*);
obj* l_lean_elaborator_section_elaborate___lambda__1(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_preresolve___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24___boxed(obj*, obj*, obj*);
obj* l_list_enum__from___main___rarg(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__state(obj*);
obj* l_lean_elaborator_variables_elaborate___closed__2;
uint8 l_lean_elaborator_match__precedence___main(obj*, obj*);
obj* l_lean_elaborator_with__current__command___boxed(obj*);
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
obj* l_lean_elaborator_resolve__context___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(obj*, obj*, obj*, obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___boxed(obj*, obj*);
obj* l_lean_elaborator_run___lambda__8(obj*);
extern "C" obj* lean_expr_local(obj*, obj*, obj*, uint8);
obj* l_rbmap_find___main___at_lean_elaborator_run___spec__4___boxed(obj*, obj*);
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
obj* l_lean_parser_term_simple__binder_view_to__binder__info___main(obj*);
extern obj* l_lean_parser_command_set__option;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6___boxed(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2(obj*, obj*);
obj* l_lean_elaborator_max__recursion;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18___boxed(obj*, obj*, obj*);
obj* l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1___boxed(obj*, obj*);
obj* l_lean_elaborator_section_elaborate___closed__1;
obj* l_lean_elaborator_elab__def__like___closed__1;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(obj*);
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__state___boxed(obj*);
obj* l_lean_elaborator_expr_mk__annotation___closed__1;
obj* l_list_zip___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(obj*);
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__6;
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_check_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_no__kind_elaborate___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_parser_rec__t_run___at_lean_elaborator_run___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_old__elab__command___boxed(obj*, obj*, obj*, obj*);
uint8 l_coe__decidable__eq(uint8);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(obj*, obj*, obj*);
extern obj* l_lean_parser_command_notation;
obj* l_lean_elaborator_elaborator__t;
obj* l_lean_elaborator_current__command(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24(obj*, obj*, obj*);
obj* l_lean_kvmap_set__name(obj*, obj*, obj*);
uint8 l_lean_elaborator_is__open__namespace(obj*, obj*);
obj* l_lean_elaborator_elaborators;
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate(uint8, obj*, obj*, obj*);
extern obj* l_lean_parser_string__lit_has__view;
extern obj* l_lean_parser_term_pi_has__view;
obj* l_lean_elaborator_export_elaborate___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_find___rarg(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_resolve__context___main___lambda__1(obj*, obj*);
extern obj* l_lean_parser_command_universe_has__view;
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
obj* l_lean_elaborator_locally___rarg(obj*, obj*, obj*);
obj* l_state__t_monad__state___rarg(obj*);
obj* l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___boxed(obj*, obj*);
obj* l_lean_elaborator_elaborator__m;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
extern "C" obj* lean_expr_mk_lambda(obj*, uint8, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___boxed(obj*, obj*, obj*);
obj* l_lean_kvmap_set__nat(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
obj* l_lean_elaborator_declaration_elaborate(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main___closed__4;
obj* l_lean_elaborator_check_elaborate___closed__1;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___boxed(obj*, obj*, obj*);
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
obj* l_lean_elaborator_elaborator__t_monad__reader___boxed(obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_except__t_monad__except___rarg(obj*);
extern obj* l_lean_parser_term_have_has__view;
obj* l_lean_elaborator_init__quot_elaborate(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
extern obj* l_lean_parser_command_variables_has__view;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__32;
obj* l_lean_elaborator_end__scope___lambda__1(obj*, obj*);
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_lean_parser_trie_insert___rarg(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22(obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_preresolve___main(obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind___rarg___closed__1;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__5;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1___boxed(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_yield__to__outside___rarg(obj*, obj*);
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
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25(obj*, obj*);
obj* l_lean_elaborator_get__namespace___boxed(obj*);
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_name_replace__prefix___main(obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate__aux___lambda__1(obj*, obj*);
obj* l_lean_elaborator_open_elaborate(obj*, obj*, obj*);
extern obj* l_lean_parser_command_section_has__view;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(obj*);
obj* l_lean_elaborator_mk__notation__kind___boxed(obj*);
obj* l_list_join___main___rarg(obj*);
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(obj*, obj*);
obj* l_lean_elaborator_mangle__ident(obj*);
obj* l_lean_elaborator_universe_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2(obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view;
obj* l_lean_elaborator_to__pexpr___main___closed__4;
obj* l_lean_elaborator_yield__to__outside___boxed(obj*, obj*);
obj* l_lean_parser_syntax_get__pos(obj*);
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__5(obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7;
extern "C" obj* level_mk_imax(obj*, obj*);
obj* l_lean_environment_mk__empty___boxed(obj*);
obj* l_lean_elaborator_attribute_elaborate___closed__2;
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5;
obj* l_lean_elaborator_to__pexpr___main___lambda__1___boxed(obj*);
obj* l_list_zip__with___main___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1;
obj* l_lean_elaborator_run___closed__3;
obj* l_lean_elaborator_reserve__notation_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_simple__binders__to__pexpr(obj*, obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(obj*, obj*);
obj* l_lean_elaborator_is__open__namespace___boxed(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__47;
obj* l_lean_elaborator_locally___boxed(obj*);
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(obj*);
obj* l_lean_elaborator_commands_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___closed__1;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__19(obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__parser(obj*, obj*, obj*);
obj* l_lean_elaborator_match__open__spec(obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_run___spec__4(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___lambda__1___boxed(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__11;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__17___boxed(obj*, obj*);
obj* l_lean_elaborator_level__add___main___boxed(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__16;
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___rarg(obj*, obj*, obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4___boxed(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3___boxed(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__17;
extern obj* l_lean_parser_module_header;
obj* l_list_map___main___at_lean_elaborator_names__to__pexpr___spec__1(obj*);
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__1___boxed(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__23(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__36;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(obj*);
obj* l_lean_elaborator_update__parser__config(obj*, obj*);
extern obj* l_lean_parser_no__kind;
obj* l_lean_elaborator_run___lambda__4___closed__1;
obj* l_lean_elaborator_level__add___boxed(obj*, obj*);
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__46;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__9(obj*, obj*);
obj* l_monad__coroutine__trans___rarg(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__tokens(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__10;
obj* l_rbmap_insert___main___at_lean_elaborator_include_elaborate___spec__1(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(obj*, obj*);
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m(obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed(obj*, obj*);
obj* l_lean_elaborator_run(obj*);
obj* l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1___boxed(obj*);
obj* l_lean_elaborator_match__precedence___boxed(obj*, obj*);
extern obj* l_lean_message__log_empty;
obj* l_lean_elaborator_register__notation__macro___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_export_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_yield__to__outside___rarg___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___lambda__2(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2___boxed(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12___boxed(obj*, obj*, obj*);
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
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___boxed(obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_mangle__ident___spec__1(obj*, obj*);
obj* l_lean_elaborator_include_elaborate___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__9(obj*, obj*, obj*);
extern obj* l_lean_expander_binding__annotation__update;
extern obj* l_lean_parser_command_attribute;
extern obj* l_lean_parser_term_let_has__view;
obj* l_lean_elaborator_ordered__rbmap_find___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3;
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m___rarg(obj*, obj*, obj*, obj*);
extern "C" obj* level_mk_succ(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__45;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___boxed(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__14;
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(obj*);
obj* l_lean_elaborator_get__namespace___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_universe_elaborate___closed__2;
obj* l_lean_elaborator_is__open__namespace___main___boxed(obj*, obj*);
extern obj* l_lean_parser_term_projection_has__view;
obj* l_lean_elaborator_variables_elaborate___closed__1;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__13(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_coelaborator__m;
obj* l_lean_elaborator_to__pexpr___main___closed__12;
obj* l_lean_elaborator_with__current__command(obj*);
obj* l_lean_parser_syntax_to__format___main(obj*);
obj* l_lean_name_append___main(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
extern obj* l_string_join___closed__1;
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2;
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_end__scope___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__35;
obj* l_lean_elaborator_to__pexpr___main___closed__25;
obj* l_lean_elaborator_names__to__pexpr(obj*);
obj* l_list_foldl___main___at_lean_elaborator_include_elaborate___spec__2(obj*, obj*);
extern obj* l_lean_parser_command_check_has__view;
obj* l_lean_elaborator_run___closed__4;
obj* l_lean_elaborator_elaborator__t_monad__except___boxed(obj*);
obj* l_lean_elaborator_elaborator__coe__coelaborator___boxed(obj*, obj*, obj*, obj*);
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
obj* l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_universe_elaborate___closed__1;
obj* l_monad__state__trans___rarg(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__20;
obj* l_lean_elaborator_run___lambda__3___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1;
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_lean_expander_get__opt__type___main(obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4;
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2(obj*, obj*);
extern obj* l_lean_parser_term_struct__inst_has__view;
obj* l_coroutine_yield___rarg___boxed(obj*, obj*);
obj* l_lean_elaborator_run___lambda__7(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_lambda_has__view;
obj* l_lean_elaborator_mk__eqns___closed__1;
obj* l_lean_elaborator_commands_elaborate___main___lambda__3(uint8, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(obj*);
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(obj*);
obj* l_lean_elaborator_commands_elaborate___main(uint8, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8(obj*);
obj* l_lean_elaborator_run___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__1(obj*);
obj* l_lean_elaborator_resolve__context(obj*, obj*, obj*);
obj* l_lean_elaborator_with__current__command___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg(obj*);
extern "C" obj* lean_expr_mk_let(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_app_has__view;
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2___boxed(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
obj* l_reader__t_monad__reader__adapter___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main(obj*, obj*, obj*);
extern obj* l_lean_parser_ident__univs_has__view;
obj* l_lean_elaborator_to__pexpr___main___closed__9;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(obj*);
obj* l_state__t_monad__except___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_end__scope(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1___boxed(obj*, obj*);
extern obj* l_lean_parser_term_sort__app_has__view;
obj* l_lean_elaborator_to__pexpr___main___lambda__1(obj*);
extern obj* l_lean_parser_term_explicit_has__view;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_current__command___rarg(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_prec__to__nat(obj*);
obj* l_lean_elaborator_end__scope___lambda__2___closed__1;
extern obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
obj* l_state__t_lift___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__24;
obj* l_lean_elaborator_ordered__rbmap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_term_parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate(obj*, obj*, obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__13;
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__3;
obj* l_lean_elaborator_to__level___main___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__27;
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___lambda__4(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1;
obj* l_lean_format_pretty(obj*, obj*);
extern obj* l_lean_parser_command_namespace_has__view;
obj* l_lean_elaborator_preresolve___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__15;
obj* l_lean_elaborator_notation_elaborate___closed__2;
obj* l_lean_elaborator_to__pexpr___main___closed__18;
obj* l_lean_elaborator_elaborator__t_monad(obj*);
obj* l_lean_elaborator_end__scope___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___boxed(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__1___boxed(obj*);
extern obj* l_lean_parser_term_inaccessible_has__view;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5___boxed(obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__2;
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___boxed(obj*);
obj* l_lean_elaborator_dummy;
obj* l_lean_elaborator_section_elaborate___lambda__1___closed__1;
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(obj*, obj*);
obj* l_lean_elaborator_run___closed__5;
extern obj* l_coroutine_monad___closed__1;
obj* l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(obj*);
obj* l_lean_elaborator_no__kind_elaborate___lambda__2(obj*, obj*, obj*);
obj* l_lean_elaborator_module_header_elaborate(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_parser_syntax_kind___main(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__2;
obj* l_lean_elaborator_infer__mod__to__pexpr___boxed(obj*);
obj* l_lean_elaborator_section_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m___rarg___boxed(obj*, obj*, obj*, obj*);
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
obj* l_lean_elaborator_to__pexpr___main___closed__21;
obj* l_lean_name_quick__lt(obj*, obj*);
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_struct__inst__item_has__view;
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_match__precedence___main___boxed(obj*, obj*);
extern obj* l_lean_parser_term_borrowed_has__view;
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11___boxed(obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad___boxed(obj*);
obj* l_lean_parser_term_binders_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___lambda__1___boxed(obj*);
obj* l_lean_elaborator_ordered__rbmap_find(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_universe;
obj* l_lean_elaborator_to__pexpr___main___closed__19;
obj* l_list_map___main___at_lean_elaborator_ident__univ__params__to__pexpr___spec__1(obj*);
extern obj* l_lean_parser_term_show_has__view;
obj* l_lean_elaborator_run___lambda__6(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4(obj*, obj*, obj*);
obj* l_lean_elaborator_run___closed__1;
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(obj*);
obj* l_lean_level_of__nat___main(obj*);
extern obj* l_lean_parser_syntax_reprint__lst___main___closed__1;
obj* l_lean_elaborator_end__scope___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__17(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__22;
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(obj*);
obj* l_lean_parser_term_binder__ident_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14(obj*, obj*, obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_lean_elaborator_coelaborator__m_monad__coroutine;
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__8;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__43;
obj* l_lean_elaborator_attribute_elaborate___closed__1;
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(obj*);
uint8 l_lean_elaborator_match__precedence(obj*, obj*);
obj* l_lean_elaborator_elaborator;
obj* l_lean_elaborator_to__pexpr___main___closed__23;
obj* l_lean_elaborator_elab__def__like___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_string_trim(obj*);
obj* l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__34;
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__5(obj*, obj*);
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___boxed(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8(obj*, obj*, obj*);
extern obj* l_lean_parser_term_sort_has__view;
obj* l_lean_elaborator_to__pexpr___main___lambda__2___boxed(obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_locally(obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
obj* l_lean_elaborator_to__level___main___closed__2;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__5(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(obj*, obj*, obj*);
extern obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
obj* l_lean_elaborator_open_elaborate___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
obj* l_lean_elaborator_commands_elaborate___main___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_match__spec(obj*, obj*);
obj* l_lean_expander_mk__notation__transformer(obj*, obj*, obj*);
obj* l_lean_elaborator_run___lambda__1___boxed(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__30;
obj* l_lean_expr_local___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__eqns(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___lambda__1(obj*);
obj* l_lean_elaborator_level__add___main(obj*, obj*);
obj* l_lean_elaborator_elaborate__command___boxed(obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_expr_mk__capp(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1___boxed(obj*, obj*, obj*);
extern "C" obj* level_mk_mvar(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__2(uint8, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__2(obj*, obj*);
obj* l_lean_elaborator_run___lambda__1___closed__1;
extern obj* l_lean_parser_command_declaration_has__view;
obj* l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
extern obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
obj* l_lean_elaborator_run___closed__7;
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_kvmap_insert__core___main(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__28;
obj* l_lean_elaborator_to__level___main___closed__3;
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m___boxed(obj*);
extern obj* l_lean_parser_command_end_has__view;
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2(obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_elaborator_run___lambda__7___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__6(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_init__quot;
obj* l_lean_elaborator_variables_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__41;
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_run___spec__6___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(obj*);
obj* l_lean_elaborator_ident__univ__params__to__pexpr(obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(obj*, obj*);
obj* l_rbtree_to__list___rarg(obj*);
obj* l_lean_elaborator_elaborator__t_monad___rarg(obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_yield__to__outside(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__3(obj*, obj*);
obj* l_lean_elaborator_section_elaborate___lambda__2(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__coe__coelaborator___lambda__1(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__21(obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___closed__1;
obj* l_lean_elaborator_postprocess__notation__spec(obj*);
obj* l_lean_elaborator_elab__def__like___closed__2;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__19___boxed(obj*, obj*);
extern obj* l_lean_parser_command_include_has__view;
extern obj* l_lean_parser_command_namespace;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2(obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(obj*);
obj* l_lean_elaborator_old__elab__command(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___boxed(obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1(obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
extern "C" obj* level_mk_param(obj*);
uint8 l_rbnode_is__red___main___rarg(obj*);
extern "C" obj* lean_elaborator_elaborate_command(obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20(obj*, obj*, obj*);
extern obj* l_lean_expander_get__opt__type___main___closed__1;
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__10(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_level_trailing_has__view;
obj* l_lean_elaborator_no__kind_elaborate___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___closed__1;
obj* l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25___boxed(obj*, obj*);
obj* l_except__t_lift___rarg___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__29;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5(obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_option_map___rarg(obj*, obj*);
extern obj* l_lean_expander_no__expansion___closed__1;
extern "C" obj* lean_expr_mk_bvar(obj*);
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
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2___boxed(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4(obj*, obj*, uint8, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__42;
extern "C" uint8 lean_environment_contains(obj*, obj*);
extern obj* l_lean_parser_command_notation_has__view;
extern obj* l_lean_parser_command_check;
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__1(obj*, obj*);
extern obj* l_lean_parser_command_export;
obj* l_lean_elaborator_ordered__rbmap_of__list___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__state___rarg(obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__44;
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
obj* l_lean_elaborator_init__quot_elaborate___closed__1;
obj* l_lean_elaborator_postprocess__notation__spec___closed__1;
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
obj* x_4; 
x_4 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_ordered__rbmap_empty(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg), 4, 0);
return x_3;
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
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg), 4, 0);
return x_3;
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
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_insert___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_ordered__rbmap_insert(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_3, x_9);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_7);
lean::inc(x_3);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_3);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_11);
return x_29;
}
else
{
lean::dec(x_11);
x_1 = x_0;
x_2 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_13);
x_1 = x_0;
x_2 = x_7;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg___boxed), 4, 0);
return x_2;
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
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___rarg), 3, 0);
return x_3;
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
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_find___rarg), 3, 0);
return x_3;
}
}
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_find___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_ordered__rbmap_find(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg), 4, 0);
return x_3;
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
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg), 4, 0);
return x_3;
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
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
return x_4;
}
}
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___rarg), 3, 0);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
x_3 = l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_of__list___rarg), 2, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_ordered__rbmap_of__list(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_elaborator__config__coe__frontend__config(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_lean_elaborator_elaborator__config__coe__frontend__config___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_elaborator__config__coe__frontend__config(x_0);
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__t_monad___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_elaborator_elaborator__t_monad___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_elaborator__t_monad(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__t_monad__reader___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_elaborator_elaborator__t_monad__reader___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_elaborator__t_monad__reader(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_elaborator__t_monad__state___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_except__t_monad___rarg(x_0);
lean::inc(x_1);
x_3 = l_state__t_monad___rarg(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__t_monad__state___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_elaborator_elaborator__t_monad__state___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_elaborator__t_monad__state(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__t_monad__except___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_elaborator_elaborator__t_monad__except___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_elaborator__t_monad__except(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_4(x_1, x_0, x_2, x_3, x_4);
return x_5;
}
}
obj* l_lean_elaborator_command_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1), 5, 4);
lean::closure_set(x_4, 0, x_3);
lean::closure_set(x_4, 1, x_0);
lean::closure_set(x_4, 2, x_1);
lean::closure_set(x_4, 3, x_2);
return x_4;
}
}
obj* _init_l_lean_elaborator_coelaborator__m_monad__coroutine() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = l_coroutine_monad___closed__1;
x_1 = l_lean_elaborator_elaborator__t_monad___rarg(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_1);
x_3 = l_except__t_monad___rarg(x_0);
lean::inc(x_3);
x_5 = l_state__t_monad___rarg(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg___boxed), 4, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg___boxed), 3, 1);
lean::closure_set(x_8, 0, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_yield___rarg___boxed), 2, 0);
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__reader__adapter___boxed), 5, 4);
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__t_monad__reader__adapter___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_elaborator_elaborator__t_monad__reader__adapter___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_elaborator__t_monad__reader__adapter(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_current__command___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
x_4 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_elaborator_current__command(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_elaborator_current__command___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_current__command(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_with__current__command___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::apply_4(x_1, x_2, x_3, x_4, x_0);
return x_6;
}
}
obj* l_lean_elaborator_with__current__command(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_with__current__command___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_lean_elaborator_with__current__command___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_elaborator_with__current__command___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_lean_elaborator_with__current__command___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_with__current__command(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_2(x_0, x_2, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__m__coe__coelaborator__m___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_elaborator__m__coe__coelaborator__m___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_elaborator__m__coe__coelaborator__m(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg(obj* x_0, obj* x_1) {
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
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
obj* l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 0);
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
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
}
}
obj* l_lean_elaborator_elaborator__coe__coelaborator(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__coe__coelaborator___lambda__1), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_elaborator__coe__coelaborator___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_elaborator__coe__coelaborator(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = l_lean_parser_syntax_get__pos(x_0);
x_13 = lean::mk_nat_obj(0u);
x_14 = l_option_get__or__else___main___rarg(x_12, x_13);
lean::dec(x_12);
x_16 = l_lean_file__map_to__position(x_9, x_14);
x_17 = lean::box(0);
x_18 = 2;
x_19 = l_string_join___closed__1;
x_20 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_20, 0, x_7);
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg___boxed), 4, 0);
return x_1;
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
lean::dec(x_2);
lean::dec(x_0);
return x_12;
}
else
{
obj* x_15; obj* x_18; uint8 x_19; 
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_19 = lean_name_dec_eq(x_15, x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_21 = lean_name_dec_eq(x_15, x_20);
lean::dec(x_15);
if (x_21 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; 
lean::inc(x_0);
x_24 = l_lean_parser_syntax_to__format___main(x_0);
x_25 = lean::mk_nat_obj(80u);
x_26 = l_lean_format_pretty(x_24, x_25);
x_27 = l_lean_elaborator_level__get__app__args___main___closed__1;
x_28 = lean::string_append(x_27, x_26);
lean::dec(x_26);
x_30 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_28, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
return x_30;
}
else
{
obj* x_33; obj* x_34; obj* x_38; 
x_33 = l_lean_parser_level_trailing_has__view;
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
lean::dec(x_33);
lean::inc(x_0);
x_38 = lean::apply_1(x_34, x_0);
if (lean::obj_tag(x_38) == 0)
{
obj* x_40; obj* x_43; obj* x_45; 
lean::dec(x_0);
x_40 = lean::cnstr_get(x_38, 0);
lean::inc(x_40);
lean::dec(x_38);
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = l_lean_elaborator_level__get__app__args___main(x_43, x_1, x_2);
if (lean::obj_tag(x_45) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_40);
x_47 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 x_49 = x_45;
} else {
 lean::inc(x_47);
 lean::dec(x_45);
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
obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_51 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 x_53 = x_45;
} else {
 lean::inc(x_51);
 lean::dec(x_45);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 0);
x_56 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 x_58 = x_51;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_51);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_54, 0);
x_61 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_63 = x_54;
} else {
 lean::inc(x_59);
 lean::inc(x_61);
 lean::dec(x_54);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_40, 1);
lean::inc(x_64);
lean::dec(x_40);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_64);
lean::cnstr_set(x_67, 1, x_61);
if (lean::is_scalar(x_63)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_63;
}
lean::cnstr_set(x_68, 0, x_59);
lean::cnstr_set(x_68, 1, x_67);
if (lean::is_scalar(x_58)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_58;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_56);
if (lean::is_scalar(x_53)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_53;
}
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_1);
lean::dec(x_38);
x_73 = lean::box(0);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_0);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_2);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_1);
lean::dec(x_15);
x_79 = lean::box(0);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_0);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_2);
x_82 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
return x_82;
}
}
}
}
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_4; obj* x_5; obj* x_6; obj* x_8; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_1, x_4);
x_6 = l_lean_elaborator_level__add___main(x_0, x_5);
lean::dec(x_5);
x_8 = level_mk_succ(x_6);
return x_8;
}
else
{
lean::inc(x_0);
return x_0;
}
}
}
obj* l_lean_elaborator_level__add___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_level__add___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* l_lean_elaborator_level__add___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_level__add(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
x_41 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_43 = x_36;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_36);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
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
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_0);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(x_0, x_5);
x_9 = level_mk_max(x_3, x_8);
return x_9;
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
x_41 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_43 = x_36;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_36);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
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
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_0);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(x_0, x_5);
x_9 = level_mk_imax(x_3, x_8);
return x_9;
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
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_22; obj* x_24; obj* x_26; 
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
x_22 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_24 = x_15;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_15);
 x_24 = lean::box(0);
}
lean::inc(x_20);
x_26 = l_lean_parser_syntax_kind___main(x_20);
if (lean::obj_tag(x_26) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; 
lean::dec(x_14);
lean::dec(x_24);
lean::dec(x_20);
lean::dec(x_22);
lean::inc(x_0);
x_32 = l_lean_parser_syntax_to__format___main(x_0);
x_33 = lean::mk_nat_obj(80u);
x_34 = l_lean_format_pretty(x_32, x_33);
x_35 = l_lean_elaborator_to__level___main___closed__1;
x_36 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_38 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_36, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_38;
}
else
{
obj* x_41; obj* x_44; uint8 x_45; 
x_41 = lean::cnstr_get(x_26, 0);
lean::inc(x_41);
lean::dec(x_26);
x_44 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_45 = lean_name_dec_eq(x_41, x_44);
if (x_45 == 0)
{
obj* x_48; uint8 x_49; 
lean::dec(x_14);
lean::dec(x_24);
x_48 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_49 = lean_name_dec_eq(x_41, x_48);
lean::dec(x_41);
if (x_49 == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_20);
lean::dec(x_22);
lean::inc(x_0);
x_54 = l_lean_parser_syntax_to__format___main(x_0);
x_55 = lean::mk_nat_obj(80u);
x_56 = l_lean_format_pretty(x_54, x_55);
x_57 = l_lean_elaborator_to__level___main___closed__1;
x_58 = lean::string_append(x_57, x_56);
lean::dec(x_56);
x_60 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_58, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_60;
}
else
{
obj* x_63; obj* x_64; obj* x_67; 
x_63 = l_lean_parser_level_trailing_has__view;
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
lean::dec(x_63);
x_67 = lean::apply_1(x_64, x_20);
if (lean::obj_tag(x_67) == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_67);
lean::dec(x_22);
x_70 = l_lean_elaborator_to__level___main___closed__2;
x_71 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_71;
}
else
{
if (lean::obj_tag(x_22) == 0)
{
obj* x_75; obj* x_78; obj* x_80; 
lean::dec(x_0);
x_75 = lean::cnstr_get(x_67, 0);
lean::inc(x_75);
lean::dec(x_67);
x_78 = lean::cnstr_get(x_75, 0);
lean::inc(x_78);
x_80 = l_lean_elaborator_to__level___main(x_78, x_1, x_17);
if (lean::obj_tag(x_80) == 0)
{
obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_75);
x_82 = lean::cnstr_get(x_80, 0);
if (lean::is_exclusive(x_80)) {
 x_84 = x_80;
} else {
 lean::inc(x_82);
 lean::dec(x_80);
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
obj* x_86; obj* x_88; obj* x_89; obj* x_91; obj* x_93; obj* x_94; obj* x_97; obj* x_98; obj* x_101; obj* x_102; 
x_86 = lean::cnstr_get(x_80, 0);
if (lean::is_exclusive(x_80)) {
 x_88 = x_80;
} else {
 lean::inc(x_86);
 lean::dec(x_80);
 x_88 = lean::box(0);
}
x_89 = lean::cnstr_get(x_86, 0);
x_91 = lean::cnstr_get(x_86, 1);
if (lean::is_exclusive(x_86)) {
 x_93 = x_86;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_86);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_75, 2);
lean::inc(x_94);
lean::dec(x_75);
x_97 = l_lean_parser_number_view_to__nat___main(x_94);
x_98 = l_lean_elaborator_level__add___main(x_89, x_97);
lean::dec(x_97);
lean::dec(x_89);
if (lean::is_scalar(x_93)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_93;
}
lean::cnstr_set(x_101, 0, x_98);
lean::cnstr_set(x_101, 1, x_91);
if (lean::is_scalar(x_88)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_88;
}
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
else
{
obj* x_105; obj* x_106; 
lean::dec(x_67);
lean::dec(x_22);
x_105 = l_lean_elaborator_to__level___main___closed__2;
x_106 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_105, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_106;
}
}
}
}
else
{
obj* x_110; obj* x_111; obj* x_114; 
lean::dec(x_41);
x_110 = l_lean_parser_level_leading_has__view;
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
lean::dec(x_110);
x_114 = lean::apply_1(x_111, x_20);
switch (lean::obj_tag(x_114)) {
case 0:
{
lean::dec(x_14);
lean::dec(x_24);
lean::dec(x_114);
if (lean::obj_tag(x_22) == 0)
{
obj* x_118; obj* x_119; 
x_118 = l_lean_elaborator_to__level___main___closed__2;
x_119 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_118, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_119;
}
else
{
obj* x_123; obj* x_125; obj* x_129; 
lean::dec(x_0);
x_123 = lean::cnstr_get(x_22, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_22, 1);
lean::inc(x_125);
lean::dec(x_22);
lean::inc(x_1);
x_129 = l_lean_elaborator_to__level___main(x_123, x_1, x_17);
if (lean::obj_tag(x_129) == 0)
{
obj* x_132; obj* x_134; obj* x_135; 
lean::dec(x_1);
lean::dec(x_125);
x_132 = lean::cnstr_get(x_129, 0);
if (lean::is_exclusive(x_129)) {
 x_134 = x_129;
} else {
 lean::inc(x_132);
 lean::dec(x_129);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_132);
return x_135;
}
else
{
obj* x_136; obj* x_139; obj* x_141; obj* x_144; 
x_136 = lean::cnstr_get(x_129, 0);
lean::inc(x_136);
lean::dec(x_129);
x_139 = lean::cnstr_get(x_136, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_136, 1);
lean::inc(x_141);
lean::dec(x_136);
x_144 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_125, x_1, x_141);
if (lean::obj_tag(x_144) == 0)
{
obj* x_146; obj* x_148; obj* x_149; 
lean::dec(x_139);
x_146 = lean::cnstr_get(x_144, 0);
if (lean::is_exclusive(x_144)) {
 x_148 = x_144;
} else {
 lean::inc(x_146);
 lean::dec(x_144);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_146);
return x_149;
}
else
{
obj* x_150; obj* x_152; obj* x_153; obj* x_155; obj* x_157; obj* x_158; obj* x_160; obj* x_161; 
x_150 = lean::cnstr_get(x_144, 0);
if (lean::is_exclusive(x_144)) {
 x_152 = x_144;
} else {
 lean::inc(x_150);
 lean::dec(x_144);
 x_152 = lean::box(0);
}
x_153 = lean::cnstr_get(x_150, 0);
x_155 = lean::cnstr_get(x_150, 1);
if (lean::is_exclusive(x_150)) {
 x_157 = x_150;
} else {
 lean::inc(x_153);
 lean::inc(x_155);
 lean::dec(x_150);
 x_157 = lean::box(0);
}
x_158 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(x_139, x_153);
lean::dec(x_139);
if (lean::is_scalar(x_157)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_157;
}
lean::cnstr_set(x_160, 0, x_158);
lean::cnstr_set(x_160, 1, x_155);
if (lean::is_scalar(x_152)) {
 x_161 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_161 = x_152;
}
lean::cnstr_set(x_161, 0, x_160);
return x_161;
}
}
}
}
case 1:
{
lean::dec(x_14);
lean::dec(x_24);
lean::dec(x_114);
if (lean::obj_tag(x_22) == 0)
{
obj* x_165; obj* x_166; 
x_165 = l_lean_elaborator_to__level___main___closed__2;
x_166 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_165, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_166;
}
else
{
obj* x_170; obj* x_172; obj* x_176; 
lean::dec(x_0);
x_170 = lean::cnstr_get(x_22, 0);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_22, 1);
lean::inc(x_172);
lean::dec(x_22);
lean::inc(x_1);
x_176 = l_lean_elaborator_to__level___main(x_170, x_1, x_17);
if (lean::obj_tag(x_176) == 0)
{
obj* x_179; obj* x_181; obj* x_182; 
lean::dec(x_172);
lean::dec(x_1);
x_179 = lean::cnstr_get(x_176, 0);
if (lean::is_exclusive(x_176)) {
 x_181 = x_176;
} else {
 lean::inc(x_179);
 lean::dec(x_176);
 x_181 = lean::box(0);
}
if (lean::is_scalar(x_181)) {
 x_182 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_182 = x_181;
}
lean::cnstr_set(x_182, 0, x_179);
return x_182;
}
else
{
obj* x_183; obj* x_186; obj* x_188; obj* x_191; 
x_183 = lean::cnstr_get(x_176, 0);
lean::inc(x_183);
lean::dec(x_176);
x_186 = lean::cnstr_get(x_183, 0);
lean::inc(x_186);
x_188 = lean::cnstr_get(x_183, 1);
lean::inc(x_188);
lean::dec(x_183);
x_191 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_172, x_1, x_188);
if (lean::obj_tag(x_191) == 0)
{
obj* x_193; obj* x_195; obj* x_196; 
lean::dec(x_186);
x_193 = lean::cnstr_get(x_191, 0);
if (lean::is_exclusive(x_191)) {
 x_195 = x_191;
} else {
 lean::inc(x_193);
 lean::dec(x_191);
 x_195 = lean::box(0);
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_196 = x_195;
}
lean::cnstr_set(x_196, 0, x_193);
return x_196;
}
else
{
obj* x_197; obj* x_199; obj* x_200; obj* x_202; obj* x_204; obj* x_205; obj* x_207; obj* x_208; 
x_197 = lean::cnstr_get(x_191, 0);
if (lean::is_exclusive(x_191)) {
 x_199 = x_191;
} else {
 lean::inc(x_197);
 lean::dec(x_191);
 x_199 = lean::box(0);
}
x_200 = lean::cnstr_get(x_197, 0);
x_202 = lean::cnstr_get(x_197, 1);
if (lean::is_exclusive(x_197)) {
 x_204 = x_197;
} else {
 lean::inc(x_200);
 lean::inc(x_202);
 lean::dec(x_197);
 x_204 = lean::box(0);
}
x_205 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(x_186, x_200);
lean::dec(x_186);
if (lean::is_scalar(x_204)) {
 x_207 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_207 = x_204;
}
lean::cnstr_set(x_207, 0, x_205);
lean::cnstr_set(x_207, 1, x_202);
if (lean::is_scalar(x_199)) {
 x_208 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_208 = x_199;
}
lean::cnstr_set(x_208, 0, x_207);
return x_208;
}
}
}
}
case 2:
{
lean::dec(x_114);
if (lean::obj_tag(x_22) == 0)
{
obj* x_212; obj* x_213; obj* x_214; 
lean::dec(x_1);
lean::dec(x_0);
x_212 = l_lean_elaborator_to__level___main___closed__3;
if (lean::is_scalar(x_24)) {
 x_213 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_213 = x_24;
}
lean::cnstr_set(x_213, 0, x_212);
lean::cnstr_set(x_213, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_214 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_214 = x_14;
}
lean::cnstr_set(x_214, 0, x_213);
return x_214;
}
else
{
obj* x_218; obj* x_219; 
lean::dec(x_14);
lean::dec(x_24);
lean::dec(x_22);
x_218 = l_lean_elaborator_to__level___main___closed__2;
x_219 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_218, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_219;
}
}
case 3:
{
obj* x_226; obj* x_227; 
lean::dec(x_14);
lean::dec(x_24);
lean::dec(x_22);
lean::dec(x_114);
x_226 = l_lean_elaborator_to__level___main___closed__2;
x_227 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_226, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_227;
}
case 4:
{
if (lean::obj_tag(x_22) == 0)
{
obj* x_232; obj* x_235; obj* x_236; obj* x_238; obj* x_239; 
lean::dec(x_1);
lean::dec(x_0);
x_232 = lean::cnstr_get(x_114, 0);
lean::inc(x_232);
lean::dec(x_114);
x_235 = l_lean_parser_number_view_to__nat___main(x_232);
x_236 = l_lean_level_of__nat___main(x_235);
lean::dec(x_235);
if (lean::is_scalar(x_24)) {
 x_238 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_238 = x_24;
}
lean::cnstr_set(x_238, 0, x_236);
lean::cnstr_set(x_238, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_239 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_239 = x_14;
}
lean::cnstr_set(x_239, 0, x_238);
return x_239;
}
else
{
obj* x_244; obj* x_245; 
lean::dec(x_14);
lean::dec(x_24);
lean::dec(x_22);
lean::dec(x_114);
x_244 = l_lean_elaborator_to__level___main___closed__2;
x_245 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_244, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_245;
}
}
default:
{
if (lean::obj_tag(x_22) == 0)
{
obj* x_248; obj* x_251; obj* x_252; obj* x_254; obj* x_257; 
x_248 = lean::cnstr_get(x_114, 0);
lean::inc(x_248);
lean::dec(x_114);
x_251 = l_lean_elaborator_mangle__ident(x_248);
x_252 = lean::cnstr_get(x_17, 4);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_252, 1);
lean::inc(x_254);
lean::dec(x_252);
x_257 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_254, x_251);
if (lean::obj_tag(x_257) == 0)
{
obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_265; obj* x_266; obj* x_267; 
lean::dec(x_14);
lean::dec(x_24);
x_260 = l_lean_name_to__string___closed__1;
x_261 = l_lean_name_to__string__with__sep___main(x_260, x_251);
x_262 = l_lean_elaborator_to__level___main___closed__4;
x_263 = lean::string_append(x_262, x_261);
lean::dec(x_261);
x_265 = l_char_has__repr___closed__1;
x_266 = lean::string_append(x_263, x_265);
x_267 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_266, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_267;
}
else
{
obj* x_273; obj* x_274; obj* x_275; 
lean::dec(x_257);
lean::dec(x_1);
lean::dec(x_0);
x_273 = level_mk_param(x_251);
if (lean::is_scalar(x_24)) {
 x_274 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_274 = x_24;
}
lean::cnstr_set(x_274, 0, x_273);
lean::cnstr_set(x_274, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_275 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_275 = x_14;
}
lean::cnstr_set(x_275, 0, x_274);
return x_275;
}
}
else
{
obj* x_280; obj* x_281; 
lean::dec(x_14);
lean::dec(x_24);
lean::dec(x_22);
lean::dec(x_114);
x_280 = l_lean_elaborator_to__level___main___closed__2;
x_281 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_280, x_1, x_17);
lean::dec(x_17);
lean::dec(x_0);
return x_281;
}
}
}
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_0, x_1);
lean::dec(x_1);
return x_2;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_16; obj* x_20; uint8 x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_10 = x_1;
} else {
 lean::inc(x_8);
 lean::dec(x_1);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
x_14 = lean::cnstr_get(x_6, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_6, 1);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_0);
x_20 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(x_0, x_8);
x_21 = 4;
lean::inc(x_11);
x_23 = lean_expr_local(x_11, x_11, x_0, x_21);
x_24 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
x_25 = l_lean_elaborator_expr_mk__annotation(x_24, x_23);
x_26 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_25, x_14);
x_27 = lean_expr_mk_app(x_26, x_16);
if (lean::is_scalar(x_10)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_10;
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
lean::inc(x_0);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_41 = x_32;
} else {
 lean::inc(x_39);
 lean::dec(x_32);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_11;
}
lean::cnstr_set(x_47, 0, x_27);
lean::cnstr_set(x_47, 1, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
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
obj* x_24; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_36; 
x_24 = lean::cnstr_get(x_15, 0);
lean::inc(x_24);
lean::dec(x_15);
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
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_27);
lean::dec(x_31);
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
obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_11);
lean::dec(x_27);
lean::dec(x_31);
lean::dec(x_49);
lean::dec(x_53);
x_60 = lean::cnstr_get(x_54, 0);
if (lean::is_exclusive(x_54)) {
 x_62 = x_54;
} else {
 lean::inc(x_60);
 lean::dec(x_54);
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
obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_64 = lean::cnstr_get(x_54, 0);
if (lean::is_exclusive(x_54)) {
 x_66 = x_54;
} else {
 lean::inc(x_64);
 lean::dec(x_54);
 x_66 = lean::box(0);
}
x_67 = lean::cnstr_get(x_64, 0);
x_69 = lean::cnstr_get(x_64, 1);
if (lean::is_exclusive(x_64)) {
 x_71 = x_64;
} else {
 lean::inc(x_67);
 lean::inc(x_69);
 lean::dec(x_64);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_71;
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
if (lean::is_scalar(x_31)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_31;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_69);
if (lean::is_scalar(x_66)) {
 x_77 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_77 = x_66;
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_41 = x_32;
} else {
 lean::inc(x_39);
 lean::dec(x_32);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_11;
}
lean::cnstr_set(x_47, 0, x_27);
lean::cnstr_set(x_47, 1, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
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
obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
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
x_19 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_21 = x_16;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_16);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_15;
}
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
obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; 
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
x_37 = lean::cnstr_get(x_34, 1);
if (lean::is_exclusive(x_34)) {
 x_39 = x_34;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_34);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_33;
}
lean::cnstr_set(x_40, 0, x_2);
lean::cnstr_set(x_40, 1, x_35);
if (lean::is_scalar(x_39)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_39;
}
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
obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
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
x_19 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_21 = x_16;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_16);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_15;
}
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
obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
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
x_42 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_44 = x_39;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_39);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_2);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
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
obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_64; 
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
x_60 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 x_62 = x_57;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_57);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_56;
}
lean::cnstr_set(x_63, 0, x_2);
lean::cnstr_set(x_63, 1, x_58);
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_62;
}
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_22; 
x_13 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_15 = x_1;
} else {
 lean::inc(x_13);
 lean::dec(x_1);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_16, 2);
lean::inc(x_19);
lean::inc(x_2);
x_22 = l_lean_elaborator_to__pexpr___main(x_19, x_2, x_3);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_2);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_27);
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
obj* x_31; obj* x_34; obj* x_36; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
lean::dec(x_22);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::dec(x_31);
x_39 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_13, x_2, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_15);
lean::dec(x_34);
lean::dec(x_16);
x_43 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_45 = x_39;
} else {
 lean::inc(x_43);
 lean::dec(x_39);
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
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_47 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_49 = x_39;
} else {
 lean::inc(x_47);
 lean::dec(x_39);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 0);
x_52 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_54 = x_47;
} else {
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_47);
 x_54 = lean::box(0);
}
x_55 = lean::box(0);
x_56 = lean::cnstr_get(x_16, 0);
lean::inc(x_56);
lean::dec(x_16);
x_59 = l_lean_elaborator_mangle__ident(x_56);
x_60 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_61 = l_lean_kvmap_set__name(x_55, x_60, x_59);
x_62 = lean_expr_mk_mdata(x_61, x_34);
if (lean::is_scalar(x_15)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_15;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_50);
if (lean::is_scalar(x_54)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_54;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_52);
if (lean::is_scalar(x_49)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_49;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_10);
x_67 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_69 = x_1;
} else {
 lean::inc(x_67);
 lean::dec(x_1);
 x_69 = lean::box(0);
}
x_70 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_72 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_72) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_2);
lean::dec(x_69);
lean::dec(x_67);
x_77 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_79 = x_72;
} else {
 lean::inc(x_77);
 lean::dec(x_72);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
return x_80;
}
else
{
obj* x_81; obj* x_84; obj* x_86; obj* x_89; 
x_81 = lean::cnstr_get(x_72, 0);
lean::inc(x_81);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_81, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_81, 1);
lean::inc(x_86);
lean::dec(x_81);
x_89 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_67, x_2, x_86);
if (lean::obj_tag(x_89) == 0)
{
obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_69);
lean::dec(x_84);
x_92 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_94 = x_89;
} else {
 lean::inc(x_92);
 lean::dec(x_89);
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
obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_96 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_98 = x_89;
} else {
 lean::inc(x_96);
 lean::dec(x_89);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_96, 0);
x_101 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 x_103 = x_96;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_96);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_104 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_104 = x_69;
}
lean::cnstr_set(x_104, 0, x_84);
lean::cnstr_set(x_104, 1, x_99);
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_103;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_101);
if (lean::is_scalar(x_98)) {
 x_106 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_106 = x_98;
}
lean::cnstr_set(x_106, 0, x_105);
return x_106;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
lean::dec(x_10);
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
x_17 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_19 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_17, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_26 = x_19;
} else {
 lean::inc(x_24);
 lean::dec(x_19);
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
obj* x_28; obj* x_31; obj* x_33; obj* x_36; 
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
lean::dec(x_19);
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
lean::dec(x_28);
x_36 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_14, x_2, x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_16);
lean::dec(x_31);
x_39 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_41 = x_36;
} else {
 lean::inc(x_39);
 lean::dec(x_36);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_45 = x_36;
} else {
 lean::inc(x_43);
 lean::dec(x_36);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_16;
}
lean::cnstr_set(x_51, 0, x_31);
lean::cnstr_set(x_51, 1, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
obj* x_54; obj* x_57; 
x_54 = lean::cnstr_get(x_10, 0);
lean::inc(x_54);
lean::dec(x_10);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_57) == 0)
{
obj* x_60; obj* x_62; obj* x_63; obj* x_65; 
x_60 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_62 = x_1;
} else {
 lean::inc(x_60);
 lean::dec(x_1);
 x_62 = lean::box(0);
}
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_65 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_63, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_65) == 0)
{
obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_2);
lean::dec(x_62);
lean::dec(x_60);
x_70 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_72 = x_65;
} else {
 lean::inc(x_70);
 lean::dec(x_65);
 x_72 = lean::box(0);
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
obj* x_74; obj* x_77; obj* x_79; obj* x_82; 
x_74 = lean::cnstr_get(x_65, 0);
lean::inc(x_74);
lean::dec(x_65);
x_77 = lean::cnstr_get(x_74, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 1);
lean::inc(x_79);
lean::dec(x_74);
x_82 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_60, x_2, x_79);
if (lean::obj_tag(x_82) == 0)
{
obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_62);
lean::dec(x_77);
x_85 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 x_87 = x_82;
} else {
 lean::inc(x_85);
 lean::dec(x_82);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_89 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 x_91 = x_82;
} else {
 lean::inc(x_89);
 lean::dec(x_82);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_89, 0);
x_94 = lean::cnstr_get(x_89, 1);
if (lean::is_exclusive(x_89)) {
 x_96 = x_89;
} else {
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_89);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_97 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_97 = x_62;
}
lean::cnstr_set(x_97, 0, x_77);
lean::cnstr_set(x_97, 1, x_92);
if (lean::is_scalar(x_96)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_96;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_94);
if (lean::is_scalar(x_91)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_91;
}
lean::cnstr_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
obj* x_100; obj* x_102; obj* x_103; obj* x_107; 
x_100 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_102 = x_1;
} else {
 lean::inc(x_100);
 lean::dec(x_1);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_57, 0);
lean::inc(x_103);
lean::dec(x_57);
lean::inc(x_2);
x_107 = l_lean_elaborator_to__pexpr___main(x_103, x_2, x_3);
if (lean::obj_tag(x_107) == 0)
{
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_2);
lean::dec(x_102);
lean::dec(x_100);
x_111 = lean::cnstr_get(x_107, 0);
if (lean::is_exclusive(x_107)) {
 x_113 = x_107;
} else {
 lean::inc(x_111);
 lean::dec(x_107);
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
obj* x_115; obj* x_118; obj* x_120; obj* x_123; 
x_115 = lean::cnstr_get(x_107, 0);
lean::inc(x_115);
lean::dec(x_107);
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
lean::dec(x_115);
x_123 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_100, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_102);
lean::dec(x_118);
x_126 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_128 = x_123;
} else {
 lean::inc(x_126);
 lean::dec(x_123);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
return x_129;
}
else
{
obj* x_130; obj* x_132; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_130 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_132 = x_123;
} else {
 lean::inc(x_130);
 lean::dec(x_123);
 x_132 = lean::box(0);
}
x_133 = lean::cnstr_get(x_130, 0);
x_135 = lean::cnstr_get(x_130, 1);
if (lean::is_exclusive(x_130)) {
 x_137 = x_130;
} else {
 lean::inc(x_133);
 lean::inc(x_135);
 lean::dec(x_130);
 x_137 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_138 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_138 = x_102;
}
lean::cnstr_set(x_138, 0, x_118);
lean::cnstr_set(x_138, 1, x_133);
if (lean::is_scalar(x_137)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_137;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_135);
if (lean::is_scalar(x_132)) {
 x_140 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_140 = x_132;
}
lean::cnstr_set(x_140, 0, x_139);
return x_140;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_22; 
x_13 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_15 = x_1;
} else {
 lean::inc(x_13);
 lean::dec(x_1);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_16, 2);
lean::inc(x_19);
lean::inc(x_2);
x_22 = l_lean_elaborator_to__pexpr___main(x_19, x_2, x_3);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_2);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_27);
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
obj* x_31; obj* x_34; obj* x_36; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
lean::dec(x_22);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::dec(x_31);
x_39 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_13, x_2, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_15);
lean::dec(x_34);
lean::dec(x_16);
x_43 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_45 = x_39;
} else {
 lean::inc(x_43);
 lean::dec(x_39);
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
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_47 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_49 = x_39;
} else {
 lean::inc(x_47);
 lean::dec(x_39);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 0);
x_52 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_54 = x_47;
} else {
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_47);
 x_54 = lean::box(0);
}
x_55 = lean::box(0);
x_56 = lean::cnstr_get(x_16, 0);
lean::inc(x_56);
lean::dec(x_16);
x_59 = l_lean_elaborator_mangle__ident(x_56);
x_60 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_61 = l_lean_kvmap_set__name(x_55, x_60, x_59);
x_62 = lean_expr_mk_mdata(x_61, x_34);
if (lean::is_scalar(x_15)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_15;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_50);
if (lean::is_scalar(x_54)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_54;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_52);
if (lean::is_scalar(x_49)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_49;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_10);
x_67 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_69 = x_1;
} else {
 lean::inc(x_67);
 lean::dec(x_1);
 x_69 = lean::box(0);
}
x_70 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_72 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_72) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_2);
lean::dec(x_69);
lean::dec(x_67);
x_77 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_79 = x_72;
} else {
 lean::inc(x_77);
 lean::dec(x_72);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
return x_80;
}
else
{
obj* x_81; obj* x_84; obj* x_86; obj* x_89; 
x_81 = lean::cnstr_get(x_72, 0);
lean::inc(x_81);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_81, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_81, 1);
lean::inc(x_86);
lean::dec(x_81);
x_89 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_67, x_2, x_86);
if (lean::obj_tag(x_89) == 0)
{
obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_69);
lean::dec(x_84);
x_92 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_94 = x_89;
} else {
 lean::inc(x_92);
 lean::dec(x_89);
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
obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_96 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_98 = x_89;
} else {
 lean::inc(x_96);
 lean::dec(x_89);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_96, 0);
x_101 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 x_103 = x_96;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_96);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_104 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_104 = x_69;
}
lean::cnstr_set(x_104, 0, x_84);
lean::cnstr_set(x_104, 1, x_99);
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_103;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_101);
if (lean::is_scalar(x_98)) {
 x_106 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_106 = x_98;
}
lean::cnstr_set(x_106, 0, x_105);
return x_106;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
lean::dec(x_10);
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
x_17 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_19 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_17, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_26 = x_19;
} else {
 lean::inc(x_24);
 lean::dec(x_19);
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
obj* x_28; obj* x_31; obj* x_33; obj* x_36; 
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
lean::dec(x_19);
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
lean::dec(x_28);
x_36 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_14, x_2, x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_16);
lean::dec(x_31);
x_39 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_41 = x_36;
} else {
 lean::inc(x_39);
 lean::dec(x_36);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_45 = x_36;
} else {
 lean::inc(x_43);
 lean::dec(x_36);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_16;
}
lean::cnstr_set(x_51, 0, x_31);
lean::cnstr_set(x_51, 1, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
obj* x_54; obj* x_57; 
x_54 = lean::cnstr_get(x_10, 0);
lean::inc(x_54);
lean::dec(x_10);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_57) == 0)
{
obj* x_60; obj* x_62; obj* x_63; obj* x_65; 
x_60 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_62 = x_1;
} else {
 lean::inc(x_60);
 lean::dec(x_1);
 x_62 = lean::box(0);
}
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_65 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_63, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_65) == 0)
{
obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_2);
lean::dec(x_62);
lean::dec(x_60);
x_70 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_72 = x_65;
} else {
 lean::inc(x_70);
 lean::dec(x_65);
 x_72 = lean::box(0);
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
obj* x_74; obj* x_77; obj* x_79; obj* x_82; 
x_74 = lean::cnstr_get(x_65, 0);
lean::inc(x_74);
lean::dec(x_65);
x_77 = lean::cnstr_get(x_74, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 1);
lean::inc(x_79);
lean::dec(x_74);
x_82 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_60, x_2, x_79);
if (lean::obj_tag(x_82) == 0)
{
obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_62);
lean::dec(x_77);
x_85 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 x_87 = x_82;
} else {
 lean::inc(x_85);
 lean::dec(x_82);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_89 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 x_91 = x_82;
} else {
 lean::inc(x_89);
 lean::dec(x_82);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_89, 0);
x_94 = lean::cnstr_get(x_89, 1);
if (lean::is_exclusive(x_89)) {
 x_96 = x_89;
} else {
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_89);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_97 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_97 = x_62;
}
lean::cnstr_set(x_97, 0, x_77);
lean::cnstr_set(x_97, 1, x_92);
if (lean::is_scalar(x_96)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_96;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_94);
if (lean::is_scalar(x_91)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_91;
}
lean::cnstr_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
obj* x_100; obj* x_102; obj* x_103; obj* x_107; 
x_100 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_102 = x_1;
} else {
 lean::inc(x_100);
 lean::dec(x_1);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_57, 0);
lean::inc(x_103);
lean::dec(x_57);
lean::inc(x_2);
x_107 = l_lean_elaborator_to__pexpr___main(x_103, x_2, x_3);
if (lean::obj_tag(x_107) == 0)
{
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_2);
lean::dec(x_102);
lean::dec(x_100);
x_111 = lean::cnstr_get(x_107, 0);
if (lean::is_exclusive(x_107)) {
 x_113 = x_107;
} else {
 lean::inc(x_111);
 lean::dec(x_107);
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
obj* x_115; obj* x_118; obj* x_120; obj* x_123; 
x_115 = lean::cnstr_get(x_107, 0);
lean::inc(x_115);
lean::dec(x_107);
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
lean::dec(x_115);
x_123 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_100, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_102);
lean::dec(x_118);
x_126 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_128 = x_123;
} else {
 lean::inc(x_126);
 lean::dec(x_123);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
return x_129;
}
else
{
obj* x_130; obj* x_132; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_130 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_132 = x_123;
} else {
 lean::inc(x_130);
 lean::dec(x_123);
 x_132 = lean::box(0);
}
x_133 = lean::cnstr_get(x_130, 0);
x_135 = lean::cnstr_get(x_130, 1);
if (lean::is_exclusive(x_130)) {
 x_137 = x_130;
} else {
 lean::inc(x_133);
 lean::inc(x_135);
 lean::dec(x_130);
 x_137 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_138 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_138 = x_102;
}
lean::cnstr_set(x_138, 0, x_118);
lean::cnstr_set(x_138, 1, x_133);
if (lean::is_scalar(x_137)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_137;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_135);
if (lean::is_scalar(x_132)) {
 x_140 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_140 = x_132;
}
lean::cnstr_set(x_140, 0, x_139);
return x_140;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_22; 
x_13 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_15 = x_1;
} else {
 lean::inc(x_13);
 lean::dec(x_1);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_16, 2);
lean::inc(x_19);
lean::inc(x_2);
x_22 = l_lean_elaborator_to__pexpr___main(x_19, x_2, x_3);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_2);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_27);
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
obj* x_31; obj* x_34; obj* x_36; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
lean::dec(x_22);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::dec(x_31);
x_39 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_13, x_2, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_15);
lean::dec(x_34);
lean::dec(x_16);
x_43 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_45 = x_39;
} else {
 lean::inc(x_43);
 lean::dec(x_39);
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
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_47 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_49 = x_39;
} else {
 lean::inc(x_47);
 lean::dec(x_39);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 0);
x_52 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_54 = x_47;
} else {
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_47);
 x_54 = lean::box(0);
}
x_55 = lean::box(0);
x_56 = lean::cnstr_get(x_16, 0);
lean::inc(x_56);
lean::dec(x_16);
x_59 = l_lean_elaborator_mangle__ident(x_56);
x_60 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_61 = l_lean_kvmap_set__name(x_55, x_60, x_59);
x_62 = lean_expr_mk_mdata(x_61, x_34);
if (lean::is_scalar(x_15)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_15;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_50);
if (lean::is_scalar(x_54)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_54;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_52);
if (lean::is_scalar(x_49)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_49;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_10);
x_67 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_69 = x_1;
} else {
 lean::inc(x_67);
 lean::dec(x_1);
 x_69 = lean::box(0);
}
x_70 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_72 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_72) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_2);
lean::dec(x_69);
lean::dec(x_67);
x_77 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_79 = x_72;
} else {
 lean::inc(x_77);
 lean::dec(x_72);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
return x_80;
}
else
{
obj* x_81; obj* x_84; obj* x_86; obj* x_89; 
x_81 = lean::cnstr_get(x_72, 0);
lean::inc(x_81);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_81, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_81, 1);
lean::inc(x_86);
lean::dec(x_81);
x_89 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_67, x_2, x_86);
if (lean::obj_tag(x_89) == 0)
{
obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_69);
lean::dec(x_84);
x_92 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_94 = x_89;
} else {
 lean::inc(x_92);
 lean::dec(x_89);
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
obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_96 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_98 = x_89;
} else {
 lean::inc(x_96);
 lean::dec(x_89);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_96, 0);
x_101 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 x_103 = x_96;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_96);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_104 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_104 = x_69;
}
lean::cnstr_set(x_104, 0, x_84);
lean::cnstr_set(x_104, 1, x_99);
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_103;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_101);
if (lean::is_scalar(x_98)) {
 x_106 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_106 = x_98;
}
lean::cnstr_set(x_106, 0, x_105);
return x_106;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
lean::dec(x_10);
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
x_17 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_19 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_17, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_26 = x_19;
} else {
 lean::inc(x_24);
 lean::dec(x_19);
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
obj* x_28; obj* x_31; obj* x_33; obj* x_36; 
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
lean::dec(x_19);
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
lean::dec(x_28);
x_36 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_14, x_2, x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_16);
lean::dec(x_31);
x_39 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_41 = x_36;
} else {
 lean::inc(x_39);
 lean::dec(x_36);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_45 = x_36;
} else {
 lean::inc(x_43);
 lean::dec(x_36);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_16;
}
lean::cnstr_set(x_51, 0, x_31);
lean::cnstr_set(x_51, 1, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
obj* x_54; obj* x_57; 
x_54 = lean::cnstr_get(x_10, 0);
lean::inc(x_54);
lean::dec(x_10);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_57) == 0)
{
obj* x_60; obj* x_62; obj* x_63; obj* x_65; 
x_60 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_62 = x_1;
} else {
 lean::inc(x_60);
 lean::dec(x_1);
 x_62 = lean::box(0);
}
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_65 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_63, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_65) == 0)
{
obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_2);
lean::dec(x_62);
lean::dec(x_60);
x_70 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_72 = x_65;
} else {
 lean::inc(x_70);
 lean::dec(x_65);
 x_72 = lean::box(0);
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
obj* x_74; obj* x_77; obj* x_79; obj* x_82; 
x_74 = lean::cnstr_get(x_65, 0);
lean::inc(x_74);
lean::dec(x_65);
x_77 = lean::cnstr_get(x_74, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 1);
lean::inc(x_79);
lean::dec(x_74);
x_82 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_60, x_2, x_79);
if (lean::obj_tag(x_82) == 0)
{
obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_62);
lean::dec(x_77);
x_85 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 x_87 = x_82;
} else {
 lean::inc(x_85);
 lean::dec(x_82);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_89 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 x_91 = x_82;
} else {
 lean::inc(x_89);
 lean::dec(x_82);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_89, 0);
x_94 = lean::cnstr_get(x_89, 1);
if (lean::is_exclusive(x_89)) {
 x_96 = x_89;
} else {
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_89);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_97 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_97 = x_62;
}
lean::cnstr_set(x_97, 0, x_77);
lean::cnstr_set(x_97, 1, x_92);
if (lean::is_scalar(x_96)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_96;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_94);
if (lean::is_scalar(x_91)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_91;
}
lean::cnstr_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
obj* x_100; obj* x_102; obj* x_103; obj* x_107; 
x_100 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_102 = x_1;
} else {
 lean::inc(x_100);
 lean::dec(x_1);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_57, 0);
lean::inc(x_103);
lean::dec(x_57);
lean::inc(x_2);
x_107 = l_lean_elaborator_to__pexpr___main(x_103, x_2, x_3);
if (lean::obj_tag(x_107) == 0)
{
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_2);
lean::dec(x_102);
lean::dec(x_100);
x_111 = lean::cnstr_get(x_107, 0);
if (lean::is_exclusive(x_107)) {
 x_113 = x_107;
} else {
 lean::inc(x_111);
 lean::dec(x_107);
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
obj* x_115; obj* x_118; obj* x_120; obj* x_123; 
x_115 = lean::cnstr_get(x_107, 0);
lean::inc(x_115);
lean::dec(x_107);
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
lean::dec(x_115);
x_123 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_100, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_102);
lean::dec(x_118);
x_126 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_128 = x_123;
} else {
 lean::inc(x_126);
 lean::dec(x_123);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
return x_129;
}
else
{
obj* x_130; obj* x_132; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_130 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_132 = x_123;
} else {
 lean::inc(x_130);
 lean::dec(x_123);
 x_132 = lean::box(0);
}
x_133 = lean::cnstr_get(x_130, 0);
x_135 = lean::cnstr_get(x_130, 1);
if (lean::is_exclusive(x_130)) {
 x_137 = x_130;
} else {
 lean::inc(x_133);
 lean::inc(x_135);
 lean::dec(x_130);
 x_137 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_138 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_138 = x_102;
}
lean::cnstr_set(x_138, 0, x_118);
lean::cnstr_set(x_138, 1, x_133);
if (lean::is_scalar(x_137)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_137;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_135);
if (lean::is_scalar(x_132)) {
 x_140 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_140 = x_132;
}
lean::cnstr_set(x_140, 0, x_139);
return x_140;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_22; 
x_13 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_15 = x_1;
} else {
 lean::inc(x_13);
 lean::dec(x_1);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_16, 2);
lean::inc(x_19);
lean::inc(x_2);
x_22 = l_lean_elaborator_to__pexpr___main(x_19, x_2, x_3);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_2);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_27);
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
obj* x_31; obj* x_34; obj* x_36; obj* x_39; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
lean::dec(x_22);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::dec(x_31);
x_39 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_13, x_2, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_15);
lean::dec(x_34);
lean::dec(x_16);
x_43 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_45 = x_39;
} else {
 lean::inc(x_43);
 lean::dec(x_39);
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
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_47 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_49 = x_39;
} else {
 lean::inc(x_47);
 lean::dec(x_39);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 0);
x_52 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_54 = x_47;
} else {
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_47);
 x_54 = lean::box(0);
}
x_55 = lean::box(0);
x_56 = lean::cnstr_get(x_16, 0);
lean::inc(x_56);
lean::dec(x_16);
x_59 = l_lean_elaborator_mangle__ident(x_56);
x_60 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_61 = l_lean_kvmap_set__name(x_55, x_60, x_59);
x_62 = lean_expr_mk_mdata(x_61, x_34);
if (lean::is_scalar(x_15)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_15;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_50);
if (lean::is_scalar(x_54)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_54;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_52);
if (lean::is_scalar(x_49)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_49;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_10);
x_67 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_69 = x_1;
} else {
 lean::inc(x_67);
 lean::dec(x_1);
 x_69 = lean::box(0);
}
x_70 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_72 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_72) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_2);
lean::dec(x_69);
lean::dec(x_67);
x_77 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_79 = x_72;
} else {
 lean::inc(x_77);
 lean::dec(x_72);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
return x_80;
}
else
{
obj* x_81; obj* x_84; obj* x_86; obj* x_89; 
x_81 = lean::cnstr_get(x_72, 0);
lean::inc(x_81);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_81, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_81, 1);
lean::inc(x_86);
lean::dec(x_81);
x_89 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_67, x_2, x_86);
if (lean::obj_tag(x_89) == 0)
{
obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_69);
lean::dec(x_84);
x_92 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_94 = x_89;
} else {
 lean::inc(x_92);
 lean::dec(x_89);
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
obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_96 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_98 = x_89;
} else {
 lean::inc(x_96);
 lean::dec(x_89);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_96, 0);
x_101 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 x_103 = x_96;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_96);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_104 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_104 = x_69;
}
lean::cnstr_set(x_104, 0, x_84);
lean::cnstr_set(x_104, 1, x_99);
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_103;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_101);
if (lean::is_scalar(x_98)) {
 x_106 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_106 = x_98;
}
lean::cnstr_set(x_106, 0, x_105);
return x_106;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
lean::dec(x_10);
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
x_17 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_19 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_17, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_26 = x_19;
} else {
 lean::inc(x_24);
 lean::dec(x_19);
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
obj* x_28; obj* x_31; obj* x_33; obj* x_36; 
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
lean::dec(x_19);
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
lean::dec(x_28);
x_36 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_14, x_2, x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_16);
lean::dec(x_31);
x_39 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_41 = x_36;
} else {
 lean::inc(x_39);
 lean::dec(x_36);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_45 = x_36;
} else {
 lean::inc(x_43);
 lean::dec(x_36);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_16;
}
lean::cnstr_set(x_51, 0, x_31);
lean::cnstr_set(x_51, 1, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
obj* x_54; obj* x_57; 
x_54 = lean::cnstr_get(x_10, 0);
lean::inc(x_54);
lean::dec(x_10);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_57) == 0)
{
obj* x_60; obj* x_62; obj* x_63; obj* x_65; 
x_60 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_62 = x_1;
} else {
 lean::inc(x_60);
 lean::dec(x_1);
 x_62 = lean::box(0);
}
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_2);
x_65 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_63, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_65) == 0)
{
obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_2);
lean::dec(x_62);
lean::dec(x_60);
x_70 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_72 = x_65;
} else {
 lean::inc(x_70);
 lean::dec(x_65);
 x_72 = lean::box(0);
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
obj* x_74; obj* x_77; obj* x_79; obj* x_82; 
x_74 = lean::cnstr_get(x_65, 0);
lean::inc(x_74);
lean::dec(x_65);
x_77 = lean::cnstr_get(x_74, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 1);
lean::inc(x_79);
lean::dec(x_74);
x_82 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_60, x_2, x_79);
if (lean::obj_tag(x_82) == 0)
{
obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_62);
lean::dec(x_77);
x_85 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 x_87 = x_82;
} else {
 lean::inc(x_85);
 lean::dec(x_82);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_89 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 x_91 = x_82;
} else {
 lean::inc(x_89);
 lean::dec(x_82);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_89, 0);
x_94 = lean::cnstr_get(x_89, 1);
if (lean::is_exclusive(x_89)) {
 x_96 = x_89;
} else {
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_89);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_97 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_97 = x_62;
}
lean::cnstr_set(x_97, 0, x_77);
lean::cnstr_set(x_97, 1, x_92);
if (lean::is_scalar(x_96)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_96;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_94);
if (lean::is_scalar(x_91)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_91;
}
lean::cnstr_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
obj* x_100; obj* x_102; obj* x_103; obj* x_107; 
x_100 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_102 = x_1;
} else {
 lean::inc(x_100);
 lean::dec(x_1);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_57, 0);
lean::inc(x_103);
lean::dec(x_57);
lean::inc(x_2);
x_107 = l_lean_elaborator_to__pexpr___main(x_103, x_2, x_3);
if (lean::obj_tag(x_107) == 0)
{
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_2);
lean::dec(x_102);
lean::dec(x_100);
x_111 = lean::cnstr_get(x_107, 0);
if (lean::is_exclusive(x_107)) {
 x_113 = x_107;
} else {
 lean::inc(x_111);
 lean::dec(x_107);
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
obj* x_115; obj* x_118; obj* x_120; obj* x_123; 
x_115 = lean::cnstr_get(x_107, 0);
lean::inc(x_115);
lean::dec(x_107);
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
lean::dec(x_115);
x_123 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_100, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_102);
lean::dec(x_118);
x_126 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_128 = x_123;
} else {
 lean::inc(x_126);
 lean::dec(x_123);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
return x_129;
}
else
{
obj* x_130; obj* x_132; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_130 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_132 = x_123;
} else {
 lean::inc(x_130);
 lean::dec(x_123);
 x_132 = lean::box(0);
}
x_133 = lean::cnstr_get(x_130, 0);
x_135 = lean::cnstr_get(x_130, 1);
if (lean::is_exclusive(x_130)) {
 x_137 = x_130;
} else {
 lean::inc(x_133);
 lean::inc(x_135);
 lean::dec(x_130);
 x_137 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_138 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_138 = x_102;
}
lean::cnstr_set(x_138, 0, x_118);
lean::cnstr_set(x_138, 1, x_133);
if (lean::is_scalar(x_137)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_137;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_135);
if (lean::is_scalar(x_132)) {
 x_140 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_140 = x_132;
}
lean::cnstr_set(x_140, 0, x_139);
return x_140;
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
x_41 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_43 = x_36;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_36);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
x_41 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_43 = x_36;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_36);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
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
return x_1;
}
}
obj* l_lean_elaborator_to__pexpr___main___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_to__pexpr___main___lambda__1___boxed), 1, 0);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_to__pexpr___main___lambda__2___boxed), 1, 0);
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
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_65; 
x_59 = l_lean_name_to__string___closed__1;
x_60 = l_lean_name_to__string__with__sep___main(x_59, x_7);
x_61 = l_lean_elaborator_to__pexpr___main___closed__23;
x_62 = lean::string_append(x_61, x_60);
lean::dec(x_60);
lean::inc(x_1);
x_65 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_62, x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_65) == 0)
{
obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_1);
lean::dec(x_0);
x_69 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_71 = x_65;
} else {
 lean::inc(x_69);
 lean::dec(x_65);
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
obj* x_73; obj* x_75; 
x_73 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_set(x_65, 0, lean::box(0));
 x_75 = x_65;
} else {
 lean::inc(x_73);
 lean::dec(x_65);
 x_75 = lean::box(0);
}
if (x_21 == 0)
{
obj* x_76; obj* x_78; obj* x_80; obj* x_81; 
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
x_81 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_81) == 0)
{
obj* x_84; obj* x_85; 
lean::dec(x_1);
if (lean::is_scalar(x_80)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_80;
}
lean::cnstr_set(x_84, 0, x_76);
lean::cnstr_set(x_84, 1, x_78);
if (lean::is_scalar(x_75)) {
 x_85 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_85 = x_75;
}
lean::cnstr_set(x_85, 0, x_84);
return x_85;
}
else
{
obj* x_86; obj* x_89; obj* x_92; obj* x_95; obj* x_96; obj* x_97; obj* x_99; obj* x_100; obj* x_101; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_86 = lean::cnstr_get(x_81, 0);
lean::inc(x_86);
lean::dec(x_81);
x_89 = lean::cnstr_get(x_1, 0);
lean::inc(x_89);
lean::dec(x_1);
x_92 = lean::cnstr_get(x_89, 2);
lean::inc(x_92);
lean::dec(x_89);
x_95 = l_lean_file__map_to__position(x_92, x_86);
x_96 = lean::box(0);
x_97 = lean::cnstr_get(x_95, 1);
lean::inc(x_97);
x_99 = l_lean_elaborator_to__pexpr___main___closed__3;
x_100 = l_lean_kvmap_set__nat(x_96, x_99, x_97);
x_101 = lean::cnstr_get(x_95, 0);
lean::inc(x_101);
lean::dec(x_95);
x_104 = l_lean_elaborator_to__pexpr___main___closed__4;
x_105 = l_lean_kvmap_set__nat(x_100, x_104, x_101);
x_106 = lean_expr_mk_mdata(x_105, x_76);
if (lean::is_scalar(x_80)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_80;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_78);
if (lean::is_scalar(x_75)) {
 x_108 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_108 = x_75;
}
lean::cnstr_set(x_108, 0, x_107);
return x_108;
}
}
else
{
obj* x_111; obj* x_113; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_1);
lean::dec(x_0);
x_111 = lean::cnstr_get(x_73, 0);
x_113 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 x_115 = x_73;
} else {
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_73);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_111);
lean::cnstr_set(x_116, 1, x_113);
if (lean::is_scalar(x_75)) {
 x_117 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_117 = x_75;
}
lean::cnstr_set(x_117, 0, x_116);
return x_117;
}
}
}
else
{
obj* x_118; obj* x_119; obj* x_123; obj* x_124; obj* x_126; obj* x_128; 
x_118 = l_lean_parser_term_match_has__view;
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
lean::dec(x_118);
lean::inc(x_0);
x_123 = lean::apply_1(x_119, x_0);
x_124 = lean::cnstr_get(x_123, 5);
lean::inc(x_124);
x_126 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(x_124);
lean::inc(x_1);
x_128 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_126, x_1, x_2);
if (lean::obj_tag(x_128) == 0)
{
obj* x_130; obj* x_132; obj* x_133; 
lean::dec(x_123);
x_130 = lean::cnstr_get(x_128, 0);
if (lean::is_exclusive(x_128)) {
 x_132 = x_128;
} else {
 lean::inc(x_130);
 lean::dec(x_128);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_130);
x_12 = x_133;
goto lbl_13;
}
else
{
obj* x_134; obj* x_137; obj* x_139; obj* x_142; obj* x_144; obj* x_147; 
x_134 = lean::cnstr_get(x_128, 0);
lean::inc(x_134);
lean::dec(x_128);
x_137 = lean::cnstr_get(x_134, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_134, 1);
lean::inc(x_139);
lean::dec(x_134);
x_142 = lean::cnstr_get(x_123, 2);
lean::inc(x_142);
x_144 = l_lean_expander_get__opt__type___main(x_142);
lean::dec(x_142);
lean::inc(x_1);
x_147 = l_lean_elaborator_to__pexpr___main(x_144, x_1, x_139);
if (lean::obj_tag(x_147) == 0)
{
obj* x_150; obj* x_152; obj* x_153; 
lean::dec(x_137);
lean::dec(x_123);
x_150 = lean::cnstr_get(x_147, 0);
if (lean::is_exclusive(x_147)) {
 x_152 = x_147;
} else {
 lean::inc(x_150);
 lean::dec(x_147);
 x_152 = lean::box(0);
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_150);
x_12 = x_153;
goto lbl_13;
}
else
{
obj* x_154; obj* x_157; obj* x_159; obj* x_162; 
x_154 = lean::cnstr_get(x_147, 0);
lean::inc(x_154);
lean::dec(x_147);
x_157 = lean::cnstr_get(x_154, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_154, 1);
lean::inc(x_159);
lean::dec(x_154);
x_162 = l_lean_elaborator_mk__eqns(x_157, x_137);
switch (lean::obj_tag(x_162)) {
case 10:
{
obj* x_163; obj* x_165; obj* x_168; obj* x_172; 
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_162, 1);
lean::inc(x_165);
lean::dec(x_162);
x_168 = lean::cnstr_get(x_123, 1);
lean::inc(x_168);
lean::dec(x_123);
lean::inc(x_1);
x_172 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_168, x_1, x_159);
if (lean::obj_tag(x_172) == 0)
{
obj* x_175; obj* x_177; obj* x_178; 
lean::dec(x_163);
lean::dec(x_165);
x_175 = lean::cnstr_get(x_172, 0);
if (lean::is_exclusive(x_172)) {
 x_177 = x_172;
} else {
 lean::inc(x_175);
 lean::dec(x_172);
 x_177 = lean::box(0);
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_175);
x_12 = x_178;
goto lbl_13;
}
else
{
obj* x_179; obj* x_181; obj* x_182; obj* x_184; obj* x_186; obj* x_187; uint8 x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
x_179 = lean::cnstr_get(x_172, 0);
if (lean::is_exclusive(x_172)) {
 x_181 = x_172;
} else {
 lean::inc(x_179);
 lean::dec(x_172);
 x_181 = lean::box(0);
}
x_182 = lean::cnstr_get(x_179, 0);
x_184 = lean::cnstr_get(x_179, 1);
if (lean::is_exclusive(x_179)) {
 x_186 = x_179;
} else {
 lean::inc(x_182);
 lean::inc(x_184);
 lean::dec(x_179);
 x_186 = lean::box(0);
}
x_187 = l_lean_elaborator_to__pexpr___main___closed__24;
x_188 = 1;
x_189 = l_lean_kvmap_set__bool(x_163, x_187, x_188);
x_190 = lean_expr_mk_mdata(x_189, x_165);
x_191 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_190, x_182);
if (lean::is_scalar(x_186)) {
 x_192 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_192 = x_186;
}
lean::cnstr_set(x_192, 0, x_191);
lean::cnstr_set(x_192, 1, x_184);
if (lean::is_scalar(x_181)) {
 x_193 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_193 = x_181;
}
lean::cnstr_set(x_193, 0, x_192);
x_12 = x_193;
goto lbl_13;
}
}
default:
{
obj* x_196; obj* x_198; 
lean::dec(x_162);
lean::dec(x_123);
x_196 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
lean::inc(x_1);
x_198 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_196, x_1, x_159);
lean::dec(x_159);
x_12 = x_198;
goto lbl_13;
}
}
}
}
}
}
else
{
obj* x_200; obj* x_201; obj* x_205; obj* x_206; obj* x_208; obj* x_209; obj* x_211; obj* x_214; obj* x_215; 
x_200 = l_lean_parser_term_struct__inst_has__view;
x_201 = lean::cnstr_get(x_200, 0);
lean::inc(x_201);
lean::dec(x_200);
lean::inc(x_0);
x_205 = lean::apply_1(x_201, x_0);
x_206 = lean::cnstr_get(x_205, 3);
lean::inc(x_206);
x_208 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_206);
x_209 = lean::cnstr_get(x_208, 0);
lean::inc(x_209);
x_211 = lean::cnstr_get(x_208, 1);
lean::inc(x_211);
lean::dec(x_208);
x_214 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_211);
x_215 = lean::cnstr_get(x_214, 1);
lean::inc(x_215);
if (lean::obj_tag(x_215) == 0)
{
obj* x_217; obj* x_221; 
x_217 = lean::cnstr_get(x_214, 0);
lean::inc(x_217);
lean::dec(x_214);
lean::inc(x_1);
x_221 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_209, x_1, x_2);
if (lean::obj_tag(x_221) == 0)
{
obj* x_227; obj* x_229; obj* x_230; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_217);
lean::dec(x_205);
x_227 = lean::cnstr_get(x_221, 0);
if (lean::is_exclusive(x_221)) {
 x_229 = x_221;
} else {
 lean::inc(x_227);
 lean::dec(x_221);
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
obj* x_231; obj* x_234; obj* x_236; obj* x_239; obj* x_242; 
x_231 = lean::cnstr_get(x_221, 0);
lean::inc(x_231);
lean::dec(x_221);
x_234 = lean::cnstr_get(x_231, 0);
lean::inc(x_234);
x_236 = lean::cnstr_get(x_231, 1);
lean::inc(x_236);
lean::dec(x_231);
lean::inc(x_1);
x_242 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_217, x_1, x_236);
if (lean::obj_tag(x_242) == 0)
{
obj* x_248; obj* x_250; obj* x_251; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
lean::dec(x_234);
x_248 = lean::cnstr_get(x_242, 0);
if (lean::is_exclusive(x_242)) {
 x_250 = x_242;
} else {
 lean::inc(x_248);
 lean::dec(x_242);
 x_250 = lean::box(0);
}
if (lean::is_scalar(x_250)) {
 x_251 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_251 = x_250;
}
lean::cnstr_set(x_251, 0, x_248);
return x_251;
}
else
{
obj* x_252; obj* x_255; 
x_252 = lean::cnstr_get(x_242, 0);
lean::inc(x_252);
lean::dec(x_242);
x_255 = lean::cnstr_get(x_205, 2);
lean::inc(x_255);
if (lean::obj_tag(x_255) == 0)
{
obj* x_257; obj* x_259; obj* x_261; obj* x_262; 
x_257 = lean::cnstr_get(x_252, 0);
x_259 = lean::cnstr_get(x_252, 1);
if (lean::is_exclusive(x_252)) {
 x_261 = x_252;
} else {
 lean::inc(x_257);
 lean::inc(x_259);
 lean::dec(x_252);
 x_261 = lean::box(0);
}
if (lean::is_scalar(x_261)) {
 x_262 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_262 = x_261;
}
lean::cnstr_set(x_262, 0, x_257);
lean::cnstr_set(x_262, 1, x_259);
x_239 = x_262;
goto lbl_240;
}
else
{
obj* x_263; obj* x_265; obj* x_268; obj* x_271; obj* x_275; 
x_263 = lean::cnstr_get(x_252, 0);
lean::inc(x_263);
x_265 = lean::cnstr_get(x_252, 1);
lean::inc(x_265);
lean::dec(x_252);
x_268 = lean::cnstr_get(x_255, 0);
lean::inc(x_268);
lean::dec(x_255);
x_271 = lean::cnstr_get(x_268, 0);
lean::inc(x_271);
lean::dec(x_268);
lean::inc(x_1);
x_275 = l_lean_elaborator_to__pexpr___main(x_271, x_1, x_265);
if (lean::obj_tag(x_275) == 0)
{
obj* x_282; obj* x_284; obj* x_285; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
lean::dec(x_263);
lean::dec(x_234);
x_282 = lean::cnstr_get(x_275, 0);
if (lean::is_exclusive(x_275)) {
 x_284 = x_275;
} else {
 lean::inc(x_282);
 lean::dec(x_275);
 x_284 = lean::box(0);
}
if (lean::is_scalar(x_284)) {
 x_285 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_285 = x_284;
}
lean::cnstr_set(x_285, 0, x_282);
return x_285;
}
else
{
obj* x_286; obj* x_289; obj* x_291; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; 
x_286 = lean::cnstr_get(x_275, 0);
lean::inc(x_286);
lean::dec(x_275);
x_289 = lean::cnstr_get(x_286, 0);
x_291 = lean::cnstr_get(x_286, 1);
if (lean::is_exclusive(x_286)) {
 x_293 = x_286;
} else {
 lean::inc(x_289);
 lean::inc(x_291);
 lean::dec(x_286);
 x_293 = lean::box(0);
}
x_294 = lean::box(0);
x_295 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_295, 0, x_289);
lean::cnstr_set(x_295, 1, x_294);
x_296 = l_list_append___rarg(x_263, x_295);
if (lean::is_scalar(x_293)) {
 x_297 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_297 = x_293;
}
lean::cnstr_set(x_297, 0, x_296);
lean::cnstr_set(x_297, 1, x_291);
x_239 = x_297;
goto lbl_240;
}
}
}
lbl_240:
{
obj* x_298; obj* x_300; obj* x_302; obj* x_303; obj* x_304; obj* x_306; obj* x_307; obj* x_308; obj* x_309; uint8 x_310; obj* x_311; obj* x_312; obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; 
x_298 = lean::cnstr_get(x_239, 0);
x_300 = lean::cnstr_get(x_239, 1);
if (lean::is_exclusive(x_239)) {
 x_302 = x_239;
} else {
 lean::inc(x_298);
 lean::inc(x_300);
 lean::dec(x_239);
 x_302 = lean::box(0);
}
x_303 = lean::box(0);
x_304 = lean::mk_nat_obj(0u);
lean::inc(x_234);
x_306 = l_list_length__aux___main___rarg(x_234, x_304);
x_307 = l_lean_elaborator_to__pexpr___main___closed__25;
x_308 = l_lean_kvmap_set__nat(x_303, x_307, x_306);
x_309 = l_lean_elaborator_to__pexpr___main___closed__26;
x_310 = 0;
x_311 = l_lean_kvmap_set__bool(x_308, x_309, x_310);
x_312 = lean::cnstr_get(x_205, 1);
lean::inc(x_312);
lean::dec(x_205);
x_315 = l_lean_elaborator_to__pexpr___main___closed__27;
x_316 = l_option_map___rarg(x_315, x_312);
x_317 = l_lean_elaborator_to__pexpr___main___closed__28;
x_318 = l_option_map___rarg(x_317, x_316);
x_319 = lean::box(0);
x_320 = l_option_get__or__else___main___rarg(x_318, x_319);
lean::dec(x_318);
x_322 = l_lean_elaborator_to__pexpr___main___closed__29;
x_323 = l_lean_kvmap_set__name(x_311, x_322, x_320);
x_324 = l_list_append___rarg(x_234, x_298);
x_325 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(x_324);
x_326 = lean_expr_mk_mdata(x_323, x_325);
if (lean::is_scalar(x_302)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_302;
}
lean::cnstr_set(x_327, 0, x_326);
lean::cnstr_set(x_327, 1, x_300);
x_14 = x_327;
goto lbl_15;
}
}
}
else
{
obj* x_328; obj* x_330; 
x_328 = lean::cnstr_get(x_215, 0);
lean::inc(x_328);
x_330 = lean::cnstr_get(x_328, 0);
lean::inc(x_330);
lean::dec(x_328);
if (lean::obj_tag(x_330) == 0)
{
obj* x_333; obj* x_334; obj* x_337; obj* x_338; obj* x_341; obj* x_342; obj* x_344; 
if (lean::is_exclusive(x_215)) {
 lean::cnstr_release(x_215, 0);
 lean::cnstr_release(x_215, 1);
 x_333 = x_215;
} else {
 lean::dec(x_215);
 x_333 = lean::box(0);
}
x_334 = lean::cnstr_get(x_214, 0);
lean::inc(x_334);
lean::dec(x_214);
x_337 = l_lean_parser_term_struct__inst__item_has__view;
x_338 = lean::cnstr_get(x_337, 1);
lean::inc(x_338);
lean::dec(x_337);
x_341 = lean::apply_1(x_338, x_330);
x_342 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
x_344 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_341, x_342, x_1, x_2);
lean::dec(x_2);
lean::dec(x_341);
if (lean::obj_tag(x_344) == 0)
{
obj* x_354; obj* x_356; obj* x_357; 
lean::dec(x_334);
lean::dec(x_333);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_209);
lean::dec(x_205);
x_354 = lean::cnstr_get(x_344, 0);
if (lean::is_exclusive(x_344)) {
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
obj* x_358; obj* x_361; obj* x_363; obj* x_367; 
x_358 = lean::cnstr_get(x_344, 0);
lean::inc(x_358);
lean::dec(x_344);
x_361 = lean::cnstr_get(x_358, 0);
lean::inc(x_361);
x_363 = lean::cnstr_get(x_358, 1);
lean::inc(x_363);
lean::dec(x_358);
lean::inc(x_1);
x_367 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_209, x_1, x_363);
if (lean::obj_tag(x_367) == 0)
{
obj* x_375; obj* x_377; obj* x_378; 
lean::dec(x_334);
lean::dec(x_333);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_361);
lean::dec(x_205);
x_375 = lean::cnstr_get(x_367, 0);
if (lean::is_exclusive(x_367)) {
 x_377 = x_367;
} else {
 lean::inc(x_375);
 lean::dec(x_367);
 x_377 = lean::box(0);
}
if (lean::is_scalar(x_377)) {
 x_378 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_378 = x_377;
}
lean::cnstr_set(x_378, 0, x_375);
return x_378;
}
else
{
obj* x_379; obj* x_382; obj* x_384; obj* x_387; obj* x_390; 
x_379 = lean::cnstr_get(x_367, 0);
lean::inc(x_379);
lean::dec(x_367);
x_382 = lean::cnstr_get(x_379, 0);
lean::inc(x_382);
x_384 = lean::cnstr_get(x_379, 1);
lean::inc(x_384);
lean::dec(x_379);
lean::inc(x_1);
x_390 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_334, x_1, x_384);
if (lean::obj_tag(x_390) == 0)
{
obj* x_398; obj* x_400; obj* x_401; 
lean::dec(x_333);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_361);
lean::dec(x_382);
lean::dec(x_205);
x_398 = lean::cnstr_get(x_390, 0);
if (lean::is_exclusive(x_390)) {
 x_400 = x_390;
} else {
 lean::inc(x_398);
 lean::dec(x_390);
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
obj* x_402; obj* x_405; 
x_402 = lean::cnstr_get(x_390, 0);
lean::inc(x_402);
lean::dec(x_390);
x_405 = lean::cnstr_get(x_205, 2);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_408; obj* x_410; obj* x_412; obj* x_413; 
lean::dec(x_333);
x_408 = lean::cnstr_get(x_402, 0);
x_410 = lean::cnstr_get(x_402, 1);
if (lean::is_exclusive(x_402)) {
 x_412 = x_402;
} else {
 lean::inc(x_408);
 lean::inc(x_410);
 lean::dec(x_402);
 x_412 = lean::box(0);
}
if (lean::is_scalar(x_412)) {
 x_413 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_413 = x_412;
}
lean::cnstr_set(x_413, 0, x_408);
lean::cnstr_set(x_413, 1, x_410);
x_387 = x_413;
goto lbl_388;
}
else
{
obj* x_414; obj* x_416; obj* x_419; obj* x_422; obj* x_426; 
x_414 = lean::cnstr_get(x_402, 0);
lean::inc(x_414);
x_416 = lean::cnstr_get(x_402, 1);
lean::inc(x_416);
lean::dec(x_402);
x_419 = lean::cnstr_get(x_405, 0);
lean::inc(x_419);
lean::dec(x_405);
x_422 = lean::cnstr_get(x_419, 0);
lean::inc(x_422);
lean::dec(x_419);
lean::inc(x_1);
x_426 = l_lean_elaborator_to__pexpr___main(x_422, x_1, x_416);
if (lean::obj_tag(x_426) == 0)
{
obj* x_435; obj* x_437; obj* x_438; 
lean::dec(x_333);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_361);
lean::dec(x_382);
lean::dec(x_205);
lean::dec(x_414);
x_435 = lean::cnstr_get(x_426, 0);
if (lean::is_exclusive(x_426)) {
 x_437 = x_426;
} else {
 lean::inc(x_435);
 lean::dec(x_426);
 x_437 = lean::box(0);
}
if (lean::is_scalar(x_437)) {
 x_438 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_438 = x_437;
}
lean::cnstr_set(x_438, 0, x_435);
return x_438;
}
else
{
obj* x_439; obj* x_442; obj* x_444; obj* x_446; obj* x_447; obj* x_448; obj* x_449; obj* x_450; 
x_439 = lean::cnstr_get(x_426, 0);
lean::inc(x_439);
lean::dec(x_426);
x_442 = lean::cnstr_get(x_439, 0);
x_444 = lean::cnstr_get(x_439, 1);
if (lean::is_exclusive(x_439)) {
 x_446 = x_439;
} else {
 lean::inc(x_442);
 lean::inc(x_444);
 lean::dec(x_439);
 x_446 = lean::box(0);
}
x_447 = lean::box(0);
if (lean::is_scalar(x_333)) {
 x_448 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_448 = x_333;
}
lean::cnstr_set(x_448, 0, x_442);
lean::cnstr_set(x_448, 1, x_447);
x_449 = l_list_append___rarg(x_414, x_448);
if (lean::is_scalar(x_446)) {
 x_450 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_450 = x_446;
}
lean::cnstr_set(x_450, 0, x_449);
lean::cnstr_set(x_450, 1, x_444);
x_387 = x_450;
goto lbl_388;
}
}
}
lbl_388:
{
obj* x_451; obj* x_453; obj* x_455; obj* x_456; obj* x_457; obj* x_459; obj* x_460; obj* x_461; obj* x_462; uint8 x_463; obj* x_464; obj* x_465; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; 
x_451 = lean::cnstr_get(x_387, 0);
x_453 = lean::cnstr_get(x_387, 1);
if (lean::is_exclusive(x_387)) {
 x_455 = x_387;
} else {
 lean::inc(x_451);
 lean::inc(x_453);
 lean::dec(x_387);
 x_455 = lean::box(0);
}
x_456 = lean::box(0);
x_457 = lean::mk_nat_obj(0u);
lean::inc(x_382);
x_459 = l_list_length__aux___main___rarg(x_382, x_457);
x_460 = l_lean_elaborator_to__pexpr___main___closed__25;
x_461 = l_lean_kvmap_set__nat(x_456, x_460, x_459);
x_462 = l_lean_elaborator_to__pexpr___main___closed__26;
x_463 = lean::unbox(x_361);
x_464 = l_lean_kvmap_set__bool(x_461, x_462, x_463);
x_465 = lean::cnstr_get(x_205, 1);
lean::inc(x_465);
lean::dec(x_205);
x_468 = l_lean_elaborator_to__pexpr___main___closed__27;
x_469 = l_option_map___rarg(x_468, x_465);
x_470 = l_lean_elaborator_to__pexpr___main___closed__28;
x_471 = l_option_map___rarg(x_470, x_469);
x_472 = lean::box(0);
x_473 = l_option_get__or__else___main___rarg(x_471, x_472);
lean::dec(x_471);
x_475 = l_lean_elaborator_to__pexpr___main___closed__29;
x_476 = l_lean_kvmap_set__name(x_464, x_475, x_473);
x_477 = l_list_append___rarg(x_382, x_451);
x_478 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_477);
x_479 = lean_expr_mk_mdata(x_476, x_478);
if (lean::is_scalar(x_455)) {
 x_480 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_480 = x_455;
}
lean::cnstr_set(x_480, 0, x_479);
lean::cnstr_set(x_480, 1, x_453);
x_14 = x_480;
goto lbl_15;
}
}
}
}
else
{
obj* x_481; obj* x_483; 
x_481 = lean::cnstr_get(x_215, 1);
if (lean::is_exclusive(x_215)) {
 lean::cnstr_release(x_215, 0);
 lean::cnstr_set(x_215, 1, lean::box(0));
 x_483 = x_215;
} else {
 lean::inc(x_481);
 lean::dec(x_215);
 x_483 = lean::box(0);
}
if (lean::obj_tag(x_481) == 0)
{
obj* x_485; obj* x_489; 
lean::dec(x_330);
x_485 = lean::cnstr_get(x_214, 0);
lean::inc(x_485);
lean::dec(x_214);
lean::inc(x_1);
x_489 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_209, x_1, x_2);
if (lean::obj_tag(x_489) == 0)
{
obj* x_496; obj* x_498; obj* x_499; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
lean::dec(x_483);
lean::dec(x_485);
x_496 = lean::cnstr_get(x_489, 0);
if (lean::is_exclusive(x_489)) {
 x_498 = x_489;
} else {
 lean::inc(x_496);
 lean::dec(x_489);
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
obj* x_500; obj* x_503; obj* x_505; obj* x_508; obj* x_511; 
x_500 = lean::cnstr_get(x_489, 0);
lean::inc(x_500);
lean::dec(x_489);
x_503 = lean::cnstr_get(x_500, 0);
lean::inc(x_503);
x_505 = lean::cnstr_get(x_500, 1);
lean::inc(x_505);
lean::dec(x_500);
lean::inc(x_1);
x_511 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_485, x_1, x_505);
if (lean::obj_tag(x_511) == 0)
{
obj* x_518; obj* x_520; obj* x_521; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
lean::dec(x_483);
lean::dec(x_503);
x_518 = lean::cnstr_get(x_511, 0);
if (lean::is_exclusive(x_511)) {
 x_520 = x_511;
} else {
 lean::inc(x_518);
 lean::dec(x_511);
 x_520 = lean::box(0);
}
if (lean::is_scalar(x_520)) {
 x_521 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_521 = x_520;
}
lean::cnstr_set(x_521, 0, x_518);
return x_521;
}
else
{
obj* x_522; obj* x_525; 
x_522 = lean::cnstr_get(x_511, 0);
lean::inc(x_522);
lean::dec(x_511);
x_525 = lean::cnstr_get(x_205, 2);
lean::inc(x_525);
if (lean::obj_tag(x_525) == 0)
{
obj* x_528; obj* x_530; obj* x_532; obj* x_533; 
lean::dec(x_483);
x_528 = lean::cnstr_get(x_522, 0);
x_530 = lean::cnstr_get(x_522, 1);
if (lean::is_exclusive(x_522)) {
 x_532 = x_522;
} else {
 lean::inc(x_528);
 lean::inc(x_530);
 lean::dec(x_522);
 x_532 = lean::box(0);
}
if (lean::is_scalar(x_532)) {
 x_533 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_533 = x_532;
}
lean::cnstr_set(x_533, 0, x_528);
lean::cnstr_set(x_533, 1, x_530);
x_508 = x_533;
goto lbl_509;
}
else
{
obj* x_534; obj* x_536; obj* x_539; obj* x_542; obj* x_546; 
x_534 = lean::cnstr_get(x_522, 0);
lean::inc(x_534);
x_536 = lean::cnstr_get(x_522, 1);
lean::inc(x_536);
lean::dec(x_522);
x_539 = lean::cnstr_get(x_525, 0);
lean::inc(x_539);
lean::dec(x_525);
x_542 = lean::cnstr_get(x_539, 0);
lean::inc(x_542);
lean::dec(x_539);
lean::inc(x_1);
x_546 = l_lean_elaborator_to__pexpr___main(x_542, x_1, x_536);
if (lean::obj_tag(x_546) == 0)
{
obj* x_554; obj* x_556; obj* x_557; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
lean::dec(x_534);
lean::dec(x_483);
lean::dec(x_503);
x_554 = lean::cnstr_get(x_546, 0);
if (lean::is_exclusive(x_546)) {
 x_556 = x_546;
} else {
 lean::inc(x_554);
 lean::dec(x_546);
 x_556 = lean::box(0);
}
if (lean::is_scalar(x_556)) {
 x_557 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_557 = x_556;
}
lean::cnstr_set(x_557, 0, x_554);
return x_557;
}
else
{
obj* x_558; obj* x_561; obj* x_563; obj* x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; 
x_558 = lean::cnstr_get(x_546, 0);
lean::inc(x_558);
lean::dec(x_546);
x_561 = lean::cnstr_get(x_558, 0);
x_563 = lean::cnstr_get(x_558, 1);
if (lean::is_exclusive(x_558)) {
 x_565 = x_558;
} else {
 lean::inc(x_561);
 lean::inc(x_563);
 lean::dec(x_558);
 x_565 = lean::box(0);
}
x_566 = lean::box(0);
if (lean::is_scalar(x_483)) {
 x_567 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_567 = x_483;
}
lean::cnstr_set(x_567, 0, x_561);
lean::cnstr_set(x_567, 1, x_566);
x_568 = l_list_append___rarg(x_534, x_567);
if (lean::is_scalar(x_565)) {
 x_569 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_569 = x_565;
}
lean::cnstr_set(x_569, 0, x_568);
lean::cnstr_set(x_569, 1, x_563);
x_508 = x_569;
goto lbl_509;
}
}
}
lbl_509:
{
obj* x_570; obj* x_572; obj* x_574; obj* x_575; obj* x_576; obj* x_578; obj* x_579; obj* x_580; obj* x_581; uint8 x_582; obj* x_583; obj* x_584; obj* x_587; obj* x_588; obj* x_589; obj* x_590; obj* x_591; obj* x_592; obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; 
x_570 = lean::cnstr_get(x_508, 0);
x_572 = lean::cnstr_get(x_508, 1);
if (lean::is_exclusive(x_508)) {
 x_574 = x_508;
} else {
 lean::inc(x_570);
 lean::inc(x_572);
 lean::dec(x_508);
 x_574 = lean::box(0);
}
x_575 = lean::box(0);
x_576 = lean::mk_nat_obj(0u);
lean::inc(x_503);
x_578 = l_list_length__aux___main___rarg(x_503, x_576);
x_579 = l_lean_elaborator_to__pexpr___main___closed__25;
x_580 = l_lean_kvmap_set__nat(x_575, x_579, x_578);
x_581 = l_lean_elaborator_to__pexpr___main___closed__26;
x_582 = 1;
x_583 = l_lean_kvmap_set__bool(x_580, x_581, x_582);
x_584 = lean::cnstr_get(x_205, 1);
lean::inc(x_584);
lean::dec(x_205);
x_587 = l_lean_elaborator_to__pexpr___main___closed__27;
x_588 = l_option_map___rarg(x_587, x_584);
x_589 = l_lean_elaborator_to__pexpr___main___closed__28;
x_590 = l_option_map___rarg(x_589, x_588);
x_591 = lean::box(0);
x_592 = l_option_get__or__else___main___rarg(x_590, x_591);
lean::dec(x_590);
x_594 = l_lean_elaborator_to__pexpr___main___closed__29;
x_595 = l_lean_kvmap_set__name(x_583, x_594, x_592);
x_596 = l_list_append___rarg(x_503, x_570);
x_597 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_596);
x_598 = lean_expr_mk_mdata(x_595, x_597);
if (lean::is_scalar(x_574)) {
 x_599 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_599 = x_574;
}
lean::cnstr_set(x_599, 0, x_598);
lean::cnstr_set(x_599, 1, x_572);
x_14 = x_599;
goto lbl_15;
}
}
}
else
{
obj* x_601; obj* x_602; obj* x_605; obj* x_606; obj* x_609; obj* x_610; obj* x_612; 
lean::dec(x_483);
if (lean::is_exclusive(x_481)) {
 lean::cnstr_release(x_481, 0);
 lean::cnstr_release(x_481, 1);
 x_601 = x_481;
} else {
 lean::dec(x_481);
 x_601 = lean::box(0);
}
x_602 = lean::cnstr_get(x_214, 0);
lean::inc(x_602);
lean::dec(x_214);
x_605 = l_lean_parser_term_struct__inst__item_has__view;
x_606 = lean::cnstr_get(x_605, 1);
lean::inc(x_606);
lean::dec(x_605);
x_609 = lean::apply_1(x_606, x_330);
x_610 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
x_612 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_609, x_610, x_1, x_2);
lean::dec(x_2);
lean::dec(x_609);
if (lean::obj_tag(x_612) == 0)
{
obj* x_622; obj* x_624; obj* x_625; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_601);
lean::dec(x_602);
lean::dec(x_209);
lean::dec(x_205);
x_622 = lean::cnstr_get(x_612, 0);
if (lean::is_exclusive(x_612)) {
 x_624 = x_612;
} else {
 lean::inc(x_622);
 lean::dec(x_612);
 x_624 = lean::box(0);
}
if (lean::is_scalar(x_624)) {
 x_625 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_625 = x_624;
}
lean::cnstr_set(x_625, 0, x_622);
return x_625;
}
else
{
obj* x_626; obj* x_629; obj* x_631; obj* x_635; 
x_626 = lean::cnstr_get(x_612, 0);
lean::inc(x_626);
lean::dec(x_612);
x_629 = lean::cnstr_get(x_626, 0);
lean::inc(x_629);
x_631 = lean::cnstr_get(x_626, 1);
lean::inc(x_631);
lean::dec(x_626);
lean::inc(x_1);
x_635 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_209, x_1, x_631);
if (lean::obj_tag(x_635) == 0)
{
obj* x_643; obj* x_645; obj* x_646; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_601);
lean::dec(x_602);
lean::dec(x_629);
lean::dec(x_205);
x_643 = lean::cnstr_get(x_635, 0);
if (lean::is_exclusive(x_635)) {
 x_645 = x_635;
} else {
 lean::inc(x_643);
 lean::dec(x_635);
 x_645 = lean::box(0);
}
if (lean::is_scalar(x_645)) {
 x_646 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_646 = x_645;
}
lean::cnstr_set(x_646, 0, x_643);
return x_646;
}
else
{
obj* x_647; obj* x_650; obj* x_652; obj* x_655; obj* x_658; 
x_647 = lean::cnstr_get(x_635, 0);
lean::inc(x_647);
lean::dec(x_635);
x_650 = lean::cnstr_get(x_647, 0);
lean::inc(x_650);
x_652 = lean::cnstr_get(x_647, 1);
lean::inc(x_652);
lean::dec(x_647);
lean::inc(x_1);
x_658 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_602, x_1, x_652);
if (lean::obj_tag(x_658) == 0)
{
obj* x_666; obj* x_668; obj* x_669; 
lean::dec(x_650);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_601);
lean::dec(x_629);
lean::dec(x_205);
x_666 = lean::cnstr_get(x_658, 0);
if (lean::is_exclusive(x_658)) {
 x_668 = x_658;
} else {
 lean::inc(x_666);
 lean::dec(x_658);
 x_668 = lean::box(0);
}
if (lean::is_scalar(x_668)) {
 x_669 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_669 = x_668;
}
lean::cnstr_set(x_669, 0, x_666);
return x_669;
}
else
{
obj* x_670; obj* x_673; 
x_670 = lean::cnstr_get(x_658, 0);
lean::inc(x_670);
lean::dec(x_658);
x_673 = lean::cnstr_get(x_205, 2);
lean::inc(x_673);
if (lean::obj_tag(x_673) == 0)
{
obj* x_676; obj* x_678; obj* x_680; obj* x_681; 
lean::dec(x_601);
x_676 = lean::cnstr_get(x_670, 0);
x_678 = lean::cnstr_get(x_670, 1);
if (lean::is_exclusive(x_670)) {
 x_680 = x_670;
} else {
 lean::inc(x_676);
 lean::inc(x_678);
 lean::dec(x_670);
 x_680 = lean::box(0);
}
if (lean::is_scalar(x_680)) {
 x_681 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_681 = x_680;
}
lean::cnstr_set(x_681, 0, x_676);
lean::cnstr_set(x_681, 1, x_678);
x_655 = x_681;
goto lbl_656;
}
else
{
obj* x_682; obj* x_684; obj* x_687; obj* x_690; obj* x_694; 
x_682 = lean::cnstr_get(x_670, 0);
lean::inc(x_682);
x_684 = lean::cnstr_get(x_670, 1);
lean::inc(x_684);
lean::dec(x_670);
x_687 = lean::cnstr_get(x_673, 0);
lean::inc(x_687);
lean::dec(x_673);
x_690 = lean::cnstr_get(x_687, 0);
lean::inc(x_690);
lean::dec(x_687);
lean::inc(x_1);
x_694 = l_lean_elaborator_to__pexpr___main(x_690, x_1, x_684);
if (lean::obj_tag(x_694) == 0)
{
obj* x_703; obj* x_705; obj* x_706; 
lean::dec(x_650);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_682);
lean::dec(x_0);
lean::dec(x_601);
lean::dec(x_629);
lean::dec(x_205);
x_703 = lean::cnstr_get(x_694, 0);
if (lean::is_exclusive(x_694)) {
 x_705 = x_694;
} else {
 lean::inc(x_703);
 lean::dec(x_694);
 x_705 = lean::box(0);
}
if (lean::is_scalar(x_705)) {
 x_706 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_706 = x_705;
}
lean::cnstr_set(x_706, 0, x_703);
return x_706;
}
else
{
obj* x_707; obj* x_710; obj* x_712; obj* x_714; obj* x_715; obj* x_716; obj* x_717; obj* x_718; 
x_707 = lean::cnstr_get(x_694, 0);
lean::inc(x_707);
lean::dec(x_694);
x_710 = lean::cnstr_get(x_707, 0);
x_712 = lean::cnstr_get(x_707, 1);
if (lean::is_exclusive(x_707)) {
 x_714 = x_707;
} else {
 lean::inc(x_710);
 lean::inc(x_712);
 lean::dec(x_707);
 x_714 = lean::box(0);
}
x_715 = lean::box(0);
if (lean::is_scalar(x_601)) {
 x_716 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_716 = x_601;
}
lean::cnstr_set(x_716, 0, x_710);
lean::cnstr_set(x_716, 1, x_715);
x_717 = l_list_append___rarg(x_682, x_716);
if (lean::is_scalar(x_714)) {
 x_718 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_718 = x_714;
}
lean::cnstr_set(x_718, 0, x_717);
lean::cnstr_set(x_718, 1, x_712);
x_655 = x_718;
goto lbl_656;
}
}
}
lbl_656:
{
obj* x_719; obj* x_721; obj* x_723; obj* x_724; obj* x_725; obj* x_727; obj* x_728; obj* x_729; obj* x_730; uint8 x_731; obj* x_732; obj* x_733; obj* x_736; obj* x_737; obj* x_738; obj* x_739; obj* x_740; obj* x_741; obj* x_743; obj* x_744; obj* x_745; obj* x_746; obj* x_747; obj* x_748; 
x_719 = lean::cnstr_get(x_655, 0);
x_721 = lean::cnstr_get(x_655, 1);
if (lean::is_exclusive(x_655)) {
 x_723 = x_655;
} else {
 lean::inc(x_719);
 lean::inc(x_721);
 lean::dec(x_655);
 x_723 = lean::box(0);
}
x_724 = lean::box(0);
x_725 = lean::mk_nat_obj(0u);
lean::inc(x_650);
x_727 = l_list_length__aux___main___rarg(x_650, x_725);
x_728 = l_lean_elaborator_to__pexpr___main___closed__25;
x_729 = l_lean_kvmap_set__nat(x_724, x_728, x_727);
x_730 = l_lean_elaborator_to__pexpr___main___closed__26;
x_731 = lean::unbox(x_629);
x_732 = l_lean_kvmap_set__bool(x_729, x_730, x_731);
x_733 = lean::cnstr_get(x_205, 1);
lean::inc(x_733);
lean::dec(x_205);
x_736 = l_lean_elaborator_to__pexpr___main___closed__27;
x_737 = l_option_map___rarg(x_736, x_733);
x_738 = l_lean_elaborator_to__pexpr___main___closed__28;
x_739 = l_option_map___rarg(x_738, x_737);
x_740 = lean::box(0);
x_741 = l_option_get__or__else___main___rarg(x_739, x_740);
lean::dec(x_739);
x_743 = l_lean_elaborator_to__pexpr___main___closed__29;
x_744 = l_lean_kvmap_set__name(x_732, x_743, x_741);
x_745 = l_list_append___rarg(x_650, x_719);
x_746 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_745);
x_747 = lean_expr_mk_mdata(x_744, x_746);
if (lean::is_scalar(x_723)) {
 x_748 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_748 = x_723;
}
lean::cnstr_set(x_748, 0, x_747);
lean::cnstr_set(x_748, 1, x_721);
x_14 = x_748;
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
obj* x_751; 
lean::inc(x_1);
lean::inc(x_9);
x_751 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_9, x_1, x_2);
if (lean::obj_tag(x_751) == 0)
{
obj* x_756; obj* x_758; obj* x_759; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_756 = lean::cnstr_get(x_751, 0);
if (lean::is_exclusive(x_751)) {
 x_758 = x_751;
} else {
 lean::inc(x_756);
 lean::dec(x_751);
 x_758 = lean::box(0);
}
if (lean::is_scalar(x_758)) {
 x_759 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_759 = x_758;
}
lean::cnstr_set(x_759, 0, x_756);
return x_759;
}
else
{
obj* x_760; obj* x_763; obj* x_765; obj* x_767; obj* x_768; obj* x_769; 
x_760 = lean::cnstr_get(x_751, 0);
lean::inc(x_760);
lean::dec(x_751);
x_763 = lean::cnstr_get(x_760, 0);
x_765 = lean::cnstr_get(x_760, 1);
if (lean::is_exclusive(x_760)) {
 x_767 = x_760;
} else {
 lean::inc(x_763);
 lean::inc(x_765);
 lean::dec(x_760);
 x_767 = lean::box(0);
}
x_768 = l_list_reverse___rarg(x_763);
if (lean::is_scalar(x_767)) {
 x_769 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_769 = x_767;
}
lean::cnstr_set(x_769, 0, x_768);
lean::cnstr_set(x_769, 1, x_765);
x_16 = x_769;
goto lbl_17;
}
}
}
else
{
obj* x_772; obj* x_773; obj* x_777; obj* x_778; obj* x_779; obj* x_780; obj* x_782; obj* x_783; 
lean::dec(x_9);
lean::dec(x_7);
x_772 = l_lean_parser_string__lit_has__view;
x_773 = lean::cnstr_get(x_772, 0);
lean::inc(x_773);
lean::dec(x_772);
lean::inc(x_0);
x_777 = lean::apply_1(x_773, x_0);
x_778 = l_lean_parser_string__lit_view_value(x_777);
x_779 = l_lean_elaborator_to__pexpr___main___closed__31;
x_780 = l_option_get__or__else___main___rarg(x_778, x_779);
lean::dec(x_778);
x_782 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_782, 0, x_780);
x_783 = lean_expr_mk_lit(x_782);
if (x_21 == 0)
{
obj* x_784; 
x_784 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_784) == 0)
{
obj* x_787; obj* x_788; 
lean::dec(x_1);
x_787 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_787, 0, x_783);
lean::cnstr_set(x_787, 1, x_2);
x_788 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_788, 0, x_787);
return x_788;
}
else
{
obj* x_789; obj* x_792; obj* x_795; obj* x_798; obj* x_799; obj* x_800; obj* x_802; obj* x_803; obj* x_804; obj* x_807; obj* x_808; obj* x_809; obj* x_810; obj* x_811; 
x_789 = lean::cnstr_get(x_784, 0);
lean::inc(x_789);
lean::dec(x_784);
x_792 = lean::cnstr_get(x_1, 0);
lean::inc(x_792);
lean::dec(x_1);
x_795 = lean::cnstr_get(x_792, 2);
lean::inc(x_795);
lean::dec(x_792);
x_798 = l_lean_file__map_to__position(x_795, x_789);
x_799 = lean::box(0);
x_800 = lean::cnstr_get(x_798, 1);
lean::inc(x_800);
x_802 = l_lean_elaborator_to__pexpr___main___closed__3;
x_803 = l_lean_kvmap_set__nat(x_799, x_802, x_800);
x_804 = lean::cnstr_get(x_798, 0);
lean::inc(x_804);
lean::dec(x_798);
x_807 = l_lean_elaborator_to__pexpr___main___closed__4;
x_808 = l_lean_kvmap_set__nat(x_803, x_807, x_804);
x_809 = lean_expr_mk_mdata(x_808, x_783);
x_810 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_810, 0, x_809);
lean::cnstr_set(x_810, 1, x_2);
x_811 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_811, 0, x_810);
return x_811;
}
}
else
{
obj* x_814; obj* x_815; 
lean::dec(x_1);
lean::dec(x_0);
x_814 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_814, 0, x_783);
lean::cnstr_set(x_814, 1, x_2);
x_815 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_815, 0, x_814);
return x_815;
}
}
}
else
{
obj* x_818; obj* x_819; obj* x_823; obj* x_824; obj* x_825; obj* x_826; 
lean::dec(x_9);
lean::dec(x_7);
x_818 = l_lean_parser_number_has__view;
x_819 = lean::cnstr_get(x_818, 0);
lean::inc(x_819);
lean::dec(x_818);
lean::inc(x_0);
x_823 = lean::apply_1(x_819, x_0);
x_824 = l_lean_parser_number_view_to__nat___main(x_823);
x_825 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_825, 0, x_824);
x_826 = lean_expr_mk_lit(x_825);
if (x_21 == 0)
{
obj* x_827; 
x_827 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_827) == 0)
{
obj* x_830; obj* x_831; 
lean::dec(x_1);
x_830 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_830, 0, x_826);
lean::cnstr_set(x_830, 1, x_2);
x_831 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_831, 0, x_830);
return x_831;
}
else
{
obj* x_832; obj* x_835; obj* x_838; obj* x_841; obj* x_842; obj* x_843; obj* x_845; obj* x_846; obj* x_847; obj* x_850; obj* x_851; obj* x_852; obj* x_853; obj* x_854; 
x_832 = lean::cnstr_get(x_827, 0);
lean::inc(x_832);
lean::dec(x_827);
x_835 = lean::cnstr_get(x_1, 0);
lean::inc(x_835);
lean::dec(x_1);
x_838 = lean::cnstr_get(x_835, 2);
lean::inc(x_838);
lean::dec(x_835);
x_841 = l_lean_file__map_to__position(x_838, x_832);
x_842 = lean::box(0);
x_843 = lean::cnstr_get(x_841, 1);
lean::inc(x_843);
x_845 = l_lean_elaborator_to__pexpr___main___closed__3;
x_846 = l_lean_kvmap_set__nat(x_842, x_845, x_843);
x_847 = lean::cnstr_get(x_841, 0);
lean::inc(x_847);
lean::dec(x_841);
x_850 = l_lean_elaborator_to__pexpr___main___closed__4;
x_851 = l_lean_kvmap_set__nat(x_846, x_850, x_847);
x_852 = lean_expr_mk_mdata(x_851, x_826);
x_853 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_853, 0, x_852);
lean::cnstr_set(x_853, 1, x_2);
x_854 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_854, 0, x_853);
return x_854;
}
}
else
{
obj* x_857; obj* x_858; 
lean::dec(x_1);
lean::dec(x_0);
x_857 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_857, 0, x_826);
lean::cnstr_set(x_857, 1, x_2);
x_858 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_858, 0, x_857);
return x_858;
}
}
}
else
{
obj* x_860; obj* x_861; obj* x_865; obj* x_866; obj* x_870; 
lean::dec(x_9);
x_860 = l_lean_parser_term_borrowed_has__view;
x_861 = lean::cnstr_get(x_860, 0);
lean::inc(x_861);
lean::dec(x_860);
lean::inc(x_0);
x_865 = lean::apply_1(x_861, x_0);
x_866 = lean::cnstr_get(x_865, 1);
lean::inc(x_866);
lean::dec(x_865);
lean::inc(x_1);
x_870 = l_lean_elaborator_to__pexpr___main(x_866, x_1, x_2);
if (lean::obj_tag(x_870) == 0)
{
obj* x_874; obj* x_876; obj* x_877; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_874 = lean::cnstr_get(x_870, 0);
if (lean::is_exclusive(x_870)) {
 x_876 = x_870;
} else {
 lean::inc(x_874);
 lean::dec(x_870);
 x_876 = lean::box(0);
}
if (lean::is_scalar(x_876)) {
 x_877 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_877 = x_876;
}
lean::cnstr_set(x_877, 0, x_874);
return x_877;
}
else
{
obj* x_878; obj* x_881; obj* x_883; obj* x_885; obj* x_886; obj* x_887; obj* x_888; 
x_878 = lean::cnstr_get(x_870, 0);
lean::inc(x_878);
lean::dec(x_870);
x_881 = lean::cnstr_get(x_878, 0);
x_883 = lean::cnstr_get(x_878, 1);
if (lean::is_exclusive(x_878)) {
 x_885 = x_878;
} else {
 lean::inc(x_881);
 lean::inc(x_883);
 lean::dec(x_878);
 x_885 = lean::box(0);
}
x_886 = l_lean_elaborator_to__pexpr___main___closed__32;
x_887 = l_lean_elaborator_expr_mk__annotation(x_886, x_881);
if (lean::is_scalar(x_885)) {
 x_888 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_888 = x_885;
}
lean::cnstr_set(x_888, 0, x_887);
lean::cnstr_set(x_888, 1, x_883);
x_14 = x_888;
goto lbl_15;
}
}
}
else
{
obj* x_890; obj* x_891; obj* x_895; obj* x_896; obj* x_900; 
lean::dec(x_9);
x_890 = l_lean_parser_term_inaccessible_has__view;
x_891 = lean::cnstr_get(x_890, 0);
lean::inc(x_891);
lean::dec(x_890);
lean::inc(x_0);
x_895 = lean::apply_1(x_891, x_0);
x_896 = lean::cnstr_get(x_895, 1);
lean::inc(x_896);
lean::dec(x_895);
lean::inc(x_1);
x_900 = l_lean_elaborator_to__pexpr___main(x_896, x_1, x_2);
if (lean::obj_tag(x_900) == 0)
{
obj* x_904; obj* x_906; obj* x_907; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_904 = lean::cnstr_get(x_900, 0);
if (lean::is_exclusive(x_900)) {
 x_906 = x_900;
} else {
 lean::inc(x_904);
 lean::dec(x_900);
 x_906 = lean::box(0);
}
if (lean::is_scalar(x_906)) {
 x_907 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_907 = x_906;
}
lean::cnstr_set(x_907, 0, x_904);
return x_907;
}
else
{
obj* x_908; obj* x_911; obj* x_913; obj* x_915; obj* x_916; obj* x_917; obj* x_918; 
x_908 = lean::cnstr_get(x_900, 0);
lean::inc(x_908);
lean::dec(x_900);
x_911 = lean::cnstr_get(x_908, 0);
x_913 = lean::cnstr_get(x_908, 1);
if (lean::is_exclusive(x_908)) {
 x_915 = x_908;
} else {
 lean::inc(x_911);
 lean::inc(x_913);
 lean::dec(x_908);
 x_915 = lean::box(0);
}
x_916 = l_lean_elaborator_to__pexpr___main___closed__33;
x_917 = l_lean_elaborator_expr_mk__annotation(x_916, x_911);
if (lean::is_scalar(x_915)) {
 x_918 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_918 = x_915;
}
lean::cnstr_set(x_918, 0, x_917);
lean::cnstr_set(x_918, 1, x_913);
x_14 = x_918;
goto lbl_15;
}
}
}
else
{
obj* x_920; obj* x_921; obj* x_925; obj* x_926; obj* x_928; obj* x_929; obj* x_932; obj* x_935; 
lean::dec(x_9);
x_920 = l_lean_parser_term_explicit_has__view;
x_921 = lean::cnstr_get(x_920, 0);
lean::inc(x_921);
lean::dec(x_920);
lean::inc(x_0);
x_925 = lean::apply_1(x_921, x_0);
x_926 = lean::cnstr_get(x_925, 0);
lean::inc(x_926);
x_928 = l_lean_parser_ident__univs_has__view;
x_929 = lean::cnstr_get(x_928, 1);
lean::inc(x_929);
lean::dec(x_928);
x_932 = lean::cnstr_get(x_925, 1);
lean::inc(x_932);
lean::dec(x_925);
x_935 = lean::apply_1(x_929, x_932);
if (lean::obj_tag(x_926) == 0)
{
obj* x_938; 
lean::dec(x_926);
lean::inc(x_1);
x_938 = l_lean_elaborator_to__pexpr___main(x_935, x_1, x_2);
if (lean::obj_tag(x_938) == 0)
{
obj* x_942; obj* x_944; obj* x_945; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_942 = lean::cnstr_get(x_938, 0);
if (lean::is_exclusive(x_938)) {
 x_944 = x_938;
} else {
 lean::inc(x_942);
 lean::dec(x_938);
 x_944 = lean::box(0);
}
if (lean::is_scalar(x_944)) {
 x_945 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_945 = x_944;
}
lean::cnstr_set(x_945, 0, x_942);
return x_945;
}
else
{
obj* x_946; obj* x_949; obj* x_951; obj* x_953; obj* x_954; obj* x_955; obj* x_956; 
x_946 = lean::cnstr_get(x_938, 0);
lean::inc(x_946);
lean::dec(x_938);
x_949 = lean::cnstr_get(x_946, 0);
x_951 = lean::cnstr_get(x_946, 1);
if (lean::is_exclusive(x_946)) {
 x_953 = x_946;
} else {
 lean::inc(x_949);
 lean::inc(x_951);
 lean::dec(x_946);
 x_953 = lean::box(0);
}
x_954 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
x_955 = l_lean_elaborator_expr_mk__annotation(x_954, x_949);
if (lean::is_scalar(x_953)) {
 x_956 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_956 = x_953;
}
lean::cnstr_set(x_956, 0, x_955);
lean::cnstr_set(x_956, 1, x_951);
x_14 = x_956;
goto lbl_15;
}
}
else
{
obj* x_959; 
lean::dec(x_926);
lean::inc(x_1);
x_959 = l_lean_elaborator_to__pexpr___main(x_935, x_1, x_2);
if (lean::obj_tag(x_959) == 0)
{
obj* x_963; obj* x_965; obj* x_966; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_963 = lean::cnstr_get(x_959, 0);
if (lean::is_exclusive(x_959)) {
 x_965 = x_959;
} else {
 lean::inc(x_963);
 lean::dec(x_959);
 x_965 = lean::box(0);
}
if (lean::is_scalar(x_965)) {
 x_966 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_966 = x_965;
}
lean::cnstr_set(x_966, 0, x_963);
return x_966;
}
else
{
obj* x_967; obj* x_970; obj* x_972; obj* x_974; obj* x_975; obj* x_976; obj* x_977; 
x_967 = lean::cnstr_get(x_959, 0);
lean::inc(x_967);
lean::dec(x_959);
x_970 = lean::cnstr_get(x_967, 0);
x_972 = lean::cnstr_get(x_967, 1);
if (lean::is_exclusive(x_967)) {
 x_974 = x_967;
} else {
 lean::inc(x_970);
 lean::inc(x_972);
 lean::dec(x_967);
 x_974 = lean::box(0);
}
x_975 = l_lean_elaborator_to__pexpr___main___closed__34;
x_976 = l_lean_elaborator_expr_mk__annotation(x_975, x_970);
if (lean::is_scalar(x_974)) {
 x_977 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_977 = x_974;
}
lean::cnstr_set(x_977, 0, x_976);
lean::cnstr_set(x_977, 1, x_972);
x_14 = x_977;
goto lbl_15;
}
}
}
}
else
{
obj* x_979; obj* x_980; obj* x_984; obj* x_985; 
lean::dec(x_9);
x_979 = l_lean_parser_term_projection_has__view;
x_980 = lean::cnstr_get(x_979, 0);
lean::inc(x_980);
lean::dec(x_979);
lean::inc(x_0);
x_984 = lean::apply_1(x_980, x_0);
x_985 = lean::cnstr_get(x_984, 2);
lean::inc(x_985);
if (lean::obj_tag(x_985) == 0)
{
obj* x_987; obj* x_990; obj* x_994; 
x_987 = lean::cnstr_get(x_984, 0);
lean::inc(x_987);
lean::dec(x_984);
x_990 = lean::cnstr_get(x_985, 0);
lean::inc(x_990);
lean::dec(x_985);
lean::inc(x_1);
x_994 = l_lean_elaborator_to__pexpr___main(x_987, x_1, x_2);
if (lean::obj_tag(x_994) == 0)
{
obj* x_999; obj* x_1001; obj* x_1002; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_990);
x_999 = lean::cnstr_get(x_994, 0);
if (lean::is_exclusive(x_994)) {
 x_1001 = x_994;
} else {
 lean::inc(x_999);
 lean::dec(x_994);
 x_1001 = lean::box(0);
}
if (lean::is_scalar(x_1001)) {
 x_1002 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1002 = x_1001;
}
lean::cnstr_set(x_1002, 0, x_999);
return x_1002;
}
else
{
obj* x_1003; obj* x_1006; obj* x_1008; obj* x_1010; obj* x_1011; obj* x_1014; obj* x_1015; obj* x_1016; obj* x_1017; obj* x_1018; obj* x_1019; 
x_1003 = lean::cnstr_get(x_994, 0);
lean::inc(x_1003);
lean::dec(x_994);
x_1006 = lean::cnstr_get(x_1003, 0);
x_1008 = lean::cnstr_get(x_1003, 1);
if (lean::is_exclusive(x_1003)) {
 x_1010 = x_1003;
} else {
 lean::inc(x_1006);
 lean::inc(x_1008);
 lean::dec(x_1003);
 x_1010 = lean::box(0);
}
x_1011 = lean::cnstr_get(x_990, 2);
lean::inc(x_1011);
lean::dec(x_990);
x_1014 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1014, 0, x_1011);
x_1015 = lean::box(0);
x_1016 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1017 = l_lean_kvmap_insert__core___main(x_1015, x_1016, x_1014);
x_1018 = lean_expr_mk_mdata(x_1017, x_1006);
if (lean::is_scalar(x_1010)) {
 x_1019 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1019 = x_1010;
}
lean::cnstr_set(x_1019, 0, x_1018);
lean::cnstr_set(x_1019, 1, x_1008);
x_14 = x_1019;
goto lbl_15;
}
}
else
{
obj* x_1020; obj* x_1023; obj* x_1027; 
x_1020 = lean::cnstr_get(x_984, 0);
lean::inc(x_1020);
lean::dec(x_984);
x_1023 = lean::cnstr_get(x_985, 0);
lean::inc(x_1023);
lean::dec(x_985);
lean::inc(x_1);
x_1027 = l_lean_elaborator_to__pexpr___main(x_1020, x_1, x_2);
if (lean::obj_tag(x_1027) == 0)
{
obj* x_1032; obj* x_1034; obj* x_1035; 
lean::dec(x_1023);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1032 = lean::cnstr_get(x_1027, 0);
if (lean::is_exclusive(x_1027)) {
 x_1034 = x_1027;
} else {
 lean::inc(x_1032);
 lean::dec(x_1027);
 x_1034 = lean::box(0);
}
if (lean::is_scalar(x_1034)) {
 x_1035 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1035 = x_1034;
}
lean::cnstr_set(x_1035, 0, x_1032);
return x_1035;
}
else
{
obj* x_1036; obj* x_1039; obj* x_1041; obj* x_1043; obj* x_1044; obj* x_1045; obj* x_1046; obj* x_1047; obj* x_1048; obj* x_1049; obj* x_1050; 
x_1036 = lean::cnstr_get(x_1027, 0);
lean::inc(x_1036);
lean::dec(x_1027);
x_1039 = lean::cnstr_get(x_1036, 0);
x_1041 = lean::cnstr_get(x_1036, 1);
if (lean::is_exclusive(x_1036)) {
 x_1043 = x_1036;
} else {
 lean::inc(x_1039);
 lean::inc(x_1041);
 lean::dec(x_1036);
 x_1043 = lean::box(0);
}
x_1044 = l_lean_parser_number_view_to__nat___main(x_1023);
x_1045 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1045, 0, x_1044);
x_1046 = lean::box(0);
x_1047 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1048 = l_lean_kvmap_insert__core___main(x_1046, x_1047, x_1045);
x_1049 = lean_expr_mk_mdata(x_1048, x_1039);
if (lean::is_scalar(x_1043)) {
 x_1050 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1050 = x_1043;
}
lean::cnstr_set(x_1050, 0, x_1049);
lean::cnstr_set(x_1050, 1, x_1041);
x_14 = x_1050;
goto lbl_15;
}
}
}
}
else
{
obj* x_1052; obj* x_1053; obj* x_1057; obj* x_1058; 
lean::dec(x_9);
x_1052 = l_lean_parser_term_let_has__view;
x_1053 = lean::cnstr_get(x_1052, 0);
lean::inc(x_1053);
lean::dec(x_1052);
lean::inc(x_0);
x_1057 = lean::apply_1(x_1053, x_0);
x_1058 = lean::cnstr_get(x_1057, 1);
lean::inc(x_1058);
if (lean::obj_tag(x_1058) == 0)
{
obj* x_1060; obj* x_1063; 
x_1060 = lean::cnstr_get(x_1058, 0);
lean::inc(x_1060);
lean::dec(x_1058);
x_1063 = lean::cnstr_get(x_1060, 1);
lean::inc(x_1063);
if (lean::obj_tag(x_1063) == 0)
{
obj* x_1065; 
x_1065 = lean::cnstr_get(x_1060, 2);
lean::inc(x_1065);
if (lean::obj_tag(x_1065) == 0)
{
obj* x_1069; obj* x_1071; 
lean::dec(x_1060);
lean::dec(x_1057);
x_1069 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
x_1071 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1069, x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_1071) == 0)
{
obj* x_1076; obj* x_1078; obj* x_1079; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1076 = lean::cnstr_get(x_1071, 0);
if (lean::is_exclusive(x_1071)) {
 x_1078 = x_1071;
} else {
 lean::inc(x_1076);
 lean::dec(x_1071);
 x_1078 = lean::box(0);
}
if (lean::is_scalar(x_1078)) {
 x_1079 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1079 = x_1078;
}
lean::cnstr_set(x_1079, 0, x_1076);
return x_1079;
}
else
{
obj* x_1080; 
x_1080 = lean::cnstr_get(x_1071, 0);
lean::inc(x_1080);
lean::dec(x_1071);
x_14 = x_1080;
goto lbl_15;
}
}
else
{
obj* x_1083; obj* x_1086; obj* x_1089; obj* x_1093; 
x_1083 = lean::cnstr_get(x_1060, 0);
lean::inc(x_1083);
lean::dec(x_1060);
x_1086 = lean::cnstr_get(x_1065, 0);
lean::inc(x_1086);
lean::dec(x_1065);
x_1089 = lean::cnstr_get(x_1086, 1);
lean::inc(x_1089);
lean::dec(x_1086);
lean::inc(x_1);
x_1093 = l_lean_elaborator_to__pexpr___main(x_1089, x_1, x_2);
if (lean::obj_tag(x_1093) == 0)
{
obj* x_1099; obj* x_1101; obj* x_1102; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_1083);
lean::dec(x_0);
lean::dec(x_1057);
x_1099 = lean::cnstr_get(x_1093, 0);
if (lean::is_exclusive(x_1093)) {
 x_1101 = x_1093;
} else {
 lean::inc(x_1099);
 lean::dec(x_1093);
 x_1101 = lean::box(0);
}
if (lean::is_scalar(x_1101)) {
 x_1102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1102 = x_1101;
}
lean::cnstr_set(x_1102, 0, x_1099);
return x_1102;
}
else
{
obj* x_1103; obj* x_1106; obj* x_1108; obj* x_1111; obj* x_1114; 
x_1103 = lean::cnstr_get(x_1093, 0);
lean::inc(x_1103);
lean::dec(x_1093);
x_1106 = lean::cnstr_get(x_1103, 0);
lean::inc(x_1106);
x_1108 = lean::cnstr_get(x_1103, 1);
lean::inc(x_1108);
lean::dec(x_1103);
x_1111 = lean::cnstr_get(x_1057, 3);
lean::inc(x_1111);
lean::inc(x_1);
x_1114 = l_lean_elaborator_to__pexpr___main(x_1111, x_1, x_1108);
if (lean::obj_tag(x_1114) == 0)
{
obj* x_1121; obj* x_1123; obj* x_1124; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_1083);
lean::dec(x_0);
lean::dec(x_1106);
lean::dec(x_1057);
x_1121 = lean::cnstr_get(x_1114, 0);
if (lean::is_exclusive(x_1114)) {
 x_1123 = x_1114;
} else {
 lean::inc(x_1121);
 lean::dec(x_1114);
 x_1123 = lean::box(0);
}
if (lean::is_scalar(x_1123)) {
 x_1124 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1124 = x_1123;
}
lean::cnstr_set(x_1124, 0, x_1121);
return x_1124;
}
else
{
obj* x_1125; obj* x_1128; obj* x_1130; obj* x_1133; obj* x_1137; 
x_1125 = lean::cnstr_get(x_1114, 0);
lean::inc(x_1125);
lean::dec(x_1114);
x_1128 = lean::cnstr_get(x_1125, 0);
lean::inc(x_1128);
x_1130 = lean::cnstr_get(x_1125, 1);
lean::inc(x_1130);
lean::dec(x_1125);
x_1133 = lean::cnstr_get(x_1057, 5);
lean::inc(x_1133);
lean::dec(x_1057);
lean::inc(x_1);
x_1137 = l_lean_elaborator_to__pexpr___main(x_1133, x_1, x_1130);
if (lean::obj_tag(x_1137) == 0)
{
obj* x_1144; obj* x_1146; obj* x_1147; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_1083);
lean::dec(x_0);
lean::dec(x_1106);
lean::dec(x_1128);
x_1144 = lean::cnstr_get(x_1137, 0);
if (lean::is_exclusive(x_1137)) {
 x_1146 = x_1137;
} else {
 lean::inc(x_1144);
 lean::dec(x_1137);
 x_1146 = lean::box(0);
}
if (lean::is_scalar(x_1146)) {
 x_1147 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1147 = x_1146;
}
lean::cnstr_set(x_1147, 0, x_1144);
return x_1147;
}
else
{
obj* x_1148; obj* x_1151; obj* x_1153; obj* x_1155; obj* x_1156; obj* x_1157; obj* x_1158; 
x_1148 = lean::cnstr_get(x_1137, 0);
lean::inc(x_1148);
lean::dec(x_1137);
x_1151 = lean::cnstr_get(x_1148, 0);
x_1153 = lean::cnstr_get(x_1148, 1);
if (lean::is_exclusive(x_1148)) {
 x_1155 = x_1148;
} else {
 lean::inc(x_1151);
 lean::inc(x_1153);
 lean::dec(x_1148);
 x_1155 = lean::box(0);
}
x_1156 = l_lean_elaborator_mangle__ident(x_1083);
x_1157 = lean_expr_mk_let(x_1156, x_1106, x_1128, x_1151);
if (lean::is_scalar(x_1155)) {
 x_1158 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1158 = x_1155;
}
lean::cnstr_set(x_1158, 0, x_1157);
lean::cnstr_set(x_1158, 1, x_1153);
x_14 = x_1158;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1162; obj* x_1164; 
lean::dec(x_1060);
lean::dec(x_1063);
lean::dec(x_1057);
x_1162 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
x_1164 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1162, x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_1164) == 0)
{
obj* x_1169; obj* x_1171; obj* x_1172; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1169 = lean::cnstr_get(x_1164, 0);
if (lean::is_exclusive(x_1164)) {
 x_1171 = x_1164;
} else {
 lean::inc(x_1169);
 lean::dec(x_1164);
 x_1171 = lean::box(0);
}
if (lean::is_scalar(x_1171)) {
 x_1172 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1172 = x_1171;
}
lean::cnstr_set(x_1172, 0, x_1169);
return x_1172;
}
else
{
obj* x_1173; 
x_1173 = lean::cnstr_get(x_1164, 0);
lean::inc(x_1173);
lean::dec(x_1164);
x_14 = x_1173;
goto lbl_15;
}
}
}
else
{
obj* x_1178; obj* x_1180; 
lean::dec(x_1057);
lean::dec(x_1058);
x_1178 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1);
x_1180 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1178, x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_1180) == 0)
{
obj* x_1185; obj* x_1187; obj* x_1188; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1185 = lean::cnstr_get(x_1180, 0);
if (lean::is_exclusive(x_1180)) {
 x_1187 = x_1180;
} else {
 lean::inc(x_1185);
 lean::dec(x_1180);
 x_1187 = lean::box(0);
}
if (lean::is_scalar(x_1187)) {
 x_1188 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1188 = x_1187;
}
lean::cnstr_set(x_1188, 0, x_1185);
return x_1188;
}
else
{
obj* x_1189; 
x_1189 = lean::cnstr_get(x_1180, 0);
lean::inc(x_1189);
lean::dec(x_1180);
x_14 = x_1189;
goto lbl_15;
}
}
}
}
else
{
obj* x_1193; obj* x_1194; obj* x_1198; obj* x_1199; obj* x_1202; 
lean::dec(x_9);
x_1193 = l_lean_parser_term_show_has__view;
x_1194 = lean::cnstr_get(x_1193, 0);
lean::inc(x_1194);
lean::dec(x_1193);
lean::inc(x_0);
x_1198 = lean::apply_1(x_1194, x_0);
x_1199 = lean::cnstr_get(x_1198, 1);
lean::inc(x_1199);
lean::inc(x_1);
x_1202 = l_lean_elaborator_to__pexpr___main(x_1199, x_1, x_2);
if (lean::obj_tag(x_1202) == 0)
{
obj* x_1207; obj* x_1209; obj* x_1210; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1198);
x_1207 = lean::cnstr_get(x_1202, 0);
if (lean::is_exclusive(x_1202)) {
 x_1209 = x_1202;
} else {
 lean::inc(x_1207);
 lean::dec(x_1202);
 x_1209 = lean::box(0);
}
if (lean::is_scalar(x_1209)) {
 x_1210 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1210 = x_1209;
}
lean::cnstr_set(x_1210, 0, x_1207);
return x_1210;
}
else
{
obj* x_1211; obj* x_1214; obj* x_1216; obj* x_1219; obj* x_1222; obj* x_1226; 
x_1211 = lean::cnstr_get(x_1202, 0);
lean::inc(x_1211);
lean::dec(x_1202);
x_1214 = lean::cnstr_get(x_1211, 0);
lean::inc(x_1214);
x_1216 = lean::cnstr_get(x_1211, 1);
lean::inc(x_1216);
lean::dec(x_1211);
x_1219 = lean::cnstr_get(x_1198, 3);
lean::inc(x_1219);
lean::dec(x_1198);
x_1222 = lean::cnstr_get(x_1219, 1);
lean::inc(x_1222);
lean::dec(x_1219);
lean::inc(x_1);
x_1226 = l_lean_elaborator_to__pexpr___main(x_1222, x_1, x_1216);
if (lean::obj_tag(x_1226) == 0)
{
obj* x_1231; obj* x_1233; obj* x_1234; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1214);
x_1231 = lean::cnstr_get(x_1226, 0);
if (lean::is_exclusive(x_1226)) {
 x_1233 = x_1226;
} else {
 lean::inc(x_1231);
 lean::dec(x_1226);
 x_1233 = lean::box(0);
}
if (lean::is_scalar(x_1233)) {
 x_1234 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1234 = x_1233;
}
lean::cnstr_set(x_1234, 0, x_1231);
return x_1234;
}
else
{
obj* x_1235; obj* x_1238; obj* x_1240; obj* x_1242; obj* x_1243; uint8 x_1244; obj* x_1245; obj* x_1246; obj* x_1247; obj* x_1248; obj* x_1249; obj* x_1250; 
x_1235 = lean::cnstr_get(x_1226, 0);
lean::inc(x_1235);
lean::dec(x_1226);
x_1238 = lean::cnstr_get(x_1235, 0);
x_1240 = lean::cnstr_get(x_1235, 1);
if (lean::is_exclusive(x_1235)) {
 x_1242 = x_1235;
} else {
 lean::inc(x_1238);
 lean::inc(x_1240);
 lean::dec(x_1235);
 x_1242 = lean::box(0);
}
x_1243 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1244 = 0;
x_1245 = l_lean_elaborator_to__pexpr___main___closed__38;
x_1246 = lean_expr_mk_lambda(x_1243, x_1244, x_1214, x_1245);
x_1247 = lean_expr_mk_app(x_1246, x_1238);
x_1248 = l_lean_elaborator_to__pexpr___main___closed__39;
x_1249 = l_lean_elaborator_expr_mk__annotation(x_1248, x_1247);
if (lean::is_scalar(x_1242)) {
 x_1250 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1250 = x_1242;
}
lean::cnstr_set(x_1250, 0, x_1249);
lean::cnstr_set(x_1250, 1, x_1240);
x_14 = x_1250;
goto lbl_15;
}
}
}
}
else
{
obj* x_1252; obj* x_1253; obj* x_1257; obj* x_1258; obj* x_1260; obj* x_1263; 
lean::dec(x_9);
x_1252 = l_lean_parser_term_have_has__view;
x_1253 = lean::cnstr_get(x_1252, 0);
lean::inc(x_1253);
lean::dec(x_1252);
lean::inc(x_0);
x_1257 = lean::apply_1(x_1253, x_0);
x_1260 = lean::cnstr_get(x_1257, 2);
lean::inc(x_1260);
lean::inc(x_1);
x_1263 = l_lean_elaborator_to__pexpr___main(x_1260, x_1, x_2);
if (lean::obj_tag(x_1263) == 0)
{
obj* x_1268; obj* x_1270; obj* x_1271; 
lean::dec(x_1257);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1268 = lean::cnstr_get(x_1263, 0);
if (lean::is_exclusive(x_1263)) {
 x_1270 = x_1263;
} else {
 lean::inc(x_1268);
 lean::dec(x_1263);
 x_1270 = lean::box(0);
}
if (lean::is_scalar(x_1270)) {
 x_1271 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1271 = x_1270;
}
lean::cnstr_set(x_1271, 0, x_1268);
return x_1271;
}
else
{
obj* x_1272; obj* x_1275; obj* x_1277; obj* x_1280; obj* x_1283; 
x_1272 = lean::cnstr_get(x_1263, 0);
lean::inc(x_1272);
lean::dec(x_1263);
x_1275 = lean::cnstr_get(x_1272, 0);
lean::inc(x_1275);
x_1277 = lean::cnstr_get(x_1272, 1);
lean::inc(x_1277);
lean::dec(x_1272);
x_1280 = lean::cnstr_get(x_1257, 5);
lean::inc(x_1280);
lean::inc(x_1);
x_1283 = l_lean_elaborator_to__pexpr___main(x_1280, x_1, x_1277);
if (lean::obj_tag(x_1283) == 0)
{
obj* x_1289; obj* x_1291; obj* x_1292; 
lean::dec(x_1257);
lean::dec(x_1275);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1289 = lean::cnstr_get(x_1283, 0);
if (lean::is_exclusive(x_1283)) {
 x_1291 = x_1283;
} else {
 lean::inc(x_1289);
 lean::dec(x_1283);
 x_1291 = lean::box(0);
}
if (lean::is_scalar(x_1291)) {
 x_1292 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1292 = x_1291;
}
lean::cnstr_set(x_1292, 0, x_1289);
return x_1292;
}
else
{
obj* x_1293; obj* x_1296; obj* x_1298; obj* x_1300; obj* x_1301; obj* x_1303; obj* x_1304; obj* x_1305; obj* x_1306; obj* x_1307; obj* x_1308; uint8 x_1310; obj* x_1311; obj* x_1312; 
x_1293 = lean::cnstr_get(x_1283, 0);
lean::inc(x_1293);
lean::dec(x_1283);
x_1296 = lean::cnstr_get(x_1293, 0);
x_1298 = lean::cnstr_get(x_1293, 1);
if (lean::is_exclusive(x_1293)) {
 x_1300 = x_1293;
} else {
 lean::inc(x_1296);
 lean::inc(x_1298);
 lean::dec(x_1293);
 x_1300 = lean::box(0);
}
x_1301 = lean::cnstr_get(x_1257, 1);
lean::inc(x_1301);
x_1303 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1304 = l_option_map___rarg(x_1303, x_1301);
x_1305 = l_lean_elaborator_to__pexpr___main___closed__28;
x_1306 = l_option_map___rarg(x_1305, x_1304);
x_1307 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1308 = l_option_get__or__else___main___rarg(x_1306, x_1307);
lean::dec(x_1306);
x_1310 = 0;
x_1311 = lean_expr_mk_lambda(x_1308, x_1310, x_1275, x_1296);
if (lean::is_scalar(x_1300)) {
 x_1312 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1312 = x_1300;
}
lean::cnstr_set(x_1312, 0, x_1311);
lean::cnstr_set(x_1312, 1, x_1298);
x_1258 = x_1312;
goto lbl_1259;
}
}
lbl_1259:
{
obj* x_1313; 
x_1313 = lean::cnstr_get(x_1257, 3);
lean::inc(x_1313);
lean::dec(x_1257);
if (lean::obj_tag(x_1313) == 0)
{
obj* x_1316; obj* x_1318; obj* x_1321; obj* x_1324; obj* x_1328; 
x_1316 = lean::cnstr_get(x_1258, 0);
lean::inc(x_1316);
x_1318 = lean::cnstr_get(x_1258, 1);
lean::inc(x_1318);
lean::dec(x_1258);
x_1321 = lean::cnstr_get(x_1313, 0);
lean::inc(x_1321);
lean::dec(x_1313);
x_1324 = lean::cnstr_get(x_1321, 1);
lean::inc(x_1324);
lean::dec(x_1321);
lean::inc(x_1);
x_1328 = l_lean_elaborator_to__pexpr___main(x_1324, x_1, x_1318);
if (lean::obj_tag(x_1328) == 0)
{
obj* x_1333; obj* x_1335; obj* x_1336; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1316);
x_1333 = lean::cnstr_get(x_1328, 0);
if (lean::is_exclusive(x_1328)) {
 x_1335 = x_1328;
} else {
 lean::inc(x_1333);
 lean::dec(x_1328);
 x_1335 = lean::box(0);
}
if (lean::is_scalar(x_1335)) {
 x_1336 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1336 = x_1335;
}
lean::cnstr_set(x_1336, 0, x_1333);
return x_1336;
}
else
{
obj* x_1337; obj* x_1340; obj* x_1342; obj* x_1344; obj* x_1345; obj* x_1346; obj* x_1347; obj* x_1348; 
x_1337 = lean::cnstr_get(x_1328, 0);
lean::inc(x_1337);
lean::dec(x_1328);
x_1340 = lean::cnstr_get(x_1337, 0);
x_1342 = lean::cnstr_get(x_1337, 1);
if (lean::is_exclusive(x_1337)) {
 x_1344 = x_1337;
} else {
 lean::inc(x_1340);
 lean::inc(x_1342);
 lean::dec(x_1337);
 x_1344 = lean::box(0);
}
x_1345 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1346 = l_lean_elaborator_expr_mk__annotation(x_1345, x_1316);
x_1347 = lean_expr_mk_app(x_1346, x_1340);
if (lean::is_scalar(x_1344)) {
 x_1348 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1348 = x_1344;
}
lean::cnstr_set(x_1348, 0, x_1347);
lean::cnstr_set(x_1348, 1, x_1342);
x_14 = x_1348;
goto lbl_15;
}
}
else
{
obj* x_1349; obj* x_1351; obj* x_1354; obj* x_1357; obj* x_1360; obj* x_1364; 
x_1349 = lean::cnstr_get(x_1258, 0);
lean::inc(x_1349);
x_1351 = lean::cnstr_get(x_1258, 1);
lean::inc(x_1351);
lean::dec(x_1258);
x_1354 = lean::cnstr_get(x_1313, 0);
lean::inc(x_1354);
lean::dec(x_1313);
x_1357 = lean::cnstr_get(x_1354, 1);
lean::inc(x_1357);
lean::dec(x_1354);
x_1360 = lean::cnstr_get(x_1357, 1);
lean::inc(x_1360);
lean::dec(x_1357);
lean::inc(x_1);
x_1364 = l_lean_elaborator_to__pexpr___main(x_1360, x_1, x_1351);
if (lean::obj_tag(x_1364) == 0)
{
obj* x_1369; obj* x_1371; obj* x_1372; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1349);
x_1369 = lean::cnstr_get(x_1364, 0);
if (lean::is_exclusive(x_1364)) {
 x_1371 = x_1364;
} else {
 lean::inc(x_1369);
 lean::dec(x_1364);
 x_1371 = lean::box(0);
}
if (lean::is_scalar(x_1371)) {
 x_1372 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1372 = x_1371;
}
lean::cnstr_set(x_1372, 0, x_1369);
return x_1372;
}
else
{
obj* x_1373; obj* x_1376; obj* x_1378; obj* x_1380; obj* x_1381; obj* x_1382; obj* x_1383; obj* x_1384; 
x_1373 = lean::cnstr_get(x_1364, 0);
lean::inc(x_1373);
lean::dec(x_1364);
x_1376 = lean::cnstr_get(x_1373, 0);
x_1378 = lean::cnstr_get(x_1373, 1);
if (lean::is_exclusive(x_1373)) {
 x_1380 = x_1373;
} else {
 lean::inc(x_1376);
 lean::inc(x_1378);
 lean::dec(x_1373);
 x_1380 = lean::box(0);
}
x_1381 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1382 = l_lean_elaborator_expr_mk__annotation(x_1381, x_1349);
x_1383 = lean_expr_mk_app(x_1382, x_1376);
if (lean::is_scalar(x_1380)) {
 x_1384 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1384 = x_1380;
}
lean::cnstr_set(x_1384, 0, x_1383);
lean::cnstr_set(x_1384, 1, x_1378);
x_14 = x_1384;
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
obj* x_1387; 
x_1387 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1387) == 0)
{
obj* x_1390; obj* x_1391; obj* x_1392; 
lean::dec(x_1);
x_1390 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1391 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1391, 0, x_1390);
lean::cnstr_set(x_1391, 1, x_2);
x_1392 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1392, 0, x_1391);
return x_1392;
}
else
{
obj* x_1393; obj* x_1396; obj* x_1399; obj* x_1402; obj* x_1403; obj* x_1404; obj* x_1406; obj* x_1407; obj* x_1408; obj* x_1411; obj* x_1412; obj* x_1413; obj* x_1414; obj* x_1415; obj* x_1416; 
x_1393 = lean::cnstr_get(x_1387, 0);
lean::inc(x_1393);
lean::dec(x_1387);
x_1396 = lean::cnstr_get(x_1, 0);
lean::inc(x_1396);
lean::dec(x_1);
x_1399 = lean::cnstr_get(x_1396, 2);
lean::inc(x_1399);
lean::dec(x_1396);
x_1402 = l_lean_file__map_to__position(x_1399, x_1393);
x_1403 = lean::box(0);
x_1404 = lean::cnstr_get(x_1402, 1);
lean::inc(x_1404);
x_1406 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1407 = l_lean_kvmap_set__nat(x_1403, x_1406, x_1404);
x_1408 = lean::cnstr_get(x_1402, 0);
lean::inc(x_1408);
lean::dec(x_1402);
x_1411 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1412 = l_lean_kvmap_set__nat(x_1407, x_1411, x_1408);
x_1413 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1414 = lean_expr_mk_mdata(x_1412, x_1413);
x_1415 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1415, 0, x_1414);
lean::cnstr_set(x_1415, 1, x_2);
x_1416 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1416, 0, x_1415);
return x_1416;
}
}
else
{
obj* x_1419; obj* x_1420; obj* x_1421; 
lean::dec(x_1);
lean::dec(x_0);
x_1419 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1420 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1420, 0, x_1419);
lean::cnstr_set(x_1420, 1, x_2);
x_1421 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1421, 0, x_1420);
return x_1421;
}
}
}
else
{
obj* x_1423; obj* x_1424; obj* x_1428; obj* x_1429; obj* x_1432; obj* x_1433; obj* x_1434; obj* x_1436; 
lean::dec(x_9);
x_1423 = l_lean_parser_term_anonymous__constructor_has__view;
x_1424 = lean::cnstr_get(x_1423, 0);
lean::inc(x_1424);
lean::dec(x_1423);
lean::inc(x_0);
x_1428 = lean::apply_1(x_1424, x_0);
x_1429 = lean::cnstr_get(x_1428, 1);
lean::inc(x_1429);
lean::dec(x_1428);
x_1432 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_1429);
x_1433 = l_lean_expander_get__opt__type___main___closed__1;
x_1434 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_1433, x_1432);
lean::inc(x_1);
x_1436 = l_lean_elaborator_to__pexpr___main(x_1434, x_1, x_2);
if (lean::obj_tag(x_1436) == 0)
{
obj* x_1440; obj* x_1442; obj* x_1443; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1440 = lean::cnstr_get(x_1436, 0);
if (lean::is_exclusive(x_1436)) {
 x_1442 = x_1436;
} else {
 lean::inc(x_1440);
 lean::dec(x_1436);
 x_1442 = lean::box(0);
}
if (lean::is_scalar(x_1442)) {
 x_1443 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1443 = x_1442;
}
lean::cnstr_set(x_1443, 0, x_1440);
return x_1443;
}
else
{
obj* x_1444; obj* x_1447; obj* x_1449; obj* x_1451; obj* x_1452; obj* x_1453; obj* x_1454; 
x_1444 = lean::cnstr_get(x_1436, 0);
lean::inc(x_1444);
lean::dec(x_1436);
x_1447 = lean::cnstr_get(x_1444, 0);
x_1449 = lean::cnstr_get(x_1444, 1);
if (lean::is_exclusive(x_1444)) {
 x_1451 = x_1444;
} else {
 lean::inc(x_1447);
 lean::inc(x_1449);
 lean::dec(x_1444);
 x_1451 = lean::box(0);
}
x_1452 = l_lean_elaborator_to__pexpr___main___closed__43;
x_1453 = l_lean_elaborator_expr_mk__annotation(x_1452, x_1447);
if (lean::is_scalar(x_1451)) {
 x_1454 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1454 = x_1451;
}
lean::cnstr_set(x_1454, 0, x_1453);
lean::cnstr_set(x_1454, 1, x_1449);
x_14 = x_1454;
goto lbl_15;
}
}
}
else
{
obj* x_1456; obj* x_1457; obj* x_1461; obj* x_1462; obj* x_1463; obj* x_1466; obj* x_1468; 
lean::dec(x_9);
x_1456 = l_lean_parser_term_sort__app_has__view;
x_1457 = lean::cnstr_get(x_1456, 0);
lean::inc(x_1457);
lean::dec(x_1456);
lean::inc(x_0);
x_1461 = lean::apply_1(x_1457, x_0);
x_1462 = l_lean_parser_term_sort_has__view;
x_1463 = lean::cnstr_get(x_1462, 0);
lean::inc(x_1463);
lean::dec(x_1462);
x_1466 = lean::cnstr_get(x_1461, 0);
lean::inc(x_1466);
x_1468 = lean::apply_1(x_1463, x_1466);
if (lean::obj_tag(x_1468) == 0)
{
obj* x_1470; obj* x_1474; 
lean::dec(x_1468);
x_1470 = lean::cnstr_get(x_1461, 1);
lean::inc(x_1470);
lean::dec(x_1461);
lean::inc(x_1);
x_1474 = l_lean_elaborator_to__level___main(x_1470, x_1, x_2);
if (lean::obj_tag(x_1474) == 0)
{
obj* x_1478; obj* x_1480; obj* x_1481; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1478 = lean::cnstr_get(x_1474, 0);
if (lean::is_exclusive(x_1474)) {
 x_1480 = x_1474;
} else {
 lean::inc(x_1478);
 lean::dec(x_1474);
 x_1480 = lean::box(0);
}
if (lean::is_scalar(x_1480)) {
 x_1481 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1481 = x_1480;
}
lean::cnstr_set(x_1481, 0, x_1478);
return x_1481;
}
else
{
obj* x_1482; obj* x_1485; obj* x_1487; obj* x_1489; obj* x_1490; obj* x_1491; 
x_1482 = lean::cnstr_get(x_1474, 0);
lean::inc(x_1482);
lean::dec(x_1474);
x_1485 = lean::cnstr_get(x_1482, 0);
x_1487 = lean::cnstr_get(x_1482, 1);
if (lean::is_exclusive(x_1482)) {
 x_1489 = x_1482;
} else {
 lean::inc(x_1485);
 lean::inc(x_1487);
 lean::dec(x_1482);
 x_1489 = lean::box(0);
}
x_1490 = lean_expr_mk_sort(x_1485);
if (lean::is_scalar(x_1489)) {
 x_1491 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1491 = x_1489;
}
lean::cnstr_set(x_1491, 0, x_1490);
lean::cnstr_set(x_1491, 1, x_1487);
x_14 = x_1491;
goto lbl_15;
}
}
else
{
obj* x_1493; obj* x_1497; 
lean::dec(x_1468);
x_1493 = lean::cnstr_get(x_1461, 1);
lean::inc(x_1493);
lean::dec(x_1461);
lean::inc(x_1);
x_1497 = l_lean_elaborator_to__level___main(x_1493, x_1, x_2);
if (lean::obj_tag(x_1497) == 0)
{
obj* x_1501; obj* x_1503; obj* x_1504; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1501 = lean::cnstr_get(x_1497, 0);
if (lean::is_exclusive(x_1497)) {
 x_1503 = x_1497;
} else {
 lean::inc(x_1501);
 lean::dec(x_1497);
 x_1503 = lean::box(0);
}
if (lean::is_scalar(x_1503)) {
 x_1504 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1504 = x_1503;
}
lean::cnstr_set(x_1504, 0, x_1501);
return x_1504;
}
else
{
obj* x_1505; obj* x_1508; obj* x_1510; obj* x_1512; obj* x_1513; obj* x_1514; obj* x_1515; 
x_1505 = lean::cnstr_get(x_1497, 0);
lean::inc(x_1505);
lean::dec(x_1497);
x_1508 = lean::cnstr_get(x_1505, 0);
x_1510 = lean::cnstr_get(x_1505, 1);
if (lean::is_exclusive(x_1505)) {
 x_1512 = x_1505;
} else {
 lean::inc(x_1508);
 lean::inc(x_1510);
 lean::dec(x_1505);
 x_1512 = lean::box(0);
}
x_1513 = level_mk_succ(x_1508);
x_1514 = lean_expr_mk_sort(x_1513);
if (lean::is_scalar(x_1512)) {
 x_1515 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1515 = x_1512;
}
lean::cnstr_set(x_1515, 0, x_1514);
lean::cnstr_set(x_1515, 1, x_1510);
x_14 = x_1515;
goto lbl_15;
}
}
}
}
else
{
obj* x_1518; obj* x_1519; obj* x_1523; 
lean::dec(x_9);
lean::dec(x_7);
x_1518 = l_lean_parser_term_sort_has__view;
x_1519 = lean::cnstr_get(x_1518, 0);
lean::inc(x_1519);
lean::dec(x_1518);
lean::inc(x_0);
x_1523 = lean::apply_1(x_1519, x_0);
if (lean::obj_tag(x_1523) == 0)
{
lean::dec(x_1523);
if (x_21 == 0)
{
obj* x_1525; 
x_1525 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1525) == 0)
{
obj* x_1528; obj* x_1529; obj* x_1530; 
lean::dec(x_1);
x_1528 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1529 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1529, 0, x_1528);
lean::cnstr_set(x_1529, 1, x_2);
x_1530 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1530, 0, x_1529);
return x_1530;
}
else
{
obj* x_1531; obj* x_1534; obj* x_1537; obj* x_1540; obj* x_1541; obj* x_1542; obj* x_1544; obj* x_1545; obj* x_1546; obj* x_1549; obj* x_1550; obj* x_1551; obj* x_1552; obj* x_1553; obj* x_1554; 
x_1531 = lean::cnstr_get(x_1525, 0);
lean::inc(x_1531);
lean::dec(x_1525);
x_1534 = lean::cnstr_get(x_1, 0);
lean::inc(x_1534);
lean::dec(x_1);
x_1537 = lean::cnstr_get(x_1534, 2);
lean::inc(x_1537);
lean::dec(x_1534);
x_1540 = l_lean_file__map_to__position(x_1537, x_1531);
x_1541 = lean::box(0);
x_1542 = lean::cnstr_get(x_1540, 1);
lean::inc(x_1542);
x_1544 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1545 = l_lean_kvmap_set__nat(x_1541, x_1544, x_1542);
x_1546 = lean::cnstr_get(x_1540, 0);
lean::inc(x_1546);
lean::dec(x_1540);
x_1549 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1550 = l_lean_kvmap_set__nat(x_1545, x_1549, x_1546);
x_1551 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1552 = lean_expr_mk_mdata(x_1550, x_1551);
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
obj* x_1557; obj* x_1558; obj* x_1559; 
lean::dec(x_1);
lean::dec(x_0);
x_1557 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1558 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1558, 0, x_1557);
lean::cnstr_set(x_1558, 1, x_2);
x_1559 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1559, 0, x_1558);
return x_1559;
}
}
else
{
lean::dec(x_1523);
if (x_21 == 0)
{
obj* x_1561; 
x_1561 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1561) == 0)
{
obj* x_1564; obj* x_1565; obj* x_1566; 
lean::dec(x_1);
x_1564 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1565 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1565, 0, x_1564);
lean::cnstr_set(x_1565, 1, x_2);
x_1566 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1566, 0, x_1565);
return x_1566;
}
else
{
obj* x_1567; obj* x_1570; obj* x_1573; obj* x_1576; obj* x_1577; obj* x_1578; obj* x_1580; obj* x_1581; obj* x_1582; obj* x_1585; obj* x_1586; obj* x_1587; obj* x_1588; obj* x_1589; obj* x_1590; 
x_1567 = lean::cnstr_get(x_1561, 0);
lean::inc(x_1567);
lean::dec(x_1561);
x_1570 = lean::cnstr_get(x_1, 0);
lean::inc(x_1570);
lean::dec(x_1);
x_1573 = lean::cnstr_get(x_1570, 2);
lean::inc(x_1573);
lean::dec(x_1570);
x_1576 = l_lean_file__map_to__position(x_1573, x_1567);
x_1577 = lean::box(0);
x_1578 = lean::cnstr_get(x_1576, 1);
lean::inc(x_1578);
x_1580 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1581 = l_lean_kvmap_set__nat(x_1577, x_1580, x_1578);
x_1582 = lean::cnstr_get(x_1576, 0);
lean::inc(x_1582);
lean::dec(x_1576);
x_1585 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1586 = l_lean_kvmap_set__nat(x_1581, x_1585, x_1582);
x_1587 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1588 = lean_expr_mk_mdata(x_1586, x_1587);
x_1589 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1589, 0, x_1588);
lean::cnstr_set(x_1589, 1, x_2);
x_1590 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1590, 0, x_1589);
return x_1590;
}
}
else
{
obj* x_1593; obj* x_1594; obj* x_1595; 
lean::dec(x_1);
lean::dec(x_0);
x_1593 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1594 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1594, 0, x_1593);
lean::cnstr_set(x_1594, 1, x_2);
x_1595 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1595, 0, x_1594);
return x_1595;
}
}
}
}
else
{
obj* x_1597; obj* x_1598; obj* x_1602; obj* x_1603; 
lean::dec(x_9);
x_1597 = l_lean_parser_term_pi_has__view;
x_1598 = lean::cnstr_get(x_1597, 0);
lean::inc(x_1598);
lean::dec(x_1597);
lean::inc(x_0);
x_1602 = lean::apply_1(x_1598, x_0);
x_1603 = lean::cnstr_get(x_1602, 1);
lean::inc(x_1603);
if (lean::obj_tag(x_1603) == 0)
{
obj* x_1607; obj* x_1609; 
lean::dec(x_1602);
lean::dec(x_1603);
x_1607 = l_lean_elaborator_to__pexpr___main___closed__45;
lean::inc(x_1);
x_1609 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1607, x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_1609) == 0)
{
obj* x_1614; obj* x_1616; obj* x_1617; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1614 = lean::cnstr_get(x_1609, 0);
if (lean::is_exclusive(x_1609)) {
 x_1616 = x_1609;
} else {
 lean::inc(x_1614);
 lean::dec(x_1609);
 x_1616 = lean::box(0);
}
if (lean::is_scalar(x_1616)) {
 x_1617 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1617 = x_1616;
}
lean::cnstr_set(x_1617, 0, x_1614);
return x_1617;
}
else
{
obj* x_1618; 
x_1618 = lean::cnstr_get(x_1609, 0);
lean::inc(x_1618);
lean::dec(x_1609);
x_14 = x_1618;
goto lbl_15;
}
}
else
{
obj* x_1621; obj* x_1624; obj* x_1625; obj* x_1627; obj* x_1630; obj* x_1632; obj* x_1636; 
x_1621 = lean::cnstr_get(x_1603, 0);
lean::inc(x_1621);
lean::dec(x_1603);
x_1624 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1621);
x_1625 = lean::cnstr_get(x_1624, 1);
lean::inc(x_1625);
x_1627 = lean::cnstr_get(x_1624, 0);
lean::inc(x_1627);
lean::dec(x_1624);
x_1630 = lean::cnstr_get(x_1625, 0);
lean::inc(x_1630);
x_1632 = lean::cnstr_get(x_1625, 1);
lean::inc(x_1632);
lean::dec(x_1625);
lean::inc(x_1);
x_1636 = l_lean_elaborator_to__pexpr___main(x_1632, x_1, x_2);
if (lean::obj_tag(x_1636) == 0)
{
obj* x_1643; obj* x_1645; obj* x_1646; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1627);
lean::dec(x_1602);
lean::dec(x_1630);
x_1643 = lean::cnstr_get(x_1636, 0);
if (lean::is_exclusive(x_1636)) {
 x_1645 = x_1636;
} else {
 lean::inc(x_1643);
 lean::dec(x_1636);
 x_1645 = lean::box(0);
}
if (lean::is_scalar(x_1645)) {
 x_1646 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1646 = x_1645;
}
lean::cnstr_set(x_1646, 0, x_1643);
return x_1646;
}
else
{
obj* x_1647; obj* x_1650; obj* x_1652; obj* x_1655; obj* x_1659; 
x_1647 = lean::cnstr_get(x_1636, 0);
lean::inc(x_1647);
lean::dec(x_1636);
x_1650 = lean::cnstr_get(x_1647, 0);
lean::inc(x_1650);
x_1652 = lean::cnstr_get(x_1647, 1);
lean::inc(x_1652);
lean::dec(x_1647);
x_1655 = lean::cnstr_get(x_1602, 3);
lean::inc(x_1655);
lean::dec(x_1602);
lean::inc(x_1);
x_1659 = l_lean_elaborator_to__pexpr___main(x_1655, x_1, x_1652);
if (lean::obj_tag(x_1659) == 0)
{
obj* x_1666; obj* x_1668; obj* x_1669; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1627);
lean::dec(x_1630);
lean::dec(x_1650);
x_1666 = lean::cnstr_get(x_1659, 0);
if (lean::is_exclusive(x_1659)) {
 x_1668 = x_1659;
} else {
 lean::inc(x_1666);
 lean::dec(x_1659);
 x_1668 = lean::box(0);
}
if (lean::is_scalar(x_1668)) {
 x_1669 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1669 = x_1668;
}
lean::cnstr_set(x_1669, 0, x_1666);
return x_1669;
}
else
{
obj* x_1670; obj* x_1673; obj* x_1675; obj* x_1677; obj* x_1678; uint8 x_1679; obj* x_1680; obj* x_1681; 
x_1670 = lean::cnstr_get(x_1659, 0);
lean::inc(x_1670);
lean::dec(x_1659);
x_1673 = lean::cnstr_get(x_1670, 0);
x_1675 = lean::cnstr_get(x_1670, 1);
if (lean::is_exclusive(x_1670)) {
 x_1677 = x_1670;
} else {
 lean::inc(x_1673);
 lean::inc(x_1675);
 lean::dec(x_1670);
 x_1677 = lean::box(0);
}
x_1678 = l_lean_elaborator_mangle__ident(x_1630);
x_1679 = lean::unbox(x_1627);
x_1680 = lean_expr_mk_pi(x_1678, x_1679, x_1650, x_1673);
if (lean::is_scalar(x_1677)) {
 x_1681 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1681 = x_1677;
}
lean::cnstr_set(x_1681, 0, x_1680);
lean::cnstr_set(x_1681, 1, x_1675);
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
obj* x_1693; obj* x_1695; 
lean::dec(x_1689);
lean::dec(x_1688);
x_1693 = l_lean_elaborator_to__pexpr___main___closed__46;
lean::inc(x_1);
x_1695 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1693, x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_1695) == 0)
{
obj* x_1700; obj* x_1702; obj* x_1703; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1700 = lean::cnstr_get(x_1695, 0);
if (lean::is_exclusive(x_1695)) {
 x_1702 = x_1695;
} else {
 lean::inc(x_1700);
 lean::dec(x_1695);
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
x_1704 = lean::cnstr_get(x_1695, 0);
lean::inc(x_1704);
lean::dec(x_1695);
x_14 = x_1704;
goto lbl_15;
}
}
else
{
obj* x_1707; obj* x_1710; obj* x_1711; obj* x_1713; obj* x_1716; obj* x_1718; obj* x_1722; 
x_1707 = lean::cnstr_get(x_1689, 0);
lean::inc(x_1707);
lean::dec(x_1689);
x_1710 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1707);
x_1711 = lean::cnstr_get(x_1710, 1);
lean::inc(x_1711);
x_1713 = lean::cnstr_get(x_1710, 0);
lean::inc(x_1713);
lean::dec(x_1710);
x_1716 = lean::cnstr_get(x_1711, 0);
lean::inc(x_1716);
x_1718 = lean::cnstr_get(x_1711, 1);
lean::inc(x_1718);
lean::dec(x_1711);
lean::inc(x_1);
x_1722 = l_lean_elaborator_to__pexpr___main(x_1718, x_1, x_2);
if (lean::obj_tag(x_1722) == 0)
{
obj* x_1729; obj* x_1731; obj* x_1732; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1716);
lean::dec(x_1713);
lean::dec(x_1688);
x_1729 = lean::cnstr_get(x_1722, 0);
if (lean::is_exclusive(x_1722)) {
 x_1731 = x_1722;
} else {
 lean::inc(x_1729);
 lean::dec(x_1722);
 x_1731 = lean::box(0);
}
if (lean::is_scalar(x_1731)) {
 x_1732 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1732 = x_1731;
}
lean::cnstr_set(x_1732, 0, x_1729);
return x_1732;
}
else
{
obj* x_1733; obj* x_1736; obj* x_1738; obj* x_1741; obj* x_1745; 
x_1733 = lean::cnstr_get(x_1722, 0);
lean::inc(x_1733);
lean::dec(x_1722);
x_1736 = lean::cnstr_get(x_1733, 0);
lean::inc(x_1736);
x_1738 = lean::cnstr_get(x_1733, 1);
lean::inc(x_1738);
lean::dec(x_1733);
x_1741 = lean::cnstr_get(x_1688, 3);
lean::inc(x_1741);
lean::dec(x_1688);
lean::inc(x_1);
x_1745 = l_lean_elaborator_to__pexpr___main(x_1741, x_1, x_1738);
if (lean::obj_tag(x_1745) == 0)
{
obj* x_1752; obj* x_1754; obj* x_1755; 
lean::dec(x_1736);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1716);
lean::dec(x_1713);
x_1752 = lean::cnstr_get(x_1745, 0);
if (lean::is_exclusive(x_1745)) {
 x_1754 = x_1745;
} else {
 lean::inc(x_1752);
 lean::dec(x_1745);
 x_1754 = lean::box(0);
}
if (lean::is_scalar(x_1754)) {
 x_1755 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1755 = x_1754;
}
lean::cnstr_set(x_1755, 0, x_1752);
return x_1755;
}
else
{
obj* x_1756; obj* x_1759; obj* x_1761; obj* x_1763; obj* x_1764; uint8 x_1765; obj* x_1766; obj* x_1767; 
x_1756 = lean::cnstr_get(x_1745, 0);
lean::inc(x_1756);
lean::dec(x_1745);
x_1759 = lean::cnstr_get(x_1756, 0);
x_1761 = lean::cnstr_get(x_1756, 1);
if (lean::is_exclusive(x_1756)) {
 x_1763 = x_1756;
} else {
 lean::inc(x_1759);
 lean::inc(x_1761);
 lean::dec(x_1756);
 x_1763 = lean::box(0);
}
x_1764 = l_lean_elaborator_mangle__ident(x_1716);
x_1765 = lean::unbox(x_1713);
x_1766 = lean_expr_mk_lambda(x_1764, x_1765, x_1736, x_1759);
if (lean::is_scalar(x_1763)) {
 x_1767 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1767 = x_1763;
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
lean::dec(x_1774);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1783 = lean::cnstr_get(x_1778, 0);
if (lean::is_exclusive(x_1778)) {
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
obj* x_1787; obj* x_1790; obj* x_1792; obj* x_1795; obj* x_1799; 
x_1787 = lean::cnstr_get(x_1778, 0);
lean::inc(x_1787);
lean::dec(x_1778);
x_1790 = lean::cnstr_get(x_1787, 0);
lean::inc(x_1790);
x_1792 = lean::cnstr_get(x_1787, 1);
lean::inc(x_1792);
lean::dec(x_1787);
x_1795 = lean::cnstr_get(x_1774, 1);
lean::inc(x_1795);
lean::dec(x_1774);
lean::inc(x_1);
x_1799 = l_lean_elaborator_to__pexpr___main(x_1795, x_1, x_1792);
if (lean::obj_tag(x_1799) == 0)
{
obj* x_1804; obj* x_1806; obj* x_1807; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1790);
x_1804 = lean::cnstr_get(x_1799, 0);
if (lean::is_exclusive(x_1799)) {
 x_1806 = x_1799;
} else {
 lean::inc(x_1804);
 lean::dec(x_1799);
 x_1806 = lean::box(0);
}
if (lean::is_scalar(x_1806)) {
 x_1807 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1807 = x_1806;
}
lean::cnstr_set(x_1807, 0, x_1804);
return x_1807;
}
else
{
obj* x_1808; obj* x_1811; obj* x_1813; obj* x_1815; obj* x_1816; obj* x_1817; 
x_1808 = lean::cnstr_get(x_1799, 0);
lean::inc(x_1808);
lean::dec(x_1799);
x_1811 = lean::cnstr_get(x_1808, 0);
x_1813 = lean::cnstr_get(x_1808, 1);
if (lean::is_exclusive(x_1808)) {
 x_1815 = x_1808;
} else {
 lean::inc(x_1811);
 lean::inc(x_1813);
 lean::dec(x_1808);
 x_1815 = lean::box(0);
}
x_1816 = lean_expr_mk_app(x_1790, x_1811);
if (lean::is_scalar(x_1815)) {
 x_1817 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1817 = x_1815;
}
lean::cnstr_set(x_1817, 0, x_1816);
lean::cnstr_set(x_1817, 1, x_1813);
x_14 = x_1817;
goto lbl_15;
}
}
}
}
else
{
obj* x_1819; obj* x_1820; obj* x_1824; obj* x_1825; 
lean::dec(x_9);
x_1819 = l_lean_parser_ident__univs_has__view;
x_1820 = lean::cnstr_get(x_1819, 0);
lean::inc(x_1820);
lean::dec(x_1819);
lean::inc(x_0);
x_1824 = lean::apply_1(x_1820, x_0);
x_1825 = lean::cnstr_get(x_1824, 1);
lean::inc(x_1825);
if (lean::obj_tag(x_1825) == 0)
{
obj* x_1827; obj* x_1831; obj* x_1832; obj* x_1833; obj* x_1834; obj* x_1837; obj* x_1838; obj* x_1839; obj* x_1840; obj* x_1841; obj* x_1842; uint8 x_1843; 
x_1827 = lean::cnstr_get(x_1824, 0);
lean::inc(x_1827);
lean::dec(x_1824);
lean::inc(x_1827);
x_1831 = l_lean_elaborator_mangle__ident(x_1827);
x_1832 = lean::box(0);
x_1833 = lean_expr_mk_const(x_1831, x_1832);
x_1834 = lean::cnstr_get(x_1827, 3);
lean::inc(x_1834);
lean::dec(x_1827);
x_1837 = lean::mk_nat_obj(0u);
x_1838 = l_list_enum__from___main___rarg(x_1837, x_1834);
x_1839 = l_lean_elaborator_to__pexpr___main___closed__47;
x_1840 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(x_1839, x_1838);
x_1841 = lean_expr_mk_mdata(x_1840, x_1833);
x_1842 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1843 = lean_name_dec_eq(x_7, x_1842);
lean::dec(x_7);
if (x_1843 == 0)
{
obj* x_1845; 
x_1845 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1845) == 0)
{
obj* x_1848; obj* x_1849; 
lean::dec(x_1);
x_1848 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1848, 0, x_1841);
lean::cnstr_set(x_1848, 1, x_2);
x_1849 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1849, 0, x_1848);
return x_1849;
}
else
{
obj* x_1850; obj* x_1853; obj* x_1856; obj* x_1859; obj* x_1860; obj* x_1862; obj* x_1863; obj* x_1864; obj* x_1867; obj* x_1868; obj* x_1869; obj* x_1870; obj* x_1871; 
x_1850 = lean::cnstr_get(x_1845, 0);
lean::inc(x_1850);
lean::dec(x_1845);
x_1853 = lean::cnstr_get(x_1, 0);
lean::inc(x_1853);
lean::dec(x_1);
x_1856 = lean::cnstr_get(x_1853, 2);
lean::inc(x_1856);
lean::dec(x_1853);
x_1859 = l_lean_file__map_to__position(x_1856, x_1850);
x_1860 = lean::cnstr_get(x_1859, 1);
lean::inc(x_1860);
x_1862 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1863 = l_lean_kvmap_set__nat(x_1832, x_1862, x_1860);
x_1864 = lean::cnstr_get(x_1859, 0);
lean::inc(x_1864);
lean::dec(x_1859);
x_1867 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1868 = l_lean_kvmap_set__nat(x_1863, x_1867, x_1864);
x_1869 = lean_expr_mk_mdata(x_1868, x_1841);
x_1870 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1870, 0, x_1869);
lean::cnstr_set(x_1870, 1, x_2);
x_1871 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1871, 0, x_1870);
return x_1871;
}
}
else
{
obj* x_1874; obj* x_1875; 
lean::dec(x_1);
lean::dec(x_0);
x_1874 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1874, 0, x_1841);
lean::cnstr_set(x_1874, 1, x_2);
x_1875 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1875, 0, x_1874);
return x_1875;
}
}
else
{
obj* x_1876; obj* x_1879; obj* x_1882; obj* x_1886; 
x_1876 = lean::cnstr_get(x_1824, 0);
lean::inc(x_1876);
lean::dec(x_1824);
x_1879 = lean::cnstr_get(x_1825, 0);
lean::inc(x_1879);
lean::dec(x_1825);
x_1882 = lean::cnstr_get(x_1879, 1);
lean::inc(x_1882);
lean::dec(x_1879);
lean::inc(x_1);
x_1886 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_1882, x_1, x_2);
if (lean::obj_tag(x_1886) == 0)
{
obj* x_1891; obj* x_1893; obj* x_1894; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1876);
x_1891 = lean::cnstr_get(x_1886, 0);
if (lean::is_exclusive(x_1886)) {
 x_1893 = x_1886;
} else {
 lean::inc(x_1891);
 lean::dec(x_1886);
 x_1893 = lean::box(0);
}
if (lean::is_scalar(x_1893)) {
 x_1894 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1894 = x_1893;
}
lean::cnstr_set(x_1894, 0, x_1891);
return x_1894;
}
else
{
obj* x_1895; obj* x_1898; obj* x_1900; obj* x_1902; obj* x_1904; obj* x_1905; obj* x_1906; obj* x_1909; obj* x_1910; obj* x_1911; obj* x_1912; obj* x_1913; obj* x_1914; 
x_1895 = lean::cnstr_get(x_1886, 0);
lean::inc(x_1895);
lean::dec(x_1886);
x_1898 = lean::cnstr_get(x_1895, 0);
x_1900 = lean::cnstr_get(x_1895, 1);
if (lean::is_exclusive(x_1895)) {
 x_1902 = x_1895;
} else {
 lean::inc(x_1898);
 lean::inc(x_1900);
 lean::dec(x_1895);
 x_1902 = lean::box(0);
}
lean::inc(x_1876);
x_1904 = l_lean_elaborator_mangle__ident(x_1876);
x_1905 = lean_expr_mk_const(x_1904, x_1898);
x_1906 = lean::cnstr_get(x_1876, 3);
lean::inc(x_1906);
lean::dec(x_1876);
x_1909 = lean::mk_nat_obj(0u);
x_1910 = l_list_enum__from___main___rarg(x_1909, x_1906);
x_1911 = l_lean_elaborator_to__pexpr___main___closed__47;
x_1912 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(x_1911, x_1910);
x_1913 = lean_expr_mk_mdata(x_1912, x_1905);
if (lean::is_scalar(x_1902)) {
 x_1914 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1914 = x_1902;
}
lean::cnstr_set(x_1914, 0, x_1913);
lean::cnstr_set(x_1914, 1, x_1900);
x_14 = x_1914;
goto lbl_15;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_1918; obj* x_1920; obj* x_1921; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_1918 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_1920 = x_12;
} else {
 lean::inc(x_1918);
 lean::dec(x_12);
 x_1920 = lean::box(0);
}
if (lean::is_scalar(x_1920)) {
 x_1921 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1921 = x_1920;
}
lean::cnstr_set(x_1921, 0, x_1918);
return x_1921;
}
else
{
obj* x_1922; obj* x_1924; obj* x_1925; obj* x_1927; obj* x_1929; obj* x_1930; uint8 x_1931; 
x_1922 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 x_1924 = x_12;
} else {
 lean::inc(x_1922);
 lean::dec(x_12);
 x_1924 = lean::box(0);
}
x_1925 = lean::cnstr_get(x_1922, 0);
x_1927 = lean::cnstr_get(x_1922, 1);
if (lean::is_exclusive(x_1922)) {
 lean::cnstr_set(x_1922, 0, lean::box(0));
 lean::cnstr_set(x_1922, 1, lean::box(0));
 x_1929 = x_1922;
} else {
 lean::inc(x_1925);
 lean::inc(x_1927);
 lean::dec(x_1922);
 x_1929 = lean::box(0);
}
x_1930 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1931 = lean_name_dec_eq(x_7, x_1930);
lean::dec(x_7);
if (x_1931 == 0)
{
obj* x_1933; 
x_1933 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1933) == 0)
{
obj* x_1936; obj* x_1937; 
lean::dec(x_1);
if (lean::is_scalar(x_1929)) {
 x_1936 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1936 = x_1929;
}
lean::cnstr_set(x_1936, 0, x_1925);
lean::cnstr_set(x_1936, 1, x_1927);
if (lean::is_scalar(x_1924)) {
 x_1937 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1937 = x_1924;
}
lean::cnstr_set(x_1937, 0, x_1936);
return x_1937;
}
else
{
obj* x_1938; obj* x_1941; obj* x_1944; obj* x_1947; obj* x_1948; obj* x_1949; obj* x_1951; obj* x_1952; obj* x_1953; obj* x_1956; obj* x_1957; obj* x_1958; obj* x_1959; obj* x_1960; 
x_1938 = lean::cnstr_get(x_1933, 0);
lean::inc(x_1938);
lean::dec(x_1933);
x_1941 = lean::cnstr_get(x_1, 0);
lean::inc(x_1941);
lean::dec(x_1);
x_1944 = lean::cnstr_get(x_1941, 2);
lean::inc(x_1944);
lean::dec(x_1941);
x_1947 = l_lean_file__map_to__position(x_1944, x_1938);
x_1948 = lean::box(0);
x_1949 = lean::cnstr_get(x_1947, 1);
lean::inc(x_1949);
x_1951 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1952 = l_lean_kvmap_set__nat(x_1948, x_1951, x_1949);
x_1953 = lean::cnstr_get(x_1947, 0);
lean::inc(x_1953);
lean::dec(x_1947);
x_1956 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1957 = l_lean_kvmap_set__nat(x_1952, x_1956, x_1953);
x_1958 = lean_expr_mk_mdata(x_1957, x_1925);
if (lean::is_scalar(x_1929)) {
 x_1959 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1959 = x_1929;
}
lean::cnstr_set(x_1959, 0, x_1958);
lean::cnstr_set(x_1959, 1, x_1927);
if (lean::is_scalar(x_1924)) {
 x_1960 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1960 = x_1924;
}
lean::cnstr_set(x_1960, 0, x_1959);
return x_1960;
}
}
else
{
obj* x_1963; obj* x_1964; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_1929)) {
 x_1963 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1963 = x_1929;
}
lean::cnstr_set(x_1963, 0, x_1925);
lean::cnstr_set(x_1963, 1, x_1927);
if (lean::is_scalar(x_1924)) {
 x_1964 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1964 = x_1924;
}
lean::cnstr_set(x_1964, 0, x_1963);
return x_1964;
}
}
}
lbl_15:
{
obj* x_1965; obj* x_1967; obj* x_1969; obj* x_1970; uint8 x_1971; 
x_1965 = lean::cnstr_get(x_14, 0);
x_1967 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_set(x_14, 1, lean::box(0));
 x_1969 = x_14;
} else {
 lean::inc(x_1965);
 lean::inc(x_1967);
 lean::dec(x_14);
 x_1969 = lean::box(0);
}
x_1970 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1971 = lean_name_dec_eq(x_7, x_1970);
lean::dec(x_7);
if (x_1971 == 0)
{
obj* x_1973; 
x_1973 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1973) == 0)
{
obj* x_1976; obj* x_1977; 
lean::dec(x_1);
if (lean::is_scalar(x_1969)) {
 x_1976 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1976 = x_1969;
}
lean::cnstr_set(x_1976, 0, x_1965);
lean::cnstr_set(x_1976, 1, x_1967);
x_1977 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1977, 0, x_1976);
return x_1977;
}
else
{
obj* x_1978; obj* x_1981; obj* x_1984; obj* x_1987; obj* x_1988; obj* x_1989; obj* x_1991; obj* x_1992; obj* x_1993; obj* x_1996; obj* x_1997; obj* x_1998; obj* x_1999; obj* x_2000; 
x_1978 = lean::cnstr_get(x_1973, 0);
lean::inc(x_1978);
lean::dec(x_1973);
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
x_1998 = lean_expr_mk_mdata(x_1997, x_1965);
if (lean::is_scalar(x_1969)) {
 x_1999 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1999 = x_1969;
}
lean::cnstr_set(x_1999, 0, x_1998);
lean::cnstr_set(x_1999, 1, x_1967);
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
if (lean::is_scalar(x_1969)) {
 x_2003 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2003 = x_1969;
}
lean::cnstr_set(x_2003, 0, x_1965);
lean::cnstr_set(x_2003, 1, x_1967);
x_2004 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2004, 0, x_2003);
return x_2004;
}
}
lbl_17:
{
obj* x_2005; 
x_2005 = lean::cnstr_get(x_16, 0);
lean::inc(x_2005);
if (lean::obj_tag(x_2005) == 0)
{
obj* x_2008; obj* x_2011; obj* x_2013; 
lean::dec(x_9);
x_2008 = lean::cnstr_get(x_16, 1);
lean::inc(x_2008);
lean::dec(x_16);
x_2011 = l_lean_elaborator_to__pexpr___main___closed__5;
lean::inc(x_1);
x_2013 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2011, x_1, x_2008);
lean::dec(x_2008);
if (lean::obj_tag(x_2013) == 0)
{
obj* x_2018; obj* x_2020; obj* x_2021; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
x_2018 = lean::cnstr_get(x_2013, 0);
if (lean::is_exclusive(x_2013)) {
 x_2020 = x_2013;
} else {
 lean::inc(x_2018);
 lean::dec(x_2013);
 x_2020 = lean::box(0);
}
if (lean::is_scalar(x_2020)) {
 x_2021 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2021 = x_2020;
}
lean::cnstr_set(x_2021, 0, x_2018);
return x_2021;
}
else
{
obj* x_2022; 
x_2022 = lean::cnstr_get(x_2013, 0);
lean::inc(x_2022);
lean::dec(x_2013);
x_14 = x_2022;
goto lbl_15;
}
}
else
{
obj* x_2025; obj* x_2027; obj* x_2028; obj* x_2030; obj* x_2033; obj* x_2034; obj* x_2035; obj* x_2036; obj* x_2037; obj* x_2038; obj* x_2039; obj* x_2041; obj* x_2042; 
x_2025 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_2027 = x_16;
} else {
 lean::inc(x_2025);
 lean::dec(x_16);
 x_2027 = lean::box(0);
}
x_2028 = lean::cnstr_get(x_2005, 0);
lean::inc(x_2028);
x_2030 = lean::cnstr_get(x_2005, 1);
lean::inc(x_2030);
lean::dec(x_2005);
x_2033 = lean::box(0);
x_2034 = lean::mk_nat_obj(0u);
x_2035 = l_list_length__aux___main___rarg(x_9, x_2034);
x_2036 = l_lean_elaborator_to__pexpr___main___closed__6;
x_2037 = l_lean_kvmap_set__nat(x_2033, x_2036, x_2035);
x_2038 = l_list_reverse___rarg(x_2030);
x_2039 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_2028, x_2038);
lean::dec(x_2028);
x_2041 = lean_expr_mk_mdata(x_2037, x_2039);
if (lean::is_scalar(x_2027)) {
 x_2042 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2042 = x_2027;
}
lean::cnstr_set(x_2042, 0, x_2041);
lean::cnstr_set(x_2042, 1, x_2025);
x_14 = x_2042;
goto lbl_15;
}
}
}
default:
{
obj* x_2043; 
x_2043 = lean::box(0);
x_3 = x_2043;
goto lbl_4;
}
}
lbl_4:
{
obj* x_2046; obj* x_2047; obj* x_2048; obj* x_2049; obj* x_2050; obj* x_2052; 
lean::dec(x_3);
lean::inc(x_0);
x_2046 = l_lean_parser_syntax_to__format___main(x_0);
x_2047 = lean::mk_nat_obj(80u);
x_2048 = l_lean_format_pretty(x_2046, x_2047);
x_2049 = l_lean_elaborator_to__pexpr___main___closed__1;
x_2050 = lean::string_append(x_2049, x_2048);
lean::dec(x_2048);
x_2052 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2050, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
return x_2052;
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_elaborator_to__pexpr___main___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_to__pexpr___main___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_to__pexpr___main___lambda__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_to__pexpr___main___lambda__2(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_get__namespace___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_elaborator_get__namespace___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_get__namespace(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
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
x_16 = l_lean_name_quick__lt(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
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
x_16 = l_lean_name_quick__lt(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
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
x_16 = l_lean_name_quick__lt(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
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
obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
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
lean::dec(x_18);
x_22 = l_lean_file__map_to__position(x_16, x_20);
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
x_25 = l_lean_elaborator_to__pexpr___main___closed__3;
x_26 = l_lean_kvmap_set__nat(x_11, x_25, x_23);
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_lean_elaborator_to__pexpr___main___closed__4;
x_31 = l_lean_kvmap_set__nat(x_26, x_30, x_27);
x_32 = lean_expr_mk_mdata(x_31, x_13);
x_9 = x_32;
goto lbl_10;
}
default:
{
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
obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_3);
lean::dec(x_55);
x_82 = lean::cnstr_get(x_77, 1);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 x_84 = x_77;
} else {
 lean::inc(x_82);
 lean::dec(x_77);
 x_84 = lean::box(0);
}
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
if (lean::is_scalar(x_84)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_84;
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
obj* x_114; obj* x_116; obj* x_117; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_133; obj* x_134; obj* x_136; obj* x_137; obj* x_138; obj* x_140; obj* x_141; obj* x_143; obj* x_146; obj* x_148; obj* x_149; obj* x_151; obj* x_153; obj* x_156; obj* x_158; obj* x_160; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
lean::dec(x_45);
x_114 = lean::cnstr_get(x_77, 1);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 x_116 = x_77;
} else {
 lean::inc(x_114);
 lean::dec(x_77);
 x_116 = lean::box(0);
}
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
if (lean::is_scalar(x_116)) {
 x_166 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_166 = x_116;
}
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
obj* l_lean_elaborator_old__elab__command___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_old__elab__command(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
x_41 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_43 = x_36;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_36);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_43 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_45 = x_35;
} else {
 lean::inc(x_43);
 lean::dec(x_35);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
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
if (lean::is_scalar(x_50)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_50;
}
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
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
obj* x_3; obj* x_4; obj* x_6; obj* x_8; uint8 x_10; obj* x_12; uint8 x_14; obj* x_16; obj* x_19; 
x_3 = lean::box(0);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
x_10 = l_option_is__some___main___rarg(x_8);
lean::dec(x_8);
x_12 = lean::cnstr_get(x_0, 4);
lean::inc(x_12);
x_14 = l_option_is__some___main___rarg(x_12);
lean::dec(x_12);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
lean::dec(x_0);
if (lean::obj_tag(x_4) == 0)
{
if (lean::obj_tag(x_6) == 0)
{
x_19 = x_3;
goto lbl_20;
}
else
{
obj* x_21; 
x_21 = lean::cnstr_get(x_6, 0);
lean::inc(x_21);
lean::dec(x_6);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; 
lean::dec(x_21);
x_25 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
x_19 = x_25;
goto lbl_20;
}
else
{
obj* x_27; 
lean::dec(x_21);
x_27 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
x_19 = x_27;
goto lbl_20;
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
x_19 = x_3;
goto lbl_20;
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
x_19 = x_38;
goto lbl_20;
}
else
{
obj* x_40; 
lean::dec(x_34);
x_40 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
x_19 = x_40;
goto lbl_20;
}
}
}
else
{
obj* x_41; obj* x_44; obj* x_47; obj* x_48; 
x_41 = lean::cnstr_get(x_31, 0);
lean::inc(x_41);
lean::dec(x_31);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
x_47 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
x_48 = l_lean_kvmap_set__string(x_3, x_47, x_44);
if (lean::obj_tag(x_6) == 0)
{
x_19 = x_48;
goto lbl_20;
}
else
{
obj* x_49; 
x_49 = lean::cnstr_get(x_6, 0);
lean::inc(x_49);
lean::dec(x_6);
if (lean::obj_tag(x_49) == 0)
{
obj* x_53; uint8 x_54; obj* x_55; 
lean::dec(x_49);
x_53 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
x_54 = 1;
x_55 = l_lean_kvmap_set__bool(x_48, x_53, x_54);
x_19 = x_55;
goto lbl_20;
}
else
{
obj* x_57; uint8 x_58; obj* x_59; 
lean::dec(x_49);
x_57 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
x_58 = 1;
x_59 = l_lean_kvmap_set__bool(x_48, x_57, x_58);
x_19 = x_59;
goto lbl_20;
}
}
}
}
lbl_20:
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_60 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
x_61 = l_lean_kvmap_set__bool(x_19, x_60, x_10);
x_62 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
x_63 = l_lean_kvmap_set__bool(x_61, x_62, x_14);
if (lean::obj_tag(x_16) == 0)
{
obj* x_64; 
x_64 = l_lean_elaborator_attrs__to__pexpr(x_3, x_1, x_2);
if (lean::obj_tag(x_64) == 0)
{
obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_63);
x_66 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_68 = x_64;
} else {
 lean::inc(x_66);
 lean::dec(x_64);
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
obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_70 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_72 = x_64;
} else {
 lean::inc(x_70);
 lean::dec(x_64);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_70, 0);
x_75 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 x_77 = x_70;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
x_78 = lean_expr_mk_mdata(x_63, x_73);
if (lean::is_scalar(x_77)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_77;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_75);
if (lean::is_scalar(x_72)) {
 x_80 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_80 = x_72;
}
lean::cnstr_set(x_80, 0, x_79);
return x_80;
}
}
else
{
obj* x_81; obj* x_84; obj* x_87; 
x_81 = lean::cnstr_get(x_16, 0);
lean::inc(x_81);
lean::dec(x_16);
x_84 = lean::cnstr_get(x_81, 1);
lean::inc(x_84);
lean::dec(x_81);
x_87 = l_lean_elaborator_attrs__to__pexpr(x_84, x_1, x_2);
if (lean::obj_tag(x_87) == 0)
{
obj* x_89; obj* x_91; obj* x_92; 
lean::dec(x_63);
x_89 = lean::cnstr_get(x_87, 0);
if (lean::is_exclusive(x_87)) {
 x_91 = x_87;
} else {
 lean::inc(x_89);
 lean::dec(x_87);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_89);
return x_92;
}
else
{
obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_93 = lean::cnstr_get(x_87, 0);
if (lean::is_exclusive(x_87)) {
 x_95 = x_87;
} else {
 lean::inc(x_93);
 lean::dec(x_87);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_93, 0);
x_98 = lean::cnstr_get(x_93, 1);
if (lean::is_exclusive(x_93)) {
 x_100 = x_93;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::dec(x_93);
 x_100 = lean::box(0);
}
x_101 = lean_expr_mk_mdata(x_63, x_96);
if (lean::is_scalar(x_100)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_100;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_98);
if (lean::is_scalar(x_95)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_95;
}
lean::cnstr_set(x_103, 0, x_102);
return x_103;
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
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 2);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg___lambda__2), 2, 1);
lean::closure_set(x_6, 0, x_1);
x_7 = lean::apply_1(x_3, x_6);
return x_7;
}
}
obj* l_lean_elaborator_locally___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg___lambda__3___boxed), 3, 2);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg___lambda__1___boxed), 1, 0);
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_elaborator_locally___rarg___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_locally___rarg___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_locally___rarg___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_locally___rarg___lambda__3(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_locally___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_locally(x_0);
lean::dec(x_0);
return x_1;
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
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_13, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_13, 1);
lean::inc(x_20);
lean::dec(x_13);
lean::inc(x_1);
x_24 = l_lean_elaborator_to__pexpr___main(x_20, x_1, x_2);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_15);
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
lean::dec(x_15);
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
obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; uint8 x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_51 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_53 = x_42;
} else {
 lean::inc(x_51);
 lean::dec(x_42);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 0);
x_56 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 x_58 = x_51;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_51);
 x_58 = lean::box(0);
}
x_59 = l_lean_elaborator_mangle__ident(x_18);
x_60 = lean::unbox(x_15);
lean::inc(x_59);
x_62 = lean_expr_local(x_59, x_59, x_37, x_60);
if (lean::is_scalar(x_11)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_11;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_54);
if (lean::is_scalar(x_58)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_58;
}
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
x_41 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_43 = x_36;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_36);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_39);
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
obj* x_27; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_39; 
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
lean::dec(x_17);
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
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_30);
lean::dec(x_34);
x_46 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_48 = x_39;
} else {
 lean::inc(x_46);
 lean::dec(x_39);
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
obj* x_68; obj* x_70; obj* x_71; 
lean::dec(x_13);
lean::dec(x_30);
lean::dec(x_34);
lean::dec(x_60);
lean::dec(x_55);
lean::dec(x_56);
x_68 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_70 = x_61;
} else {
 lean::inc(x_68);
 lean::dec(x_61);
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
obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_72 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_74 = x_61;
} else {
 lean::inc(x_72);
 lean::dec(x_61);
 x_74 = lean::box(0);
}
x_75 = lean::cnstr_get(x_72, 0);
x_77 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 x_79 = x_72;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::dec(x_72);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_79;
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
if (lean::is_scalar(x_34)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_34;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_77);
if (lean::is_scalar(x_74)) {
 x_84 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_84 = x_74;
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
lean::dec(x_5);
return x_16;
}
else
{
obj* x_18; obj* x_20; obj* x_22; obj* x_25; obj* x_28; obj* x_32; 
x_18 = lean::cnstr_get(x_2, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_2, 2);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_2, 4);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_6, 1);
lean::inc(x_25);
lean::dec(x_6);
x_28 = lean::cnstr_get(x_8, 0);
lean::inc(x_28);
lean::dec(x_8);
lean::inc(x_4);
x_32 = l_lean_elaborator_decl__modifiers__to__pexpr(x_1, x_4, x_5);
if (lean::obj_tag(x_32) == 0)
{
obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_20);
lean::dec(x_22);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_18);
lean::dec(x_25);
lean::dec(x_28);
x_40 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_42 = x_32;
} else {
 lean::inc(x_40);
 lean::dec(x_32);
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
x_44 = lean::cnstr_get(x_32, 0);
lean::inc(x_44);
lean::dec(x_32);
x_47 = lean::cnstr_get(x_44, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_44, 1);
lean::inc(x_49);
lean::dec(x_44);
x_52 = lean::box(0);
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_3);
x_54 = lean_expr_mk_lit(x_53);
if (lean::obj_tag(x_18) == 0)
{
obj* x_58; obj* x_61; 
x_58 = l_lean_expander_get__opt__type___main(x_25);
lean::dec(x_25);
lean::inc(x_4);
x_61 = l_lean_elaborator_to__pexpr___main(x_58, x_4, x_49);
if (lean::obj_tag(x_18) == 0)
{
if (lean::obj_tag(x_61) == 0)
{
obj* x_68; obj* x_70; obj* x_71; 
lean::dec(x_20);
lean::dec(x_22);
lean::dec(x_4);
lean::dec(x_47);
lean::dec(x_28);
lean::dec(x_54);
x_68 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_70 = x_61;
} else {
 lean::inc(x_68);
 lean::dec(x_61);
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
x_72 = lean::cnstr_get(x_61, 0);
lean::inc(x_72);
lean::dec(x_61);
x_55 = x_52;
x_56 = x_72;
goto lbl_57;
}
}
else
{
if (lean::obj_tag(x_61) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_20);
lean::dec(x_22);
lean::dec(x_4);
lean::dec(x_47);
lean::dec(x_28);
lean::dec(x_54);
x_81 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_83 = x_61;
} else {
 lean::inc(x_81);
 lean::dec(x_61);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_81);
return x_84;
}
else
{
obj* x_85; obj* x_88; obj* x_91; obj* x_94; 
x_85 = lean::cnstr_get(x_18, 0);
lean::inc(x_85);
lean::dec(x_18);
x_88 = lean::cnstr_get(x_61, 0);
lean::inc(x_88);
lean::dec(x_61);
x_91 = lean::cnstr_get(x_85, 1);
lean::inc(x_91);
lean::dec(x_85);
x_94 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(x_91);
x_55 = x_94;
x_56 = x_88;
goto lbl_57;
}
}
}
else
{
obj* x_95; obj* x_97; obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_115; obj* x_116; obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_125; obj* x_128; obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_137; obj* x_139; obj* x_142; obj* x_143; obj* x_146; 
x_95 = lean::cnstr_get(x_18, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_49, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_49, 1);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_49, 2);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_49, 3);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_49, 4);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_105, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_105, 1);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_95, 1);
lean::inc(x_111);
lean::dec(x_95);
lean::inc(x_111);
x_115 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(x_111);
x_116 = l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(x_109, x_115);
x_117 = lean::cnstr_get(x_105, 2);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_105, 3);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_105, 4);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_105, 5);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_105, 6);
lean::inc(x_125);
lean::dec(x_105);
x_128 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_128, 0, x_107);
lean::cnstr_set(x_128, 1, x_116);
lean::cnstr_set(x_128, 2, x_117);
lean::cnstr_set(x_128, 3, x_119);
lean::cnstr_set(x_128, 4, x_121);
lean::cnstr_set(x_128, 5, x_123);
lean::cnstr_set(x_128, 6, x_125);
x_129 = lean::cnstr_get(x_49, 5);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_49, 6);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_49, 7);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_49, 8);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_49, 9);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_49, 10);
lean::inc(x_139);
lean::dec(x_49);
x_142 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_142, 0, x_97);
lean::cnstr_set(x_142, 1, x_99);
lean::cnstr_set(x_142, 2, x_101);
lean::cnstr_set(x_142, 3, x_103);
lean::cnstr_set(x_142, 4, x_128);
lean::cnstr_set(x_142, 5, x_129);
lean::cnstr_set(x_142, 6, x_131);
lean::cnstr_set(x_142, 7, x_133);
lean::cnstr_set(x_142, 8, x_135);
lean::cnstr_set(x_142, 9, x_137);
lean::cnstr_set(x_142, 10, x_139);
x_143 = l_lean_expander_get__opt__type___main(x_25);
lean::dec(x_25);
lean::inc(x_4);
x_146 = l_lean_elaborator_to__pexpr___main(x_143, x_4, x_142);
if (lean::obj_tag(x_18) == 0)
{
lean::dec(x_111);
if (lean::obj_tag(x_146) == 0)
{
obj* x_154; obj* x_156; obj* x_157; 
lean::dec(x_20);
lean::dec(x_22);
lean::dec(x_4);
lean::dec(x_47);
lean::dec(x_28);
lean::dec(x_54);
x_154 = lean::cnstr_get(x_146, 0);
if (lean::is_exclusive(x_146)) {
 x_156 = x_146;
} else {
 lean::inc(x_154);
 lean::dec(x_146);
 x_156 = lean::box(0);
}
if (lean::is_scalar(x_156)) {
 x_157 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_157 = x_156;
}
lean::cnstr_set(x_157, 0, x_154);
return x_157;
}
else
{
obj* x_158; 
x_158 = lean::cnstr_get(x_146, 0);
lean::inc(x_158);
lean::dec(x_146);
x_55 = x_52;
x_56 = x_158;
goto lbl_57;
}
}
else
{
lean::dec(x_18);
if (lean::obj_tag(x_146) == 0)
{
obj* x_169; obj* x_171; obj* x_172; 
lean::dec(x_20);
lean::dec(x_22);
lean::dec(x_4);
lean::dec(x_47);
lean::dec(x_28);
lean::dec(x_54);
lean::dec(x_111);
x_169 = lean::cnstr_get(x_146, 0);
if (lean::is_exclusive(x_146)) {
 x_171 = x_146;
} else {
 lean::inc(x_169);
 lean::dec(x_146);
 x_171 = lean::box(0);
}
if (lean::is_scalar(x_171)) {
 x_172 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_172 = x_171;
}
lean::cnstr_set(x_172, 0, x_169);
return x_172;
}
else
{
obj* x_173; obj* x_176; 
x_173 = lean::cnstr_get(x_146, 0);
lean::inc(x_173);
lean::dec(x_146);
x_176 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(x_111);
x_55 = x_176;
x_56 = x_173;
goto lbl_57;
}
}
}
lbl_57:
{
obj* x_177; obj* x_179; obj* x_181; obj* x_182; obj* x_183; obj* x_185; uint8 x_186; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
x_177 = lean::cnstr_get(x_56, 0);
x_179 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_set(x_56, 0, lean::box(0));
 lean::cnstr_set(x_56, 1, lean::box(0));
 x_181 = x_56;
} else {
 lean::inc(x_177);
 lean::inc(x_179);
 lean::dec(x_56);
 x_181 = lean::box(0);
}
x_182 = l_lean_elaborator_names__to__pexpr(x_55);
x_183 = lean::cnstr_get(x_20, 0);
lean::inc(x_183);
x_185 = l_lean_elaborator_mangle__ident(x_183);
x_186 = 4;
lean::inc(x_177);
lean::inc(x_185);
x_189 = lean_expr_local(x_185, x_185, x_177, x_186);
x_190 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_190, 0, x_189);
lean::cnstr_set(x_190, 1, x_52);
x_191 = l_lean_elaborator_mk__eqns___closed__1;
x_192 = l_lean_expr_mk__capp(x_191, x_190);
switch (lean::obj_tag(x_22)) {
case 0:
{
obj* x_198; obj* x_201; obj* x_205; 
lean::dec(x_177);
lean::dec(x_181);
lean::dec(x_20);
x_198 = lean::cnstr_get(x_22, 0);
lean::inc(x_198);
lean::dec(x_22);
x_201 = lean::cnstr_get(x_198, 1);
lean::inc(x_201);
lean::dec(x_198);
lean::inc(x_4);
x_205 = l_lean_elaborator_to__pexpr___main(x_201, x_4, x_179);
if (lean::obj_tag(x_205) == 0)
{
obj* x_212; obj* x_214; obj* x_215; 
lean::dec(x_192);
lean::dec(x_182);
lean::dec(x_4);
lean::dec(x_47);
lean::dec(x_28);
lean::dec(x_54);
x_212 = lean::cnstr_get(x_205, 0);
if (lean::is_exclusive(x_205)) {
 x_214 = x_205;
} else {
 lean::inc(x_212);
 lean::dec(x_205);
 x_214 = lean::box(0);
}
if (lean::is_scalar(x_214)) {
 x_215 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_215 = x_214;
}
lean::cnstr_set(x_215, 0, x_212);
return x_215;
}
else
{
obj* x_216; 
x_216 = lean::cnstr_get(x_205, 0);
lean::inc(x_216);
lean::dec(x_205);
x_193 = x_216;
goto lbl_194;
}
}
case 1:
{
obj* x_221; obj* x_222; 
lean::dec(x_20);
lean::dec(x_22);
x_221 = l_lean_elaborator_mk__eqns(x_177, x_52);
if (lean::is_scalar(x_181)) {
 x_222 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_222 = x_181;
}
lean::cnstr_set(x_222, 0, x_221);
lean::cnstr_set(x_222, 1, x_179);
x_193 = x_222;
goto lbl_194;
}
default:
{
obj* x_224; obj* x_228; 
lean::dec(x_181);
x_224 = lean::cnstr_get(x_22, 0);
lean::inc(x_224);
lean::dec(x_22);
lean::inc(x_4);
x_228 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_20, x_224, x_4, x_179);
if (lean::obj_tag(x_228) == 0)
{
obj* x_236; obj* x_238; obj* x_239; 
lean::dec(x_177);
lean::dec(x_192);
lean::dec(x_182);
lean::dec(x_4);
lean::dec(x_47);
lean::dec(x_28);
lean::dec(x_54);
x_236 = lean::cnstr_get(x_228, 0);
if (lean::is_exclusive(x_228)) {
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
obj* x_240; obj* x_243; obj* x_245; obj* x_247; obj* x_248; obj* x_249; 
x_240 = lean::cnstr_get(x_228, 0);
lean::inc(x_240);
lean::dec(x_228);
x_243 = lean::cnstr_get(x_240, 0);
x_245 = lean::cnstr_get(x_240, 1);
if (lean::is_exclusive(x_240)) {
 x_247 = x_240;
} else {
 lean::inc(x_243);
 lean::inc(x_245);
 lean::dec(x_240);
 x_247 = lean::box(0);
}
x_248 = l_lean_elaborator_mk__eqns(x_177, x_243);
if (lean::is_scalar(x_247)) {
 x_249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_249 = x_247;
}
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_245);
x_193 = x_249;
goto lbl_194;
}
}
}
lbl_194:
{
obj* x_250; obj* x_252; obj* x_256; 
x_250 = lean::cnstr_get(x_193, 0);
lean::inc(x_250);
x_252 = lean::cnstr_get(x_193, 1);
lean::inc(x_252);
lean::dec(x_193);
lean::inc(x_4);
x_256 = l_lean_elaborator_simple__binders__to__pexpr(x_28, x_4, x_252);
if (lean::obj_tag(x_256) == 0)
{
obj* x_263; obj* x_265; obj* x_266; 
lean::dec(x_192);
lean::dec(x_182);
lean::dec(x_250);
lean::dec(x_4);
lean::dec(x_47);
lean::dec(x_54);
x_263 = lean::cnstr_get(x_256, 0);
if (lean::is_exclusive(x_256)) {
 x_265 = x_256;
} else {
 lean::inc(x_263);
 lean::dec(x_256);
 x_265 = lean::box(0);
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
obj* x_267; obj* x_270; obj* x_272; obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
x_267 = lean::cnstr_get(x_256, 0);
lean::inc(x_267);
lean::dec(x_256);
x_270 = lean::cnstr_get(x_267, 0);
lean::inc(x_270);
x_272 = lean::cnstr_get(x_267, 1);
lean::inc(x_272);
lean::dec(x_267);
x_275 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_275, 0, x_250);
lean::cnstr_set(x_275, 1, x_52);
x_276 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_276, 0, x_270);
lean::cnstr_set(x_276, 1, x_275);
x_277 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_277, 0, x_192);
lean::cnstr_set(x_277, 1, x_276);
x_278 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_278, 0, x_182);
lean::cnstr_set(x_278, 1, x_277);
x_279 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_279, 0, x_54);
lean::cnstr_set(x_279, 1, x_278);
x_280 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_280, 0, x_47);
lean::cnstr_set(x_280, 1, x_279);
x_281 = l_lean_expr_mk__capp(x_191, x_280);
x_282 = l_lean_elaborator_elab__def__like___closed__2;
x_283 = lean_expr_mk_mdata(x_282, x_281);
x_284 = l_lean_elaborator_old__elab__command(x_0, x_283, x_4, x_272);
return x_284;
}
}
}
}
}
}
}
obj* l_lean_elaborator_elab__def__like___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_elaborator_elab__def__like(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
return x_6;
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_lean_elaborator_infer__mod__to__pexpr___closed__2;
return x_3;
}
else
{
obj* x_4; 
x_4 = l_lean_elaborator_infer__mod__to__pexpr___closed__3;
return x_4;
}
}
}
}
obj* l_lean_elaborator_infer__mod__to__pexpr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_infer__mod__to__pexpr(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_12 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_1);
 x_12 = lean::box(0);
}
x_15 = lean::cnstr_get(x_8, 3);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_22; obj* x_24; 
lean::dec(x_15);
lean::dec(x_8);
lean::dec(x_17);
x_22 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
x_24 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_22, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_24) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_31 = x_24;
} else {
 lean::inc(x_29);
 lean::dec(x_24);
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
obj* x_33; 
x_33 = lean::cnstr_get(x_24, 0);
lean::inc(x_33);
lean::dec(x_24);
x_13 = x_33;
goto lbl_14;
}
}
else
{
obj* x_36; 
x_36 = lean::cnstr_get(x_17, 0);
lean::inc(x_36);
lean::dec(x_17);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; 
x_39 = lean::cnstr_get(x_15, 1);
lean::inc(x_39);
lean::dec(x_15);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_45; 
lean::dec(x_8);
x_43 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
x_45 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_43, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_45) == 0)
{
obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_50 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 x_52 = x_45;
} else {
 lean::inc(x_50);
 lean::dec(x_45);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
return x_53;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_45, 0);
lean::inc(x_54);
lean::dec(x_45);
x_13 = x_54;
goto lbl_14;
}
}
else
{
obj* x_57; obj* x_60; obj* x_64; 
x_57 = lean::cnstr_get(x_39, 0);
lean::inc(x_57);
lean::dec(x_39);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
lean::inc(x_2);
x_64 = l_lean_elaborator_to__pexpr___main(x_60, x_2, x_3);
if (lean::obj_tag(x_64) == 0)
{
obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_69 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_71 = x_64;
} else {
 lean::inc(x_69);
 lean::dec(x_64);
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
obj* x_73; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_84; uint8 x_85; obj* x_87; obj* x_88; 
x_73 = lean::cnstr_get(x_64, 0);
lean::inc(x_73);
lean::dec(x_64);
x_76 = lean::cnstr_get(x_73, 0);
x_78 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 x_80 = x_73;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::dec(x_73);
 x_80 = lean::box(0);
}
x_81 = lean::cnstr_get(x_8, 1);
lean::inc(x_81);
lean::dec(x_8);
x_84 = l_lean_elaborator_mangle__ident(x_81);
x_85 = 0;
lean::inc(x_84);
x_87 = lean_expr_local(x_84, x_84, x_76, x_85);
if (lean::is_scalar(x_80)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_80;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_78);
x_13 = x_88;
goto lbl_14;
}
}
}
else
{
obj* x_92; obj* x_94; 
lean::dec(x_15);
lean::dec(x_8);
lean::dec(x_36);
x_92 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
x_94 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_92, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_94) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
obj* x_103; 
x_103 = lean::cnstr_get(x_94, 0);
lean::inc(x_103);
lean::dec(x_94);
x_13 = x_103;
goto lbl_14;
}
}
}
lbl_14:
{
obj* x_106; obj* x_108; obj* x_111; 
x_106 = lean::cnstr_get(x_13, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_13, 1);
lean::inc(x_108);
lean::dec(x_13);
x_111 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_10, x_2, x_108);
if (lean::obj_tag(x_111) == 0)
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_12);
lean::dec(x_106);
x_114 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_116 = x_111;
} else {
 lean::inc(x_114);
 lean::dec(x_111);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_114);
return x_117;
}
else
{
obj* x_118; obj* x_120; obj* x_121; obj* x_123; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
x_118 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_120 = x_111;
} else {
 lean::inc(x_118);
 lean::dec(x_111);
 x_120 = lean::box(0);
}
x_121 = lean::cnstr_get(x_118, 0);
x_123 = lean::cnstr_get(x_118, 1);
if (lean::is_exclusive(x_118)) {
 x_125 = x_118;
} else {
 lean::inc(x_121);
 lean::inc(x_123);
 lean::dec(x_118);
 x_125 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_126 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_126 = x_12;
}
lean::cnstr_set(x_126, 0, x_106);
lean::cnstr_set(x_126, 1, x_121);
if (lean::is_scalar(x_125)) {
 x_127 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_127 = x_125;
}
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_123);
if (lean::is_scalar(x_120)) {
 x_128 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_128 = x_120;
}
lean::cnstr_set(x_128, 0, x_127);
return x_128;
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_12; obj* x_13; 
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
lean::dec(x_7);
x_12 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(x_4);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_41 = x_32;
} else {
 lean::inc(x_39);
 lean::dec(x_32);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_11;
}
lean::cnstr_set(x_47, 0, x_27);
lean::cnstr_set(x_47, 1, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_12 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_1);
 x_12 = lean::box(0);
}
switch (lean::obj_tag(x_8)) {
case 0:
{
obj* x_15; obj* x_18; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
if (lean::obj_tag(x_18) == 0)
{
obj* x_22; obj* x_24; 
lean::dec(x_18);
x_22 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
x_24 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_22, x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_24) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_31 = x_24;
} else {
 lean::inc(x_29);
 lean::dec(x_24);
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
obj* x_33; 
x_33 = lean::cnstr_get(x_24, 0);
lean::inc(x_33);
lean::dec(x_24);
x_13 = x_33;
goto lbl_14;
}
}
else
{
obj* x_36; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
x_36 = lean::cnstr_get(x_18, 0);
lean::inc(x_36);
lean::dec(x_18);
x_39 = 0;
x_40 = lean::box(x_39);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_36);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_3);
x_13 = x_42;
goto lbl_14;
}
}
case 1:
{
obj* x_43; obj* x_46; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; 
x_43 = lean::cnstr_get(x_8, 0);
lean::inc(x_43);
lean::dec(x_8);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
x_49 = 1;
x_50 = lean::box(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_46);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_3);
x_13 = x_52;
goto lbl_14;
}
case 2:
{
obj* x_53; obj* x_56; uint8 x_59; obj* x_60; obj* x_61; obj* x_62; 
x_53 = lean::cnstr_get(x_8, 0);
lean::inc(x_53);
lean::dec(x_8);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
lean::dec(x_53);
x_59 = 2;
x_60 = lean::box(x_59);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_56);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_3);
x_13 = x_62;
goto lbl_14;
}
default:
{
obj* x_63; obj* x_66; uint8 x_69; obj* x_70; obj* x_71; obj* x_72; 
x_63 = lean::cnstr_get(x_8, 0);
lean::inc(x_63);
lean::dec(x_8);
x_66 = lean::cnstr_get(x_63, 1);
lean::inc(x_66);
lean::dec(x_63);
x_69 = 3;
x_70 = lean::box(x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_66);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_3);
x_13 = x_72;
goto lbl_14;
}
}
lbl_14:
{
obj* x_73; obj* x_75; obj* x_78; obj* x_80; obj* x_83; obj* x_85; obj* x_88; obj* x_91; 
x_73 = lean::cnstr_get(x_13, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_13, 1);
lean::inc(x_75);
lean::dec(x_13);
x_78 = lean::cnstr_get(x_73, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_73, 1);
lean::inc(x_80);
lean::dec(x_73);
x_83 = lean::cnstr_get(x_80, 2);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_83, 1);
lean::inc(x_85);
lean::dec(x_83);
x_88 = l_lean_expander_get__opt__type___main(x_85);
lean::dec(x_85);
lean::inc(x_2);
x_91 = l_lean_elaborator_to__pexpr___main(x_88, x_2, x_75);
if (lean::obj_tag(x_91) == 0)
{
obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_80);
lean::dec(x_78);
x_97 = lean::cnstr_get(x_91, 0);
if (lean::is_exclusive(x_91)) {
 x_99 = x_91;
} else {
 lean::inc(x_97);
 lean::dec(x_91);
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
obj* x_101; obj* x_104; obj* x_106; obj* x_109; 
x_101 = lean::cnstr_get(x_91, 0);
lean::inc(x_101);
lean::dec(x_91);
x_104 = lean::cnstr_get(x_101, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
lean::dec(x_101);
x_109 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_10, x_2, x_106);
if (lean::obj_tag(x_109) == 0)
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_12);
lean::dec(x_80);
lean::dec(x_78);
lean::dec(x_104);
x_114 = lean::cnstr_get(x_109, 0);
if (lean::is_exclusive(x_109)) {
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
return x_117;
}
else
{
obj* x_118; obj* x_120; obj* x_121; obj* x_123; obj* x_125; obj* x_126; obj* x_127; uint8 x_128; obj* x_129; obj* x_130; obj* x_132; obj* x_133; obj* x_134; obj* x_137; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_118 = lean::cnstr_get(x_109, 0);
if (lean::is_exclusive(x_109)) {
 x_120 = x_109;
} else {
 lean::inc(x_118);
 lean::dec(x_109);
 x_120 = lean::box(0);
}
x_121 = lean::cnstr_get(x_118, 0);
x_123 = lean::cnstr_get(x_118, 1);
if (lean::is_exclusive(x_118)) {
 x_125 = x_118;
} else {
 lean::inc(x_121);
 lean::inc(x_123);
 lean::dec(x_118);
 x_125 = lean::box(0);
}
x_126 = l_lean_elaborator_mk__eqns___closed__1;
x_127 = l_lean_elaborator_dummy;
x_128 = lean::unbox(x_78);
x_129 = lean_expr_local(x_126, x_126, x_127, x_128);
x_130 = lean::cnstr_get(x_80, 0);
lean::inc(x_130);
x_132 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(x_130);
x_133 = l_lean_elaborator_names__to__pexpr(x_132);
x_134 = lean::cnstr_get(x_80, 1);
lean::inc(x_134);
lean::dec(x_80);
x_137 = l_lean_elaborator_infer__mod__to__pexpr(x_134);
lean::dec(x_134);
x_139 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_140 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_140 = x_12;
}
lean::cnstr_set(x_140, 0, x_104);
lean::cnstr_set(x_140, 1, x_139);
x_141 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_141, 0, x_137);
lean::cnstr_set(x_141, 1, x_140);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_133);
lean::cnstr_set(x_142, 1, x_141);
x_143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_143, 0, x_129);
lean::cnstr_set(x_143, 1, x_142);
x_144 = l_lean_expr_mk__capp(x_126, x_143);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_121);
if (lean::is_scalar(x_125)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_125;
}
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_123);
if (lean::is_scalar(x_120)) {
 x_147 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_147 = x_120;
}
lean::cnstr_set(x_147, 0, x_146);
return x_147;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string(".");
x_2 = lean::box(0);
x_3 = l_lean_name_to__string__with__sep___main(x_1, x_2);
lean::dec(x_1);
x_5 = l_lean_parser_substring_of__string(x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_0);
return x_8;
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
lean::dec(x_0);
x_5 = x_25;
goto lbl_6;
}
case 1:
{
obj* x_28; obj* x_31; obj* x_32; 
lean::dec(x_18);
x_28 = lean::cnstr_get(x_12, 0);
lean::inc(x_28);
lean::dec(x_12);
x_31 = lean::mk_nat_obj(5u);
x_32 = l_lean_elaborator_elab__def__like(x_0, x_28, x_15, x_31, x_1, x_2);
lean::dec(x_0);
x_5 = x_32;
goto lbl_6;
}
default:
{
obj* x_35; obj* x_38; obj* x_39; 
lean::dec(x_18);
x_35 = lean::cnstr_get(x_12, 0);
lean::inc(x_35);
lean::dec(x_12);
x_38 = lean::mk_nat_obj(0u);
x_39 = l_lean_elaborator_elab__def__like(x_0, x_35, x_15, x_38, x_1, x_2);
lean::dec(x_0);
x_5 = x_39;
goto lbl_6;
}
}
}
case 1:
{
obj* x_41; obj* x_44; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_60; obj* x_61; obj* x_62; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_41 = lean::cnstr_get(x_13, 0);
lean::inc(x_41);
lean::dec(x_13);
x_44 = lean::cnstr_get(x_12, 0);
lean::inc(x_44);
lean::dec(x_12);
x_47 = lean::box(0);
x_48 = lean::cnstr_get(x_41, 1);
lean::inc(x_48);
x_50 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
x_51 = l_option_get__or__else___main___rarg(x_48, x_50);
lean::dec(x_48);
x_53 = lean::cnstr_get(x_41, 2);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_53, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_53, 1);
lean::inc(x_57);
lean::dec(x_53);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_57);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_55);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::cnstr_get(x_41, 3);
lean::inc(x_62);
lean::dec(x_41);
x_65 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
x_66 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_47);
lean::cnstr_set(x_66, 2, x_51);
lean::cnstr_set(x_66, 3, x_61);
lean::cnstr_set(x_66, 4, x_62);
x_67 = lean::mk_nat_obj(3u);
x_68 = l_lean_elaborator_elab__def__like(x_0, x_44, x_66, x_67, x_1, x_2);
lean::dec(x_0);
x_5 = x_68;
goto lbl_6;
}
case 2:
{
obj* x_70; obj* x_73; obj* x_76; obj* x_77; obj* x_79; obj* x_81; obj* x_84; obj* x_85; obj* x_86; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_70 = lean::cnstr_get(x_13, 0);
lean::inc(x_70);
lean::dec(x_13);
x_73 = lean::cnstr_get(x_12, 0);
lean::inc(x_73);
lean::dec(x_12);
x_76 = lean::box(0);
x_77 = lean::cnstr_get(x_70, 1);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_77, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_77, 1);
lean::inc(x_81);
lean::dec(x_77);
x_84 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_84, 0, x_81);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_79);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::cnstr_get(x_70, 2);
lean::inc(x_86);
lean::dec(x_70);
x_89 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
x_90 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
x_91 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_76);
lean::cnstr_set(x_91, 2, x_90);
lean::cnstr_set(x_91, 3, x_85);
lean::cnstr_set(x_91, 4, x_86);
x_92 = lean::mk_nat_obj(2u);
x_93 = l_lean_elaborator_elab__def__like(x_0, x_73, x_91, x_92, x_1, x_2);
lean::dec(x_0);
x_5 = x_93;
goto lbl_6;
}
case 3:
{
obj* x_95; obj* x_98; obj* x_100; 
x_95 = lean::cnstr_get(x_13, 0);
lean::inc(x_95);
lean::dec(x_13);
x_98 = lean::cnstr_get(x_95, 2);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_98, 0);
lean::inc(x_100);
if (lean::obj_tag(x_100) == 0)
{
obj* x_106; obj* x_107; 
lean::dec(x_12);
lean::dec(x_98);
lean::dec(x_100);
lean::dec(x_95);
x_106 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_107 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_106, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
x_5 = x_107;
goto lbl_6;
}
else
{
obj* x_110; 
x_110 = lean::cnstr_get(x_100, 0);
lean::inc(x_110);
lean::dec(x_100);
if (lean::obj_tag(x_110) == 0)
{
obj* x_113; obj* x_116; obj* x_119; obj* x_123; 
x_113 = lean::cnstr_get(x_95, 1);
lean::inc(x_113);
lean::dec(x_95);
x_116 = lean::cnstr_get(x_98, 1);
lean::inc(x_116);
lean::dec(x_98);
x_119 = lean::cnstr_get(x_12, 0);
lean::inc(x_119);
lean::dec(x_12);
lean::inc(x_1);
x_123 = l_lean_elaborator_decl__modifiers__to__pexpr(x_119, x_1, x_2);
if (lean::obj_tag(x_123) == 0)
{
obj* x_128; obj* x_130; obj* x_131; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_113);
lean::dec(x_116);
x_128 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_130 = x_123;
} else {
 lean::inc(x_128);
 lean::dec(x_123);
 x_130 = lean::box(0);
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_128);
x_5 = x_131;
goto lbl_6;
}
else
{
obj* x_132; obj* x_135; obj* x_137; obj* x_140; obj* x_144; 
x_132 = lean::cnstr_get(x_123, 0);
lean::inc(x_132);
lean::dec(x_123);
x_135 = lean::cnstr_get(x_132, 0);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_132, 1);
lean::inc(x_137);
lean::dec(x_132);
x_140 = lean::cnstr_get(x_116, 1);
lean::inc(x_140);
lean::dec(x_116);
lean::inc(x_1);
x_144 = l_lean_elaborator_to__pexpr___main(x_140, x_1, x_137);
if (lean::obj_tag(x_144) == 0)
{
obj* x_149; obj* x_151; obj* x_152; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_135);
lean::dec(x_113);
x_149 = lean::cnstr_get(x_144, 0);
if (lean::is_exclusive(x_144)) {
 x_151 = x_144;
} else {
 lean::inc(x_149);
 lean::dec(x_144);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_149);
x_5 = x_152;
goto lbl_6;
}
else
{
obj* x_153; obj* x_156; obj* x_158; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; 
x_153 = lean::cnstr_get(x_144, 0);
lean::inc(x_153);
lean::dec(x_144);
x_156 = lean::cnstr_get(x_153, 0);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_153, 1);
lean::inc(x_158);
lean::dec(x_153);
x_161 = lean::box(0);
x_162 = l_lean_elaborator_ident__univ__params__to__pexpr(x_113);
x_163 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_163, 0, x_156);
lean::cnstr_set(x_163, 1, x_161);
x_164 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_164, 0, x_162);
lean::cnstr_set(x_164, 1, x_163);
x_165 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_165, 0, x_135);
lean::cnstr_set(x_165, 1, x_164);
x_166 = l_lean_elaborator_mk__eqns___closed__1;
x_167 = l_lean_expr_mk__capp(x_166, x_165);
x_168 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3;
x_169 = lean_expr_mk_mdata(x_168, x_167);
x_170 = l_lean_elaborator_old__elab__command(x_0, x_169, x_1, x_158);
lean::dec(x_0);
x_5 = x_170;
goto lbl_6;
}
}
}
else
{
obj* x_176; obj* x_177; 
lean::dec(x_12);
lean::dec(x_98);
lean::dec(x_95);
lean::dec(x_110);
x_176 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_177 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_176, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
x_5 = x_177;
goto lbl_6;
}
}
}
case 4:
{
obj* x_180; obj* x_183; 
x_180 = lean::cnstr_get(x_13, 0);
lean::inc(x_180);
lean::dec(x_13);
x_183 = lean::cnstr_get(x_180, 0);
lean::inc(x_183);
if (lean::obj_tag(x_183) == 0)
{
obj* x_185; obj* x_187; 
x_185 = lean::cnstr_get(x_180, 4);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_185, 0);
lean::inc(x_187);
if (lean::obj_tag(x_187) == 0)
{
obj* x_193; obj* x_194; 
lean::dec(x_185);
lean::dec(x_180);
lean::dec(x_187);
lean::dec(x_12);
x_193 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_194 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_193, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
x_5 = x_194;
goto lbl_6;
}
else
{
obj* x_197; obj* x_199; obj* x_201; obj* x_204; obj* x_207; obj* x_210; obj* x_215; 
x_197 = lean::cnstr_get(x_180, 2);
lean::inc(x_197);
x_199 = lean::cnstr_get(x_180, 3);
lean::inc(x_199);
x_201 = lean::cnstr_get(x_180, 6);
lean::inc(x_201);
lean::dec(x_180);
x_204 = lean::cnstr_get(x_185, 1);
lean::inc(x_204);
lean::dec(x_185);
x_207 = lean::cnstr_get(x_187, 0);
lean::inc(x_207);
lean::dec(x_187);
x_210 = lean::cnstr_get(x_12, 0);
lean::inc(x_210);
lean::dec(x_12);
lean::inc(x_1);
lean::inc(x_210);
x_215 = l_lean_elaborator_decl__modifiers__to__pexpr(x_210, x_1, x_2);
if (lean::obj_tag(x_215) == 0)
{
obj* x_224; obj* x_226; obj* x_227; 
lean::dec(x_199);
lean::dec(x_201);
lean::dec(x_210);
lean::dec(x_197);
lean::dec(x_207);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_204);
x_224 = lean::cnstr_get(x_215, 0);
if (lean::is_exclusive(x_215)) {
 x_226 = x_215;
} else {
 lean::inc(x_224);
 lean::dec(x_215);
 x_226 = lean::box(0);
}
if (lean::is_scalar(x_226)) {
 x_227 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_227 = x_226;
}
lean::cnstr_set(x_227, 0, x_224);
x_5 = x_227;
goto lbl_6;
}
else
{
obj* x_228; obj* x_231; obj* x_233; obj* x_236; obj* x_237; obj* x_239; 
x_228 = lean::cnstr_get(x_215, 0);
lean::inc(x_228);
lean::dec(x_215);
x_231 = lean::cnstr_get(x_228, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get(x_228, 1);
lean::inc(x_233);
lean::dec(x_228);
x_236 = lean::box(0);
x_239 = lean::cnstr_get(x_210, 1);
lean::inc(x_239);
lean::dec(x_210);
if (lean::obj_tag(x_239) == 0)
{
x_237 = x_236;
goto lbl_238;
}
else
{
obj* x_242; obj* x_245; 
x_242 = lean::cnstr_get(x_239, 0);
lean::inc(x_242);
lean::dec(x_239);
x_245 = lean::cnstr_get(x_242, 1);
lean::inc(x_245);
lean::dec(x_242);
x_237 = x_245;
goto lbl_238;
}
lbl_238:
{
obj* x_249; 
lean::inc(x_1);
x_249 = l_lean_elaborator_attrs__to__pexpr(x_237, x_1, x_233);
if (lean::obj_tag(x_249) == 0)
{
obj* x_258; obj* x_260; obj* x_261; 
lean::dec(x_199);
lean::dec(x_201);
lean::dec(x_231);
lean::dec(x_197);
lean::dec(x_207);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_204);
x_258 = lean::cnstr_get(x_249, 0);
if (lean::is_exclusive(x_249)) {
 x_260 = x_249;
} else {
 lean::inc(x_258);
 lean::dec(x_249);
 x_260 = lean::box(0);
}
if (lean::is_scalar(x_260)) {
 x_261 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_261 = x_260;
}
lean::cnstr_set(x_261, 0, x_258);
x_5 = x_261;
goto lbl_6;
}
else
{
obj* x_262; obj* x_265; obj* x_267; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_262 = lean::cnstr_get(x_249, 0);
lean::inc(x_262);
lean::dec(x_249);
x_265 = lean::cnstr_get(x_262, 0);
lean::inc(x_265);
x_267 = lean::cnstr_get(x_262, 1);
lean::inc(x_267);
lean::dec(x_262);
x_270 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_270, 0, x_265);
lean::cnstr_set(x_270, 1, x_236);
x_271 = l_lean_elaborator_mk__eqns___closed__1;
x_272 = l_lean_expr_mk__capp(x_271, x_270);
if (lean::obj_tag(x_197) == 0)
{
obj* x_276; obj* x_279; 
x_276 = l_lean_expander_get__opt__type___main(x_204);
lean::dec(x_204);
lean::inc(x_1);
x_279 = l_lean_elaborator_to__pexpr___main(x_276, x_1, x_267);
if (lean::obj_tag(x_197) == 0)
{
if (lean::obj_tag(x_279) == 0)
{
obj* x_287; obj* x_289; obj* x_290; 
lean::dec(x_199);
lean::dec(x_201);
lean::dec(x_231);
lean::dec(x_272);
lean::dec(x_207);
lean::dec(x_1);
lean::dec(x_0);
x_287 = lean::cnstr_get(x_279, 0);
if (lean::is_exclusive(x_279)) {
 x_289 = x_279;
} else {
 lean::inc(x_287);
 lean::dec(x_279);
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
obj* x_291; 
x_291 = lean::cnstr_get(x_279, 0);
lean::inc(x_291);
lean::dec(x_279);
x_273 = x_236;
x_274 = x_291;
goto lbl_275;
}
}
else
{
if (lean::obj_tag(x_279) == 0)
{
obj* x_301; obj* x_303; obj* x_304; 
lean::dec(x_199);
lean::dec(x_201);
lean::dec(x_231);
lean::dec(x_272);
lean::dec(x_207);
lean::dec(x_1);
lean::dec(x_0);
x_301 = lean::cnstr_get(x_279, 0);
if (lean::is_exclusive(x_279)) {
 x_303 = x_279;
} else {
 lean::inc(x_301);
 lean::dec(x_279);
 x_303 = lean::box(0);
}
if (lean::is_scalar(x_303)) {
 x_304 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_304 = x_303;
}
lean::cnstr_set(x_304, 0, x_301);
x_5 = x_304;
goto lbl_6;
}
else
{
obj* x_305; obj* x_308; obj* x_311; obj* x_314; 
x_305 = lean::cnstr_get(x_197, 0);
lean::inc(x_305);
lean::dec(x_197);
x_308 = lean::cnstr_get(x_279, 0);
lean::inc(x_308);
lean::dec(x_279);
x_311 = lean::cnstr_get(x_305, 1);
lean::inc(x_311);
lean::dec(x_305);
x_314 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_311);
x_273 = x_314;
x_274 = x_308;
goto lbl_275;
}
}
}
else
{
obj* x_315; obj* x_317; obj* x_319; obj* x_321; obj* x_323; obj* x_325; obj* x_327; obj* x_329; obj* x_331; obj* x_335; obj* x_336; obj* x_337; obj* x_339; obj* x_341; obj* x_343; obj* x_345; obj* x_348; obj* x_349; obj* x_351; obj* x_353; obj* x_355; obj* x_357; obj* x_359; obj* x_362; obj* x_363; obj* x_366; 
x_315 = lean::cnstr_get(x_197, 0);
lean::inc(x_315);
x_317 = lean::cnstr_get(x_267, 0);
lean::inc(x_317);
x_319 = lean::cnstr_get(x_267, 1);
lean::inc(x_319);
x_321 = lean::cnstr_get(x_267, 2);
lean::inc(x_321);
x_323 = lean::cnstr_get(x_267, 3);
lean::inc(x_323);
x_325 = lean::cnstr_get(x_267, 4);
lean::inc(x_325);
x_327 = lean::cnstr_get(x_325, 0);
lean::inc(x_327);
x_329 = lean::cnstr_get(x_325, 1);
lean::inc(x_329);
x_331 = lean::cnstr_get(x_315, 1);
lean::inc(x_331);
lean::dec(x_315);
lean::inc(x_331);
x_335 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(x_331);
x_336 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__5(x_329, x_335);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
x_339 = lean::cnstr_get(x_325, 3);
lean::inc(x_339);
x_341 = lean::cnstr_get(x_325, 4);
lean::inc(x_341);
x_343 = lean::cnstr_get(x_325, 5);
lean::inc(x_343);
x_345 = lean::cnstr_get(x_325, 6);
lean::inc(x_345);
lean::dec(x_325);
x_348 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_348, 0, x_327);
lean::cnstr_set(x_348, 1, x_336);
lean::cnstr_set(x_348, 2, x_337);
lean::cnstr_set(x_348, 3, x_339);
lean::cnstr_set(x_348, 4, x_341);
lean::cnstr_set(x_348, 5, x_343);
lean::cnstr_set(x_348, 6, x_345);
x_349 = lean::cnstr_get(x_267, 5);
lean::inc(x_349);
x_351 = lean::cnstr_get(x_267, 6);
lean::inc(x_351);
x_353 = lean::cnstr_get(x_267, 7);
lean::inc(x_353);
x_355 = lean::cnstr_get(x_267, 8);
lean::inc(x_355);
x_357 = lean::cnstr_get(x_267, 9);
lean::inc(x_357);
x_359 = lean::cnstr_get(x_267, 10);
lean::inc(x_359);
lean::dec(x_267);
x_362 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_362, 0, x_317);
lean::cnstr_set(x_362, 1, x_319);
lean::cnstr_set(x_362, 2, x_321);
lean::cnstr_set(x_362, 3, x_323);
lean::cnstr_set(x_362, 4, x_348);
lean::cnstr_set(x_362, 5, x_349);
lean::cnstr_set(x_362, 6, x_351);
lean::cnstr_set(x_362, 7, x_353);
lean::cnstr_set(x_362, 8, x_355);
lean::cnstr_set(x_362, 9, x_357);
lean::cnstr_set(x_362, 10, x_359);
x_363 = l_lean_expander_get__opt__type___main(x_204);
lean::dec(x_204);
lean::inc(x_1);
x_366 = l_lean_elaborator_to__pexpr___main(x_363, x_1, x_362);
if (lean::obj_tag(x_197) == 0)
{
lean::dec(x_331);
if (lean::obj_tag(x_366) == 0)
{
obj* x_375; obj* x_377; obj* x_378; 
lean::dec(x_199);
lean::dec(x_201);
lean::dec(x_231);
lean::dec(x_272);
lean::dec(x_207);
lean::dec(x_1);
lean::dec(x_0);
x_375 = lean::cnstr_get(x_366, 0);
if (lean::is_exclusive(x_366)) {
 x_377 = x_366;
} else {
 lean::inc(x_375);
 lean::dec(x_366);
 x_377 = lean::box(0);
}
if (lean::is_scalar(x_377)) {
 x_378 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_378 = x_377;
}
lean::cnstr_set(x_378, 0, x_375);
x_5 = x_378;
goto lbl_6;
}
else
{
obj* x_379; 
x_379 = lean::cnstr_get(x_366, 0);
lean::inc(x_379);
lean::dec(x_366);
x_273 = x_236;
x_274 = x_379;
goto lbl_275;
}
}
else
{
lean::dec(x_197);
if (lean::obj_tag(x_366) == 0)
{
obj* x_391; obj* x_393; obj* x_394; 
lean::dec(x_199);
lean::dec(x_201);
lean::dec(x_231);
lean::dec(x_272);
lean::dec(x_207);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_331);
x_391 = lean::cnstr_get(x_366, 0);
if (lean::is_exclusive(x_366)) {
 x_393 = x_366;
} else {
 lean::inc(x_391);
 lean::dec(x_366);
 x_393 = lean::box(0);
}
if (lean::is_scalar(x_393)) {
 x_394 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_394 = x_393;
}
lean::cnstr_set(x_394, 0, x_391);
x_5 = x_394;
goto lbl_6;
}
else
{
obj* x_395; obj* x_398; 
x_395 = lean::cnstr_get(x_366, 0);
lean::inc(x_395);
lean::dec(x_366);
x_398 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(x_331);
x_273 = x_398;
x_274 = x_395;
goto lbl_275;
}
}
}
lbl_275:
{
obj* x_399; obj* x_401; obj* x_405; 
x_399 = lean::cnstr_get(x_274, 0);
lean::inc(x_399);
x_401 = lean::cnstr_get(x_274, 1);
lean::inc(x_401);
lean::dec(x_274);
lean::inc(x_1);
x_405 = l_lean_elaborator_simple__binders__to__pexpr(x_207, x_1, x_401);
if (lean::obj_tag(x_405) == 0)
{
obj* x_414; obj* x_416; obj* x_417; 
lean::dec(x_199);
lean::dec(x_201);
lean::dec(x_231);
lean::dec(x_272);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_273);
lean::dec(x_399);
x_414 = lean::cnstr_get(x_405, 0);
if (lean::is_exclusive(x_405)) {
 x_416 = x_405;
} else {
 lean::inc(x_414);
 lean::dec(x_405);
 x_416 = lean::box(0);
}
if (lean::is_scalar(x_416)) {
 x_417 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_417 = x_416;
}
lean::cnstr_set(x_417, 0, x_414);
x_5 = x_417;
goto lbl_6;
}
else
{
obj* x_418; obj* x_421; obj* x_423; obj* x_428; 
x_418 = lean::cnstr_get(x_405, 0);
lean::inc(x_418);
lean::dec(x_405);
x_421 = lean::cnstr_get(x_418, 0);
lean::inc(x_421);
x_423 = lean::cnstr_get(x_418, 1);
lean::inc(x_423);
lean::dec(x_418);
lean::inc(x_1);
lean::inc(x_201);
x_428 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_201, x_1, x_423);
if (lean::obj_tag(x_428) == 0)
{
obj* x_438; obj* x_440; obj* x_441; 
lean::dec(x_199);
lean::dec(x_201);
lean::dec(x_231);
lean::dec(x_272);
lean::dec(x_421);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_273);
lean::dec(x_399);
x_438 = lean::cnstr_get(x_428, 0);
if (lean::is_exclusive(x_428)) {
 x_440 = x_428;
} else {
 lean::inc(x_438);
 lean::dec(x_428);
 x_440 = lean::box(0);
}
if (lean::is_scalar(x_440)) {
 x_441 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_441 = x_440;
}
lean::cnstr_set(x_441, 0, x_438);
x_5 = x_441;
goto lbl_6;
}
else
{
obj* x_442; obj* x_445; obj* x_447; obj* x_450; obj* x_451; obj* x_454; uint8 x_455; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; 
x_442 = lean::cnstr_get(x_428, 0);
lean::inc(x_442);
lean::dec(x_428);
x_445 = lean::cnstr_get(x_442, 0);
lean::inc(x_445);
x_447 = lean::cnstr_get(x_442, 1);
lean::inc(x_447);
lean::dec(x_442);
x_450 = l_lean_elaborator_names__to__pexpr(x_273);
x_451 = lean::cnstr_get(x_199, 0);
lean::inc(x_451);
lean::dec(x_199);
x_454 = l_lean_elaborator_mangle__ident(x_451);
x_455 = 0;
lean::inc(x_454);
x_457 = lean_expr_local(x_454, x_454, x_399, x_455);
x_458 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_458, 0, x_457);
lean::cnstr_set(x_458, 1, x_236);
x_459 = l_lean_expr_mk__capp(x_271, x_458);
x_460 = l_lean_expr_mk__capp(x_271, x_445);
x_461 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_461, 0, x_460);
lean::cnstr_set(x_461, 1, x_236);
x_462 = l_lean_expr_mk__capp(x_271, x_461);
x_463 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(x_201);
x_464 = l_lean_expr_mk__capp(x_271, x_463);
x_465 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_465, 0, x_464);
lean::cnstr_set(x_465, 1, x_236);
x_466 = l_lean_expr_mk__capp(x_271, x_465);
x_467 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_467, 0, x_466);
lean::cnstr_set(x_467, 1, x_236);
x_468 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_468, 0, x_462);
lean::cnstr_set(x_468, 1, x_467);
x_469 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_469, 0, x_421);
lean::cnstr_set(x_469, 1, x_468);
x_470 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_470, 0, x_459);
lean::cnstr_set(x_470, 1, x_469);
x_471 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_471, 0, x_450);
lean::cnstr_set(x_471, 1, x_470);
x_472 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_472, 0, x_272);
lean::cnstr_set(x_472, 1, x_471);
x_473 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_473, 0, x_231);
lean::cnstr_set(x_473, 1, x_472);
x_474 = l_lean_expr_mk__capp(x_271, x_473);
x_475 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
x_476 = lean_expr_mk_mdata(x_475, x_474);
x_477 = l_lean_elaborator_old__elab__command(x_0, x_476, x_1, x_447);
lean::dec(x_0);
x_5 = x_477;
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
obj* x_482; obj* x_483; 
lean::dec(x_183);
lean::dec(x_180);
lean::dec(x_12);
x_482 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_483 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_482, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
x_5 = x_483;
goto lbl_6;
}
}
default:
{
obj* x_486; obj* x_489; 
x_486 = lean::cnstr_get(x_13, 0);
lean::inc(x_486);
lean::dec(x_13);
x_489 = lean::cnstr_get(x_486, 0);
lean::inc(x_489);
if (lean::obj_tag(x_489) == 0)
{
obj* x_492; obj* x_494; 
lean::dec(x_489);
x_492 = lean::cnstr_get(x_486, 3);
lean::inc(x_492);
x_494 = lean::cnstr_get(x_492, 0);
lean::inc(x_494);
if (lean::obj_tag(x_494) == 0)
{
obj* x_500; obj* x_501; 
lean::dec(x_486);
lean::dec(x_12);
lean::dec(x_492);
lean::dec(x_494);
x_500 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_501 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_500, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
x_5 = x_501;
goto lbl_6;
}
else
{
obj* x_504; obj* x_506; obj* x_508; obj* x_510; obj* x_512; obj* x_515; obj* x_518; obj* x_521; obj* x_525; 
x_504 = lean::cnstr_get(x_486, 1);
lean::inc(x_504);
x_506 = lean::cnstr_get(x_486, 2);
lean::inc(x_506);
x_508 = lean::cnstr_get(x_486, 4);
lean::inc(x_508);
x_510 = lean::cnstr_get(x_486, 6);
lean::inc(x_510);
x_512 = lean::cnstr_get(x_486, 7);
lean::inc(x_512);
lean::dec(x_486);
x_515 = lean::cnstr_get(x_492, 1);
lean::inc(x_515);
lean::dec(x_492);
x_518 = lean::cnstr_get(x_494, 0);
lean::inc(x_518);
lean::dec(x_494);
x_521 = lean::cnstr_get(x_12, 0);
lean::inc(x_521);
lean::dec(x_12);
lean::inc(x_1);
x_525 = l_lean_elaborator_decl__modifiers__to__pexpr(x_521, x_1, x_2);
if (lean::obj_tag(x_525) == 0)
{
obj* x_535; obj* x_537; obj* x_538; 
lean::dec(x_515);
lean::dec(x_518);
lean::dec(x_510);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_512);
lean::dec(x_506);
lean::dec(x_504);
lean::dec(x_508);
x_535 = lean::cnstr_get(x_525, 0);
if (lean::is_exclusive(x_525)) {
 x_537 = x_525;
} else {
 lean::inc(x_535);
 lean::dec(x_525);
 x_537 = lean::box(0);
}
if (lean::is_scalar(x_537)) {
 x_538 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_538 = x_537;
}
lean::cnstr_set(x_538, 0, x_535);
x_5 = x_538;
goto lbl_6;
}
else
{
obj* x_539; obj* x_542; obj* x_544; obj* x_547; obj* x_548; obj* x_549; 
x_539 = lean::cnstr_get(x_525, 0);
lean::inc(x_539);
lean::dec(x_525);
x_542 = lean::cnstr_get(x_539, 0);
lean::inc(x_542);
x_544 = lean::cnstr_get(x_539, 1);
lean::inc(x_544);
lean::dec(x_539);
x_547 = lean::box(0);
if (lean::obj_tag(x_504) == 0)
{
obj* x_551; obj* x_554; 
x_551 = l_lean_expander_get__opt__type___main(x_515);
lean::dec(x_515);
lean::inc(x_1);
x_554 = l_lean_elaborator_to__pexpr___main(x_551, x_1, x_544);
if (lean::obj_tag(x_504) == 0)
{
if (lean::obj_tag(x_554) == 0)
{
obj* x_563; obj* x_565; obj* x_566; 
lean::dec(x_518);
lean::dec(x_510);
lean::dec(x_542);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_512);
lean::dec(x_506);
lean::dec(x_508);
x_563 = lean::cnstr_get(x_554, 0);
if (lean::is_exclusive(x_554)) {
 x_565 = x_554;
} else {
 lean::inc(x_563);
 lean::dec(x_554);
 x_565 = lean::box(0);
}
if (lean::is_scalar(x_565)) {
 x_566 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_566 = x_565;
}
lean::cnstr_set(x_566, 0, x_563);
x_5 = x_566;
goto lbl_6;
}
else
{
obj* x_567; 
x_567 = lean::cnstr_get(x_554, 0);
lean::inc(x_567);
lean::dec(x_554);
x_548 = x_547;
x_549 = x_567;
goto lbl_550;
}
}
else
{
if (lean::obj_tag(x_554) == 0)
{
obj* x_578; obj* x_580; obj* x_581; 
lean::dec(x_518);
lean::dec(x_510);
lean::dec(x_542);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_512);
lean::dec(x_506);
lean::dec(x_508);
x_578 = lean::cnstr_get(x_554, 0);
if (lean::is_exclusive(x_554)) {
 x_580 = x_554;
} else {
 lean::inc(x_578);
 lean::dec(x_554);
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
obj* x_582; obj* x_585; obj* x_588; obj* x_591; 
x_582 = lean::cnstr_get(x_504, 0);
lean::inc(x_582);
lean::dec(x_504);
x_585 = lean::cnstr_get(x_554, 0);
lean::inc(x_585);
lean::dec(x_554);
x_588 = lean::cnstr_get(x_582, 1);
lean::inc(x_588);
lean::dec(x_582);
x_591 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(x_588);
x_548 = x_591;
x_549 = x_585;
goto lbl_550;
}
}
}
else
{
obj* x_592; obj* x_594; obj* x_596; obj* x_598; obj* x_600; obj* x_602; obj* x_604; obj* x_606; obj* x_608; obj* x_612; obj* x_613; obj* x_614; obj* x_616; obj* x_618; obj* x_620; obj* x_622; obj* x_625; obj* x_626; obj* x_628; obj* x_630; obj* x_632; obj* x_634; obj* x_636; obj* x_639; obj* x_640; obj* x_643; 
x_592 = lean::cnstr_get(x_504, 0);
lean::inc(x_592);
x_594 = lean::cnstr_get(x_544, 0);
lean::inc(x_594);
x_596 = lean::cnstr_get(x_544, 1);
lean::inc(x_596);
x_598 = lean::cnstr_get(x_544, 2);
lean::inc(x_598);
x_600 = lean::cnstr_get(x_544, 3);
lean::inc(x_600);
x_602 = lean::cnstr_get(x_544, 4);
lean::inc(x_602);
x_604 = lean::cnstr_get(x_602, 0);
lean::inc(x_604);
x_606 = lean::cnstr_get(x_602, 1);
lean::inc(x_606);
x_608 = lean::cnstr_get(x_592, 1);
lean::inc(x_608);
lean::dec(x_592);
lean::inc(x_608);
x_612 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(x_608);
x_613 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(x_606, x_612);
x_614 = lean::cnstr_get(x_602, 2);
lean::inc(x_614);
x_616 = lean::cnstr_get(x_602, 3);
lean::inc(x_616);
x_618 = lean::cnstr_get(x_602, 4);
lean::inc(x_618);
x_620 = lean::cnstr_get(x_602, 5);
lean::inc(x_620);
x_622 = lean::cnstr_get(x_602, 6);
lean::inc(x_622);
lean::dec(x_602);
x_625 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_625, 0, x_604);
lean::cnstr_set(x_625, 1, x_613);
lean::cnstr_set(x_625, 2, x_614);
lean::cnstr_set(x_625, 3, x_616);
lean::cnstr_set(x_625, 4, x_618);
lean::cnstr_set(x_625, 5, x_620);
lean::cnstr_set(x_625, 6, x_622);
x_626 = lean::cnstr_get(x_544, 5);
lean::inc(x_626);
x_628 = lean::cnstr_get(x_544, 6);
lean::inc(x_628);
x_630 = lean::cnstr_get(x_544, 7);
lean::inc(x_630);
x_632 = lean::cnstr_get(x_544, 8);
lean::inc(x_632);
x_634 = lean::cnstr_get(x_544, 9);
lean::inc(x_634);
x_636 = lean::cnstr_get(x_544, 10);
lean::inc(x_636);
lean::dec(x_544);
x_639 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_639, 0, x_594);
lean::cnstr_set(x_639, 1, x_596);
lean::cnstr_set(x_639, 2, x_598);
lean::cnstr_set(x_639, 3, x_600);
lean::cnstr_set(x_639, 4, x_625);
lean::cnstr_set(x_639, 5, x_626);
lean::cnstr_set(x_639, 6, x_628);
lean::cnstr_set(x_639, 7, x_630);
lean::cnstr_set(x_639, 8, x_632);
lean::cnstr_set(x_639, 9, x_634);
lean::cnstr_set(x_639, 10, x_636);
x_640 = l_lean_expander_get__opt__type___main(x_515);
lean::dec(x_515);
lean::inc(x_1);
x_643 = l_lean_elaborator_to__pexpr___main(x_640, x_1, x_639);
if (lean::obj_tag(x_504) == 0)
{
lean::dec(x_608);
if (lean::obj_tag(x_643) == 0)
{
obj* x_653; obj* x_655; obj* x_656; 
lean::dec(x_518);
lean::dec(x_510);
lean::dec(x_542);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_512);
lean::dec(x_506);
lean::dec(x_508);
x_653 = lean::cnstr_get(x_643, 0);
if (lean::is_exclusive(x_643)) {
 x_655 = x_643;
} else {
 lean::inc(x_653);
 lean::dec(x_643);
 x_655 = lean::box(0);
}
if (lean::is_scalar(x_655)) {
 x_656 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_656 = x_655;
}
lean::cnstr_set(x_656, 0, x_653);
x_5 = x_656;
goto lbl_6;
}
else
{
obj* x_657; 
x_657 = lean::cnstr_get(x_643, 0);
lean::inc(x_657);
lean::dec(x_643);
x_548 = x_547;
x_549 = x_657;
goto lbl_550;
}
}
else
{
lean::dec(x_504);
if (lean::obj_tag(x_643) == 0)
{
obj* x_670; obj* x_672; obj* x_673; 
lean::dec(x_518);
lean::dec(x_510);
lean::dec(x_542);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_512);
lean::dec(x_506);
lean::dec(x_508);
lean::dec(x_608);
x_670 = lean::cnstr_get(x_643, 0);
if (lean::is_exclusive(x_643)) {
 x_672 = x_643;
} else {
 lean::inc(x_670);
 lean::dec(x_643);
 x_672 = lean::box(0);
}
if (lean::is_scalar(x_672)) {
 x_673 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_673 = x_672;
}
lean::cnstr_set(x_673, 0, x_670);
x_5 = x_673;
goto lbl_6;
}
else
{
obj* x_674; obj* x_677; 
x_674 = lean::cnstr_get(x_643, 0);
lean::inc(x_674);
lean::dec(x_643);
x_677 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(x_608);
x_548 = x_677;
x_549 = x_674;
goto lbl_550;
}
}
}
lbl_550:
{
obj* x_678; obj* x_680; obj* x_684; 
x_678 = lean::cnstr_get(x_549, 0);
lean::inc(x_678);
x_680 = lean::cnstr_get(x_549, 1);
lean::inc(x_680);
lean::dec(x_549);
lean::inc(x_1);
x_684 = l_lean_elaborator_simple__binders__to__pexpr(x_518, x_1, x_680);
if (lean::obj_tag(x_684) == 0)
{
obj* x_694; obj* x_696; obj* x_697; 
lean::dec(x_510);
lean::dec(x_542);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_512);
lean::dec(x_506);
lean::dec(x_508);
lean::dec(x_548);
lean::dec(x_678);
x_694 = lean::cnstr_get(x_684, 0);
if (lean::is_exclusive(x_684)) {
 x_696 = x_684;
} else {
 lean::inc(x_694);
 lean::dec(x_684);
 x_696 = lean::box(0);
}
if (lean::is_scalar(x_696)) {
 x_697 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_697 = x_696;
}
lean::cnstr_set(x_697, 0, x_694);
x_5 = x_697;
goto lbl_6;
}
else
{
obj* x_698; obj* x_701; obj* x_703; obj* x_706; obj* x_707; obj* x_710; obj* x_711; uint8 x_712; obj* x_714; obj* x_715; 
x_698 = lean::cnstr_get(x_684, 0);
lean::inc(x_698);
lean::dec(x_684);
x_701 = lean::cnstr_get(x_698, 0);
lean::inc(x_701);
x_703 = lean::cnstr_get(x_698, 1);
lean::inc(x_703);
lean::dec(x_698);
x_706 = l_lean_elaborator_names__to__pexpr(x_548);
x_707 = lean::cnstr_get(x_506, 0);
lean::inc(x_707);
lean::dec(x_506);
x_710 = l_lean_elaborator_mangle__ident(x_707);
x_711 = l_lean_elaborator_dummy;
x_712 = 0;
lean::inc(x_710);
x_714 = lean_expr_local(x_710, x_710, x_711, x_712);
if (lean::obj_tag(x_508) == 0)
{
x_715 = x_547;
goto lbl_716;
}
else
{
obj* x_717; obj* x_720; 
x_717 = lean::cnstr_get(x_508, 0);
lean::inc(x_717);
lean::dec(x_508);
x_720 = lean::cnstr_get(x_717, 1);
lean::inc(x_720);
lean::dec(x_717);
x_715 = x_720;
goto lbl_716;
}
lbl_716:
{
obj* x_724; 
lean::inc(x_1);
x_724 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_715, x_1, x_703);
if (lean::obj_tag(x_724) == 0)
{
obj* x_734; obj* x_736; obj* x_737; 
lean::dec(x_706);
lean::dec(x_714);
lean::dec(x_510);
lean::dec(x_542);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_512);
lean::dec(x_678);
lean::dec(x_701);
x_734 = lean::cnstr_get(x_724, 0);
if (lean::is_exclusive(x_724)) {
 x_736 = x_724;
} else {
 lean::inc(x_734);
 lean::dec(x_724);
 x_736 = lean::box(0);
}
if (lean::is_scalar(x_736)) {
 x_737 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_737 = x_736;
}
lean::cnstr_set(x_737, 0, x_734);
x_5 = x_737;
goto lbl_6;
}
else
{
obj* x_738; obj* x_741; obj* x_743; obj* x_746; obj* x_747; obj* x_749; obj* x_750; 
x_738 = lean::cnstr_get(x_724, 0);
lean::inc(x_738);
lean::dec(x_724);
x_741 = lean::cnstr_get(x_738, 0);
lean::inc(x_741);
x_743 = lean::cnstr_get(x_738, 1);
lean::inc(x_743);
lean::dec(x_738);
x_746 = l_lean_elaborator_mk__eqns___closed__1;
x_747 = l_lean_expr_mk__capp(x_746, x_741);
lean::inc(x_1);
x_749 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_512, x_1, x_743);
if (lean::obj_tag(x_510) == 0)
{
obj* x_752; 
x_752 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7;
x_750 = x_752;
goto lbl_751;
}
else
{
obj* x_753; obj* x_755; obj* x_758; 
x_753 = lean::cnstr_get(x_510, 0);
lean::inc(x_753);
x_755 = lean::cnstr_get(x_753, 0);
lean::inc(x_755);
lean::dec(x_753);
x_758 = l_lean_elaborator_mangle__ident(x_755);
x_750 = x_758;
goto lbl_751;
}
lbl_751:
{
obj* x_760; 
lean::inc(x_750);
x_760 = lean_expr_local(x_750, x_750, x_711, x_712);
if (lean::obj_tag(x_510) == 0)
{
if (lean::obj_tag(x_749) == 0)
{
obj* x_770; obj* x_772; obj* x_773; 
lean::dec(x_747);
lean::dec(x_760);
lean::dec(x_706);
lean::dec(x_714);
lean::dec(x_542);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_678);
lean::dec(x_701);
x_770 = lean::cnstr_get(x_749, 0);
if (lean::is_exclusive(x_749)) {
 x_772 = x_749;
} else {
 lean::inc(x_770);
 lean::dec(x_749);
 x_772 = lean::box(0);
}
if (lean::is_scalar(x_772)) {
 x_773 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_773 = x_772;
}
lean::cnstr_set(x_773, 0, x_770);
x_5 = x_773;
goto lbl_6;
}
else
{
obj* x_774; obj* x_777; obj* x_779; obj* x_782; obj* x_783; obj* x_784; obj* x_785; obj* x_786; obj* x_787; obj* x_788; obj* x_789; obj* x_790; obj* x_791; obj* x_792; obj* x_793; obj* x_794; obj* x_795; obj* x_796; 
x_774 = lean::cnstr_get(x_749, 0);
lean::inc(x_774);
lean::dec(x_749);
x_777 = lean::cnstr_get(x_774, 0);
lean::inc(x_777);
x_779 = lean::cnstr_get(x_774, 1);
lean::inc(x_779);
lean::dec(x_774);
x_782 = l_lean_expr_mk__capp(x_746, x_777);
x_783 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_783, 0, x_782);
lean::cnstr_set(x_783, 1, x_547);
x_784 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5;
x_785 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_785, 0, x_784);
lean::cnstr_set(x_785, 1, x_783);
x_786 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_786, 0, x_760);
lean::cnstr_set(x_786, 1, x_785);
x_787 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_787, 0, x_678);
lean::cnstr_set(x_787, 1, x_786);
x_788 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_788, 0, x_747);
lean::cnstr_set(x_788, 1, x_787);
x_789 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_789, 0, x_701);
lean::cnstr_set(x_789, 1, x_788);
x_790 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_790, 0, x_714);
lean::cnstr_set(x_790, 1, x_789);
x_791 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_791, 0, x_706);
lean::cnstr_set(x_791, 1, x_790);
x_792 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_792, 0, x_542);
lean::cnstr_set(x_792, 1, x_791);
x_793 = l_lean_expr_mk__capp(x_746, x_792);
x_794 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
x_795 = lean_expr_mk_mdata(x_794, x_793);
x_796 = l_lean_elaborator_old__elab__command(x_0, x_795, x_1, x_779);
lean::dec(x_0);
x_5 = x_796;
goto lbl_6;
}
}
else
{
if (lean::obj_tag(x_749) == 0)
{
obj* x_808; obj* x_810; obj* x_811; 
lean::dec(x_747);
lean::dec(x_760);
lean::dec(x_706);
lean::dec(x_714);
lean::dec(x_510);
lean::dec(x_542);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_678);
lean::dec(x_701);
x_808 = lean::cnstr_get(x_749, 0);
if (lean::is_exclusive(x_749)) {
 x_810 = x_749;
} else {
 lean::inc(x_808);
 lean::dec(x_749);
 x_810 = lean::box(0);
}
if (lean::is_scalar(x_810)) {
 x_811 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_811 = x_810;
}
lean::cnstr_set(x_811, 0, x_808);
x_5 = x_811;
goto lbl_6;
}
else
{
obj* x_812; obj* x_815; obj* x_818; obj* x_820; obj* x_823; obj* x_826; obj* x_828; obj* x_829; obj* x_830; obj* x_831; obj* x_832; obj* x_833; obj* x_834; obj* x_835; obj* x_836; obj* x_837; obj* x_838; obj* x_839; obj* x_840; obj* x_841; 
x_812 = lean::cnstr_get(x_749, 0);
lean::inc(x_812);
lean::dec(x_749);
x_815 = lean::cnstr_get(x_510, 0);
lean::inc(x_815);
lean::dec(x_510);
x_818 = lean::cnstr_get(x_812, 0);
lean::inc(x_818);
x_820 = lean::cnstr_get(x_812, 1);
lean::inc(x_820);
lean::dec(x_812);
x_823 = lean::cnstr_get(x_815, 1);
lean::inc(x_823);
lean::dec(x_815);
x_826 = l_lean_elaborator_infer__mod__to__pexpr(x_823);
lean::dec(x_823);
x_828 = l_lean_expr_mk__capp(x_746, x_818);
x_829 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_829, 0, x_828);
lean::cnstr_set(x_829, 1, x_547);
x_830 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_830, 0, x_826);
lean::cnstr_set(x_830, 1, x_829);
x_831 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_831, 0, x_760);
lean::cnstr_set(x_831, 1, x_830);
x_832 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_832, 0, x_678);
lean::cnstr_set(x_832, 1, x_831);
x_833 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_833, 0, x_747);
lean::cnstr_set(x_833, 1, x_832);
x_834 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_834, 0, x_701);
lean::cnstr_set(x_834, 1, x_833);
x_835 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_835, 0, x_714);
lean::cnstr_set(x_835, 1, x_834);
x_836 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_836, 0, x_706);
lean::cnstr_set(x_836, 1, x_835);
x_837 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_837, 0, x_542);
lean::cnstr_set(x_837, 1, x_836);
x_838 = l_lean_expr_mk__capp(x_746, x_837);
x_839 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
x_840 = lean_expr_mk_mdata(x_839, x_838);
x_841 = l_lean_elaborator_old__elab__command(x_0, x_840, x_1, x_820);
lean::dec(x_0);
x_5 = x_841;
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
obj* x_846; obj* x_847; 
lean::dec(x_489);
lean::dec(x_486);
lean::dec(x_12);
x_846 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_847 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_846, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
x_5 = x_847;
goto lbl_6;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_851; obj* x_853; obj* x_854; 
lean::dec(x_3);
x_851 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_853 = x_5;
} else {
 lean::inc(x_851);
 lean::dec(x_5);
 x_853 = lean::box(0);
}
if (lean::is_scalar(x_853)) {
 x_854 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_854 = x_853;
}
lean::cnstr_set(x_854, 0, x_851);
return x_854;
}
else
{
obj* x_855; obj* x_857; obj* x_858; obj* x_860; obj* x_861; obj* x_863; obj* x_865; obj* x_867; obj* x_869; obj* x_871; obj* x_873; obj* x_875; obj* x_877; obj* x_879; obj* x_882; obj* x_883; obj* x_884; obj* x_885; 
x_855 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_857 = x_5;
} else {
 lean::inc(x_855);
 lean::dec(x_5);
 x_857 = lean::box(0);
}
x_858 = lean::cnstr_get(x_855, 1);
if (lean::is_exclusive(x_855)) {
 lean::cnstr_release(x_855, 0);
 x_860 = x_855;
} else {
 lean::inc(x_858);
 lean::dec(x_855);
 x_860 = lean::box(0);
}
x_861 = lean::cnstr_get(x_858, 0);
lean::inc(x_861);
x_863 = lean::cnstr_get(x_858, 1);
lean::inc(x_863);
x_865 = lean::cnstr_get(x_858, 2);
lean::inc(x_865);
x_867 = lean::cnstr_get(x_858, 3);
lean::inc(x_867);
x_869 = lean::cnstr_get(x_858, 5);
lean::inc(x_869);
x_871 = lean::cnstr_get(x_858, 6);
lean::inc(x_871);
x_873 = lean::cnstr_get(x_858, 7);
lean::inc(x_873);
x_875 = lean::cnstr_get(x_858, 8);
lean::inc(x_875);
x_877 = lean::cnstr_get(x_858, 9);
lean::inc(x_877);
x_879 = lean::cnstr_get(x_858, 10);
lean::inc(x_879);
lean::dec(x_858);
x_882 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_882, 0, x_861);
lean::cnstr_set(x_882, 1, x_863);
lean::cnstr_set(x_882, 2, x_865);
lean::cnstr_set(x_882, 3, x_867);
lean::cnstr_set(x_882, 4, x_3);
lean::cnstr_set(x_882, 5, x_869);
lean::cnstr_set(x_882, 6, x_871);
lean::cnstr_set(x_882, 7, x_873);
lean::cnstr_set(x_882, 8, x_875);
lean::cnstr_set(x_882, 9, x_877);
lean::cnstr_set(x_882, 10, x_879);
x_883 = lean::box(0);
if (lean::is_scalar(x_860)) {
 x_884 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_884 = x_860;
}
lean::cnstr_set(x_884, 0, x_883);
lean::cnstr_set(x_884, 1, x_882);
if (lean::is_scalar(x_857)) {
 x_885 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_885 = x_857;
}
lean::cnstr_set(x_885, 0, x_884);
return x_885;
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
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; uint8 x_28; 
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
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_15, 0);
x_22 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_24 = x_15;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_15);
 x_24 = lean::box(0);
}
x_27 = l_lean_expander_binding__annotation__update;
x_28 = l_lean_parser_syntax_is__of__kind___main(x_27, x_22);
lean::dec(x_22);
if (x_28 == 0)
{
uint8 x_32; obj* x_33; obj* x_34; 
lean::dec(x_17);
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
obj* x_37; obj* x_39; obj* x_42; 
x_37 = lean::cnstr_get(x_11, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_11, 1);
lean::inc(x_39);
lean::dec(x_11);
x_42 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_8, x_1, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_37);
x_46 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_48 = x_42;
} else {
 lean::inc(x_46);
 lean::dec(x_42);
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
obj* x_50; obj* x_52; uint8 x_53; 
x_50 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_set(x_42, 0, lean::box(0));
 x_52 = x_42;
} else {
 lean::inc(x_50);
 lean::dec(x_42);
 x_52 = lean::box(0);
}
x_53 = lean::unbox(x_37);
if (x_53 == 0)
{
obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_6);
lean::dec(x_10);
x_56 = lean::cnstr_get(x_50, 0);
x_58 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_60 = x_50;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_50);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_56);
lean::cnstr_set(x_61, 1, x_58);
if (lean::is_scalar(x_52)) {
 x_62 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_62 = x_52;
}
lean::cnstr_set(x_62, 0, x_61);
return x_62;
}
else
{
obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_63 = lean::cnstr_get(x_50, 0);
x_65 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_67 = x_50;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_50);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_68 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_68 = x_10;
}
lean::cnstr_set(x_68, 0, x_6);
lean::cnstr_set(x_68, 1, x_63);
if (lean::is_scalar(x_67)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_67;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_65);
if (lean::is_scalar(x_52)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_52;
}
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
}
lbl_26:
{
obj* x_72; obj* x_73; obj* x_75; obj* x_78; 
lean::dec(x_25);
x_72 = l_lean_elaborator_mangle__ident(x_20);
x_73 = lean::cnstr_get(x_2, 4);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_73, 2);
lean::inc(x_75);
lean::inc(x_75);
x_78 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_75, x_72);
if (lean::obj_tag(x_78) == 0)
{
obj* x_82; obj* x_83; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_92; 
lean::dec(x_17);
lean::dec(x_75);
lean::dec(x_73);
x_82 = lean::box(0);
x_83 = l_lean_name_to__string___closed__1;
lean::inc(x_72);
x_85 = l_lean_name_to__string__with__sep___main(x_83, x_72);
x_86 = l_lean_parser_substring_of__string(x_85);
x_87 = lean::box(0);
x_88 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_88, 0, x_82);
lean::cnstr_set(x_88, 1, x_86);
lean::cnstr_set(x_88, 2, x_72);
lean::cnstr_set(x_88, 3, x_87);
lean::cnstr_set(x_88, 4, x_87);
x_89 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
x_90 = l_string_join___closed__1;
lean::inc(x_1);
x_92 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_89, x_90, x_1, x_2);
lean::dec(x_2);
lean::dec(x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_1);
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
obj* x_103; obj* x_106; obj* x_108; uint8 x_109; obj* x_110; obj* x_111; 
x_103 = lean::cnstr_get(x_92, 0);
lean::inc(x_103);
lean::dec(x_92);
x_106 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 x_108 = x_103;
} else {
 lean::inc(x_106);
 lean::dec(x_103);
 x_108 = lean::box(0);
}
x_109 = 0;
x_110 = lean::box(x_109);
if (lean::is_scalar(x_108)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_108;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_106);
x_11 = x_111;
goto lbl_12;
}
}
else
{
obj* x_112; obj* x_115; obj* x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_135; uint8 x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_148; obj* x_149; obj* x_151; obj* x_153; obj* x_155; obj* x_157; obj* x_159; obj* x_162; uint8 x_163; obj* x_164; obj* x_165; 
x_112 = lean::cnstr_get(x_78, 0);
lean::inc(x_112);
lean::dec(x_78);
x_115 = lean::cnstr_get(x_112, 1);
if (lean::is_exclusive(x_112)) {
 lean::cnstr_release(x_112, 0);
 x_117 = x_112;
} else {
 lean::inc(x_115);
 lean::dec(x_112);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_2, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_2, 1);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_2, 2);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_2, 3);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_73, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_73, 1);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_115, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_115, 1);
lean::inc(x_132);
lean::dec(x_115);
x_135 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_135, 0, x_130);
lean::cnstr_set(x_135, 1, x_132);
x_136 = lean::unbox(x_17);
lean::cnstr_set_scalar(x_135, sizeof(void*)*2, x_136);
x_137 = x_135;
x_138 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(x_75, x_72, x_137);
x_139 = lean::cnstr_get(x_73, 3);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_73, 4);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_73, 5);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_73, 6);
lean::inc(x_145);
lean::dec(x_73);
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
if (lean::is_scalar(x_117)) {
 x_165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_165 = x_117;
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
obj* x_13; obj* x_15; 
lean::dec(x_9);
x_13 = l_lean_elaborator_variables_elaborate___closed__1;
lean::inc(x_1);
x_15 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_13, x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_1);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_21 = x_15;
} else {
 lean::inc(x_19);
 lean::dec(x_15);
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
x_23 = lean::cnstr_get(x_15, 0);
lean::inc(x_23);
lean::dec(x_15);
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
lean::dec(x_0);
return x_49;
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
obj* x_62; obj* x_65; obj* x_67; obj* x_71; 
x_62 = lean::cnstr_get(x_55, 0);
lean::inc(x_62);
lean::dec(x_55);
x_65 = lean::cnstr_get(x_62, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_62, 1);
lean::inc(x_67);
lean::dec(x_62);
lean::inc(x_1);
x_71 = l_lean_elaborator_simple__binders__to__pexpr(x_65, x_1, x_67);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_1);
lean::dec(x_0);
x_74 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 x_76 = x_71;
} else {
 lean::inc(x_74);
 lean::dec(x_71);
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
obj* x_78; obj* x_81; obj* x_83; obj* x_86; obj* x_87; obj* x_88; 
x_78 = lean::cnstr_get(x_71, 0);
lean::inc(x_78);
lean::dec(x_71);
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 1);
lean::inc(x_83);
lean::dec(x_78);
x_86 = l_lean_elaborator_variables_elaborate___closed__2;
x_87 = lean_expr_mk_mdata(x_86, x_81);
x_88 = l_lean_elaborator_old__elab__command(x_0, x_87, x_1, x_83);
lean::dec(x_0);
return x_88;
}
}
}
}
}
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
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
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_3 = l_lean_parser_command_include_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
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
obj* l_lean_elaborator_include_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_include_elaborate(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
lean::dec(x_2);
lean::dec(x_0);
return x_13;
}
else
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
lean::dec(x_8);
if (lean::obj_tag(x_17) == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_0);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_17);
x_26 = l_lean_elaborator_module_header_elaborate___closed__1;
x_27 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_26, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
return x_27;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg), 1, 0);
return x_1;
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
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed), 8, 3);
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
obj* x_7; 
x_7 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
return x_7;
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4___boxed), 7, 1);
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4___boxed), 7, 1);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_get__leading___boxed), 6, 0);
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
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
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
lean::dec(x_3);
lean::dec(x_22);
if (lean::obj_tag(x_24) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_9);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_31 = x_24;
} else {
 lean::inc(x_29);
 lean::dec(x_24);
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
obj* x_33; obj* x_36; obj* x_38; 
x_33 = lean::cnstr_get(x_24, 0);
lean::inc(x_33);
lean::dec(x_24);
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
lean::dec(x_33);
x_0 = x_36;
x_1 = x_9;
x_3 = x_38;
goto _start;
}
}
else
{
obj* x_43; 
lean::dec(x_7);
x_43 = lean::cnstr_get(x_14, 0);
lean::inc(x_43);
lean::dec(x_14);
x_0 = x_43;
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
lean::dec(x_3);
lean::dec(x_25);
if (lean::obj_tag(x_27) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_9);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_34 = x_27;
} else {
 lean::inc(x_32);
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
obj* x_36; obj* x_39; obj* x_41; 
x_36 = lean::cnstr_get(x_27, 0);
lean::inc(x_36);
lean::dec(x_27);
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
lean::dec(x_36);
x_0 = x_39;
x_1 = x_9;
x_3 = x_41;
goto _start;
}
}
else
{
obj* x_45; obj* x_48; obj* x_52; 
x_45 = lean::cnstr_get(x_16, 0);
lean::inc(x_45);
lean::dec(x_16);
x_48 = lean::cnstr_get(x_7, 0);
lean::inc(x_48);
lean::dec(x_7);
lean::inc(x_12);
x_52 = l_lean_elaborator_command__parser__config_register__notation__parser(x_48, x_12, x_45);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_56; obj* x_57; obj* x_60; obj* x_62; 
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
lean::dec(x_52);
x_56 = l_lean_parser_command_notation_has__view;
x_57 = lean::cnstr_get(x_56, 1);
lean::inc(x_57);
lean::dec(x_56);
x_60 = lean::apply_1(x_57, x_12);
lean::inc(x_2);
x_62 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_60, x_53, x_2, x_3);
lean::dec(x_3);
lean::dec(x_60);
if (lean::obj_tag(x_62) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_9);
lean::dec(x_2);
x_67 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_69 = x_62;
} else {
 lean::inc(x_67);
 lean::dec(x_62);
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
obj* x_71; obj* x_74; obj* x_76; 
x_71 = lean::cnstr_get(x_62, 0);
lean::inc(x_71);
lean::dec(x_62);
x_74 = lean::cnstr_get(x_71, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_71, 1);
lean::inc(x_76);
lean::dec(x_71);
x_0 = x_74;
x_1 = x_9;
x_3 = x_76;
goto _start;
}
}
else
{
obj* x_81; 
lean::dec(x_12);
x_81 = lean::cnstr_get(x_52, 0);
lean::inc(x_81);
lean::dec(x_52);
x_0 = x_81;
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
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_46 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_48 = x_36;
} else {
 lean::inc(x_46);
 lean::dec(x_36);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_46, 0);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 1);
 x_51 = x_46;
} else {
 lean::inc(x_49);
 lean::dec(x_46);
 x_51 = lean::box(0);
}
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
if (lean::is_scalar(x_51)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_51;
}
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
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 4);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 6);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 7);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 8);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 9);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 10);
lean::inc(x_20);
lean::dec(x_0);
x_23 = l_lean_message__log_empty;
x_24 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_24, 0, x_2);
lean::cnstr_set(x_24, 1, x_4);
lean::cnstr_set(x_24, 2, x_6);
lean::cnstr_set(x_24, 3, x_8);
lean::cnstr_set(x_24, 4, x_10);
lean::cnstr_set(x_24, 5, x_23);
lean::cnstr_set(x_24, 6, x_12);
lean::cnstr_set(x_24, 7, x_14);
lean::cnstr_set(x_24, 8, x_16);
lean::cnstr_set(x_24, 9, x_18);
lean::cnstr_set(x_24, 10, x_20);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_24);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
}
obj* l_lean_elaborator_yield__to__outside___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_lean_elaborator_yield__to__outside(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_yield__to__outside___rarg___lambda__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_yield__to__outside___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_yield__to__outside___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_yield__to__outside___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_yield__to__outside(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
}
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
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_17 = x_5;
} else {
 lean::inc(x_15);
 lean::dec(x_5);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_7, 0);
x_20 = lean::cnstr_get(x_7, 1);
x_22 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 3);
 x_24 = x_7;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_7);
 x_24 = lean::box(0);
}
x_25 = l_lean_elaborator_postprocess__notation__spec___closed__1;
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_18);
lean::cnstr_set(x_26, 1, x_20);
lean::cnstr_set(x_26, 2, x_22);
lean::cnstr_set(x_26, 3, x_25);
if (lean::is_scalar(x_17)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_17;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_15);
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_12);
if (lean::is_scalar(x_11)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_11;
}
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
return x_1;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___lambda__1___boxed), 1, 0);
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
obj* x_2; obj* x_4; uint8 x_6; obj* x_7; uint8 x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_6 = l_option_is__some___main___rarg(x_2);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = l_option_is__some___main___rarg(x_7);
lean::dec(x_7);
if (x_6 == 0)
{
if (x_9 == 0)
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
if (x_9 == 0)
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
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___lambda__1(x_0);
lean::dec(x_0);
return x_1;
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
lean::dec(x_2);
lean::dec(x_49);
if (lean::obj_tag(x_51) == 0)
{
obj* x_54; obj* x_56; obj* x_57; 
x_54 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_56 = x_51;
} else {
 lean::inc(x_54);
 lean::dec(x_51);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_54);
return x_57;
}
else
{
obj* x_58; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_78; obj* x_79; obj* x_80; 
x_58 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_60 = x_51;
} else {
 lean::inc(x_58);
 lean::dec(x_51);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_58, 0);
x_63 = lean::cnstr_get(x_58, 1);
if (lean::is_exclusive(x_58)) {
 x_65 = x_58;
} else {
 lean::inc(x_61);
 lean::inc(x_63);
 lean::dec(x_58);
 x_65 = lean::box(0);
}
x_66 = lean::cnstr_get(x_61, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_61, 1);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_61, 2);
lean::inc(x_70);
x_72 = l_lean_elaborator_postprocess__notation__spec(x_70);
x_73 = lean::cnstr_get(x_61, 3);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_61, 4);
lean::inc(x_75);
lean::dec(x_61);
x_78 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_78, 0, x_66);
lean::cnstr_set(x_78, 1, x_68);
lean::cnstr_set(x_78, 2, x_72);
lean::cnstr_set(x_78, 3, x_73);
lean::cnstr_set(x_78, 4, x_75);
if (lean::is_scalar(x_65)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_65;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_63);
if (lean::is_scalar(x_60)) {
 x_80 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_80 = x_60;
}
lean::cnstr_set(x_80, 0, x_79);
return x_80;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_mk__notation__kind___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_elaborator_mk__notation__kind___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_mk__notation__kind(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_3; 
x_3 = l_lean_elaborator_mk__notation__kind___rarg(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_5 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
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
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; 
x_9 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_11 = x_3;
} else {
 lean::inc(x_9);
 lean::dec(x_3);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 0);
x_14 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
lean::inc(x_12);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_12);
lean::cnstr_set(x_18, 1, x_0);
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mk__notation__transformer), 3, 1);
lean::closure_set(x_20, 0, x_18);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_14, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_14, 2);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_14, 3);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_14, 4);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_14, 5);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_14, 6);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_14, 7);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_35, 1);
lean::inc(x_39);
lean::dec(x_35);
x_42 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_39, x_12, x_20);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_37);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::cnstr_get(x_14, 8);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_14, 9);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_14, 10);
lean::inc(x_48);
lean::dec(x_14);
x_51 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_51, 0, x_21);
lean::cnstr_set(x_51, 1, x_23);
lean::cnstr_set(x_51, 2, x_25);
lean::cnstr_set(x_51, 3, x_27);
lean::cnstr_set(x_51, 4, x_29);
lean::cnstr_set(x_51, 5, x_31);
lean::cnstr_set(x_51, 6, x_33);
lean::cnstr_set(x_51, 7, x_43);
lean::cnstr_set(x_51, 8, x_44);
lean::cnstr_set(x_51, 9, x_46);
lean::cnstr_set(x_51, 10, x_48);
if (lean::is_scalar(x_16)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_16;
}
lean::cnstr_set(x_52, 0, x_18);
lean::cnstr_set(x_52, 1, x_51);
if (lean::is_scalar(x_11)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_11;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
}
obj* l_lean_elaborator_register__notation__macro___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_register__notation__macro(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* x_2; obj* x_3; uint8 x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_3);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::obj_tag(x_5) == 0)
{
return x_4;
}
else
{
obj* x_6; 
x_6 = lean::cnstr_get(x_5, 0);
switch (lean::obj_tag(x_6)) {
case 2:
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_6, 0);
x_8 = lean::cnstr_get(x_7, 1);
if (lean::obj_tag(x_8) == 0)
{
return x_4;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_8, 0);
x_10 = lean::cnstr_get(x_9, 1);
switch (lean::obj_tag(x_10)) {
case 3:
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
default:
{
return x_4;
}
}
}
}
default:
{
return x_4;
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
lean::dec(x_12);
if (x_15 == 0)
{
obj* x_17; 
x_17 = lean::box(0);
x_8 = x_17;
goto lbl_9;
}
else
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_32; obj* x_35; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_7);
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_2, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 3);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_2, 4);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_1, 0);
lean::inc(x_29);
lean::dec(x_1);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
lean::dec(x_29);
x_35 = lean::box(0);
x_36 = l_lean_elaborator_notation_elaborate___closed__1;
x_37 = 1;
x_38 = l_string_join___closed__1;
x_39 = l_lean_elaborator_notation_elaborate___closed__2;
x_40 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_40, 0, x_32);
lean::cnstr_set(x_40, 1, x_36);
lean::cnstr_set(x_40, 2, x_35);
lean::cnstr_set(x_40, 3, x_38);
lean::cnstr_set(x_40, 4, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*5, x_37);
x_41 = x_40;
x_42 = lean::cnstr_get(x_2, 5);
lean::inc(x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set(x_44, 1, x_42);
x_45 = lean::cnstr_get(x_2, 6);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_2, 7);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_2, 8);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_2, 9);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_2, 10);
lean::inc(x_53);
lean::dec(x_2);
x_56 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_56, 0, x_19);
lean::cnstr_set(x_56, 1, x_21);
lean::cnstr_set(x_56, 2, x_23);
lean::cnstr_set(x_56, 3, x_25);
lean::cnstr_set(x_56, 4, x_27);
lean::cnstr_set(x_56, 5, x_44);
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
return x_59;
}
lbl_9:
{
obj* x_62; 
lean::dec(x_8);
lean::inc(x_1);
x_62 = l_lean_elaborator_notation_elaborate__aux(x_7, x_1, x_2);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_1);
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
obj* x_68; obj* x_71; obj* x_73; obj* x_77; 
x_68 = lean::cnstr_get(x_62, 0);
lean::inc(x_68);
lean::dec(x_62);
x_71 = lean::cnstr_get(x_68, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
lean::dec(x_68);
lean::inc(x_71);
x_77 = l_lean_elaborator_register__notation__macro(x_71, x_1, x_73);
if (lean::obj_tag(x_77) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_1);
lean::dec(x_71);
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
obj* x_84; obj* x_87; 
x_84 = lean::cnstr_get(x_77, 0);
lean::inc(x_84);
lean::dec(x_77);
x_87 = lean::cnstr_get(x_71, 0);
lean::inc(x_87);
lean::dec(x_71);
if (lean::obj_tag(x_87) == 0)
{
obj* x_90; obj* x_92; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_119; obj* x_120; 
x_90 = lean::cnstr_get(x_84, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_84, 1);
lean::inc(x_92);
lean::dec(x_84);
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
obj* x_122; obj* x_124; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_153; obj* x_154; obj* x_156; obj* x_158; obj* x_160; obj* x_162; obj* x_164; obj* x_167; obj* x_168; 
lean::dec(x_87);
x_122 = lean::cnstr_get(x_84, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_84, 1);
lean::inc(x_124);
lean::dec(x_84);
x_127 = lean::cnstr_get(x_124, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_124, 1);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_124, 2);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_124, 3);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_124, 4);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_135, 0);
lean::inc(x_137);
x_139 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_139, 0, x_122);
lean::cnstr_set(x_139, 1, x_137);
x_140 = lean::cnstr_get(x_135, 1);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_135, 2);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_135, 3);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_135, 4);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_135, 5);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_135, 6);
lean::inc(x_150);
lean::dec(x_135);
x_153 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_153, 0, x_139);
lean::cnstr_set(x_153, 1, x_140);
lean::cnstr_set(x_153, 2, x_142);
lean::cnstr_set(x_153, 3, x_144);
lean::cnstr_set(x_153, 4, x_146);
lean::cnstr_set(x_153, 5, x_148);
lean::cnstr_set(x_153, 6, x_150);
x_154 = lean::cnstr_get(x_124, 5);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_124, 6);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_124, 7);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_124, 8);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_124, 9);
lean::inc(x_162);
x_164 = lean::cnstr_get(x_124, 10);
lean::inc(x_164);
lean::dec(x_124);
x_167 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_167, 0, x_127);
lean::cnstr_set(x_167, 1, x_129);
lean::cnstr_set(x_167, 2, x_131);
lean::cnstr_set(x_167, 3, x_133);
lean::cnstr_set(x_167, 4, x_153);
lean::cnstr_set(x_167, 5, x_154);
lean::cnstr_set(x_167, 6, x_156);
lean::cnstr_set(x_167, 7, x_158);
lean::cnstr_set(x_167, 8, x_160);
lean::cnstr_set(x_167, 9, x_162);
lean::cnstr_set(x_167, 10, x_164);
x_168 = l_lean_elaborator_update__parser__config(x_1, x_167);
return x_168;
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
lean::dec(x_0);
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
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_18; 
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
lean::inc(x_15);
x_18 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_15, x_12);
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
x_29 = lean::cnstr_get(x_13, 0);
lean::inc(x_29);
lean::inc(x_12);
x_32 = level_mk_param(x_12);
x_33 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_15, x_12, x_32);
x_34 = lean::cnstr_get(x_13, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_13, 3);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_13, 4);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_13, 5);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_13, 6);
lean::inc(x_42);
lean::dec(x_13);
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
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_18);
x_66 = l_lean_name_to__string___closed__1;
x_67 = l_lean_name_to__string__with__sep___main(x_66, x_12);
x_68 = l_lean_elaborator_universe_elaborate___closed__1;
x_69 = lean::string_append(x_68, x_67);
lean::dec(x_67);
x_71 = l_lean_elaborator_universe_elaborate___closed__2;
x_72 = lean::string_append(x_69, x_71);
x_73 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_72, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
return x_73;
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
lean::dec(x_2);
lean::dec(x_15);
if (lean::obj_tag(x_27) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_13);
lean::dec(x_1);
lean::dec(x_11);
x_33 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_35 = x_27;
} else {
 lean::inc(x_33);
 lean::dec(x_27);
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
obj* x_37; obj* x_40; obj* x_42; obj* x_45; 
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
lean::dec(x_27);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
x_45 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_11, x_1, x_42);
if (lean::obj_tag(x_45) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_13);
lean::dec(x_40);
x_48 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 x_50 = x_45;
} else {
 lean::inc(x_48);
 lean::dec(x_45);
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
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_52 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 x_54 = x_45;
} else {
 lean::inc(x_52);
 lean::dec(x_45);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_52, 0);
x_57 = lean::cnstr_get(x_52, 1);
if (lean::is_exclusive(x_52)) {
 x_59 = x_52;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::dec(x_52);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_60 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_60 = x_13;
}
lean::cnstr_set(x_60, 0, x_40);
lean::cnstr_set(x_60, 1, x_55);
if (lean::is_scalar(x_59)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_59;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_57);
if (lean::is_scalar(x_54)) {
 x_62 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_62 = x_54;
}
lean::cnstr_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
obj* x_63; 
x_63 = lean::cnstr_get(x_9, 1);
lean::inc(x_63);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_7);
x_66 = lean::cnstr_get(x_0, 1);
lean::inc(x_66);
lean::dec(x_0);
x_69 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_release(x_9, 1);
 x_71 = x_9;
} else {
 lean::inc(x_69);
 lean::dec(x_9);
 x_71 = lean::box(0);
}
x_72 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_66, x_1, x_2);
if (lean::obj_tag(x_72) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_71);
lean::dec(x_69);
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
obj* x_79; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_79 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_81 = x_72;
} else {
 lean::inc(x_79);
 lean::dec(x_72);
 x_81 = lean::box(0);
}
x_82 = lean::cnstr_get(x_79, 0);
x_84 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 x_86 = x_79;
} else {
 lean::inc(x_82);
 lean::inc(x_84);
 lean::dec(x_79);
 x_86 = lean::box(0);
}
x_87 = lean::box(0);
x_88 = lean_expr_mk_const(x_69, x_87);
if (lean::is_scalar(x_71)) {
 x_89 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_89 = x_71;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_82);
if (lean::is_scalar(x_86)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_86;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_84);
if (lean::is_scalar(x_81)) {
 x_91 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_91 = x_81;
}
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
}
else
{
obj* x_93; obj* x_94; obj* x_97; obj* x_98; obj* x_100; 
lean::dec(x_9);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_93 = x_63;
} else {
 lean::dec(x_63);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_0, 1);
lean::inc(x_94);
lean::dec(x_0);
x_97 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_97, 0, x_7);
x_98 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
lean::inc(x_1);
x_100 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_97, x_98, x_1, x_2);
lean::dec(x_2);
lean::dec(x_97);
if (lean::obj_tag(x_100) == 0)
{
obj* x_106; obj* x_108; obj* x_109; 
lean::dec(x_1);
lean::dec(x_93);
lean::dec(x_94);
x_106 = lean::cnstr_get(x_100, 0);
if (lean::is_exclusive(x_100)) {
 x_108 = x_100;
} else {
 lean::inc(x_106);
 lean::dec(x_100);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_106);
return x_109;
}
else
{
obj* x_110; obj* x_113; obj* x_115; obj* x_118; 
x_110 = lean::cnstr_get(x_100, 0);
lean::inc(x_110);
lean::dec(x_100);
x_113 = lean::cnstr_get(x_110, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_110, 1);
lean::inc(x_115);
lean::dec(x_110);
x_118 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_94, x_1, x_115);
if (lean::obj_tag(x_118) == 0)
{
obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_113);
lean::dec(x_93);
x_121 = lean::cnstr_get(x_118, 0);
if (lean::is_exclusive(x_118)) {
 x_123 = x_118;
} else {
 lean::inc(x_121);
 lean::dec(x_118);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_121);
return x_124;
}
else
{
obj* x_125; obj* x_127; obj* x_128; obj* x_130; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_125 = lean::cnstr_get(x_118, 0);
if (lean::is_exclusive(x_118)) {
 x_127 = x_118;
} else {
 lean::inc(x_125);
 lean::dec(x_118);
 x_127 = lean::box(0);
}
x_128 = lean::cnstr_get(x_125, 0);
x_130 = lean::cnstr_get(x_125, 1);
if (lean::is_exclusive(x_125)) {
 x_132 = x_125;
} else {
 lean::inc(x_128);
 lean::inc(x_130);
 lean::dec(x_125);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_133 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_133 = x_93;
}
lean::cnstr_set(x_133, 0, x_113);
lean::cnstr_set(x_133, 1, x_128);
if (lean::is_scalar(x_132)) {
 x_134 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_134 = x_132;
}
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_130);
if (lean::is_scalar(x_127)) {
 x_135 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_135 = x_127;
}
lean::cnstr_set(x_135, 0, x_134);
return x_135;
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
obj* x_40; obj* x_43; obj* x_45; obj* x_48; uint8 x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
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
lean::dec(x_48);
x_53 = l_lean_elaborator_attribute_elaborate___closed__1;
x_54 = l_lean_elaborator_attribute_elaborate___closed__2;
x_55 = l_lean_kvmap_set__bool(x_53, x_54, x_51);
x_56 = l_lean_elaborator_mk__eqns___closed__1;
x_57 = l_lean_expr_mk__capp(x_56, x_43);
x_58 = lean_expr_mk_app(x_23, x_57);
x_59 = lean_expr_mk_mdata(x_55, x_58);
x_60 = l_lean_elaborator_old__elab__command(x_0, x_59, x_1, x_45);
lean::dec(x_0);
return x_60;
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
lean::dec(x_0);
return x_30;
}
}
}
obj* l_lean_elaborator_open_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_3 = l_lean_parser_command_open_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
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
obj* l_lean_elaborator_open_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_open_elaborate(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* x_3; 
x_3 = l_lean_elaborator_get__namespace___rarg(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_5 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
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
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_9 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_11 = x_3;
} else {
 lean::inc(x_9);
 lean::dec(x_3);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 0);
x_14 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = l_lean_parser_command_export_has__view;
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
lean::dec(x_17);
x_21 = lean::apply_1(x_18, x_0);
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_14, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_14, 2);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_14, 3);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_21, 1);
lean::inc(x_30);
lean::dec(x_21);
x_33 = l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(x_12, x_30);
x_34 = l_list_append___rarg(x_28, x_33);
x_35 = lean::cnstr_get(x_14, 4);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_14, 5);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_14, 6);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_14, 7);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_14, 8);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_14, 9);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_14, 10);
lean::inc(x_47);
lean::dec(x_14);
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
if (lean::is_scalar(x_16)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_16;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_50);
if (lean::is_scalar(x_11)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_11;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
}
obj* l_lean_elaborator_export_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_export_elaborate(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* l_lean_elaborator_init__quot_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_init__quot_elaborate(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_elaborator_set__option_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
x_3 = l_lean_parser_command_set__option_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 2);
lean::inc(x_8);
switch (lean::obj_tag(x_8)) {
case 0:
{
obj* x_10; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_17; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_55; uint8 x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_10);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
x_17 = lean::cnstr_get(x_14, 2);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_2, 4);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_20, 6);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_2, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_2, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_2, 2);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_2, 3);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_20, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_20, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_20, 2);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_20, 3);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_20, 4);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_20, 5);
lean::inc(x_42);
lean::dec(x_20);
x_45 = lean::cnstr_get(x_2, 5);
lean::inc(x_45);
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
x_58 = 1;
x_59 = l_lean_kvmap_set__bool(x_22, x_17, x_58);
x_60 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_60, 0, x_32);
lean::cnstr_set(x_60, 1, x_34);
lean::cnstr_set(x_60, 2, x_36);
lean::cnstr_set(x_60, 3, x_38);
lean::cnstr_set(x_60, 4, x_40);
lean::cnstr_set(x_60, 5, x_42);
lean::cnstr_set(x_60, 6, x_59);
x_61 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_61, 0, x_24);
lean::cnstr_set(x_61, 1, x_26);
lean::cnstr_set(x_61, 2, x_28);
lean::cnstr_set(x_61, 3, x_30);
lean::cnstr_set(x_61, 4, x_60);
lean::cnstr_set(x_61, 5, x_45);
lean::cnstr_set(x_61, 6, x_47);
lean::cnstr_set(x_61, 7, x_49);
lean::cnstr_set(x_61, 8, x_51);
lean::cnstr_set(x_61, 9, x_53);
lean::cnstr_set(x_61, 10, x_55);
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
obj* x_66; obj* x_69; obj* x_72; obj* x_74; obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_88; obj* x_90; obj* x_92; obj* x_94; obj* x_97; obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_107; uint8 x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_10);
x_66 = lean::cnstr_get(x_7, 1);
lean::inc(x_66);
lean::dec(x_7);
x_69 = lean::cnstr_get(x_66, 2);
lean::inc(x_69);
lean::dec(x_66);
x_72 = lean::cnstr_get(x_2, 4);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_72, 6);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_2, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_2, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_2, 2);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_2, 3);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_72, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_72, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_72, 2);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_72, 3);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_72, 4);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_72, 5);
lean::inc(x_94);
lean::dec(x_72);
x_97 = lean::cnstr_get(x_2, 5);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_2, 6);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_2, 7);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_2, 8);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_2, 9);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_2, 10);
lean::inc(x_107);
lean::dec(x_2);
x_110 = 0;
x_111 = l_lean_kvmap_set__bool(x_74, x_69, x_110);
x_112 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_112, 0, x_84);
lean::cnstr_set(x_112, 1, x_86);
lean::cnstr_set(x_112, 2, x_88);
lean::cnstr_set(x_112, 3, x_90);
lean::cnstr_set(x_112, 4, x_92);
lean::cnstr_set(x_112, 5, x_94);
lean::cnstr_set(x_112, 6, x_111);
x_113 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_113, 0, x_76);
lean::cnstr_set(x_113, 1, x_78);
lean::cnstr_set(x_113, 2, x_80);
lean::cnstr_set(x_113, 3, x_82);
lean::cnstr_set(x_113, 4, x_112);
lean::cnstr_set(x_113, 5, x_97);
lean::cnstr_set(x_113, 6, x_99);
lean::cnstr_set(x_113, 7, x_101);
lean::cnstr_set(x_113, 8, x_103);
lean::cnstr_set(x_113, 9, x_105);
lean::cnstr_set(x_113, 10, x_107);
x_114 = lean::box(0);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_113);
x_116 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_116, 0, x_115);
return x_116;
}
}
case 1:
{
obj* x_117; obj* x_120; obj* x_123; obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_161; obj* x_164; 
x_117 = lean::cnstr_get(x_7, 1);
lean::inc(x_117);
lean::dec(x_7);
x_120 = lean::cnstr_get(x_117, 2);
lean::inc(x_120);
lean::dec(x_117);
x_123 = lean::cnstr_get(x_2, 4);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_123, 6);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_2, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_2, 1);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_2, 2);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_2, 3);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_123, 0);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_123, 1);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_123, 2);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_123, 3);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_123, 4);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_123, 5);
lean::inc(x_145);
lean::dec(x_123);
x_148 = lean::cnstr_get(x_2, 5);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_2, 6);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_2, 7);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_2, 8);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_2, 9);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_2, 10);
lean::inc(x_158);
lean::dec(x_2);
x_161 = lean::cnstr_get(x_8, 0);
lean::inc(x_161);
lean::dec(x_8);
x_164 = l_lean_parser_string__lit_view_value(x_161);
if (lean::obj_tag(x_164) == 0)
{
obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; 
lean::dec(x_120);
x_166 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_166, 0, x_135);
lean::cnstr_set(x_166, 1, x_137);
lean::cnstr_set(x_166, 2, x_139);
lean::cnstr_set(x_166, 3, x_141);
lean::cnstr_set(x_166, 4, x_143);
lean::cnstr_set(x_166, 5, x_145);
lean::cnstr_set(x_166, 6, x_125);
x_167 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_167, 0, x_127);
lean::cnstr_set(x_167, 1, x_129);
lean::cnstr_set(x_167, 2, x_131);
lean::cnstr_set(x_167, 3, x_133);
lean::cnstr_set(x_167, 4, x_166);
lean::cnstr_set(x_167, 5, x_148);
lean::cnstr_set(x_167, 6, x_150);
lean::cnstr_set(x_167, 7, x_152);
lean::cnstr_set(x_167, 8, x_154);
lean::cnstr_set(x_167, 9, x_156);
lean::cnstr_set(x_167, 10, x_158);
x_168 = lean::box(0);
x_169 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_169, 0, x_168);
lean::cnstr_set(x_169, 1, x_167);
x_170 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_170, 0, x_169);
return x_170;
}
else
{
obj* x_171; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_171 = lean::cnstr_get(x_164, 0);
lean::inc(x_171);
lean::dec(x_164);
x_174 = l_lean_kvmap_set__string(x_125, x_120, x_171);
x_175 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_175, 0, x_135);
lean::cnstr_set(x_175, 1, x_137);
lean::cnstr_set(x_175, 2, x_139);
lean::cnstr_set(x_175, 3, x_141);
lean::cnstr_set(x_175, 4, x_143);
lean::cnstr_set(x_175, 5, x_145);
lean::cnstr_set(x_175, 6, x_174);
x_176 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_176, 0, x_127);
lean::cnstr_set(x_176, 1, x_129);
lean::cnstr_set(x_176, 2, x_131);
lean::cnstr_set(x_176, 3, x_133);
lean::cnstr_set(x_176, 4, x_175);
lean::cnstr_set(x_176, 5, x_148);
lean::cnstr_set(x_176, 6, x_150);
lean::cnstr_set(x_176, 7, x_152);
lean::cnstr_set(x_176, 8, x_154);
lean::cnstr_set(x_176, 9, x_156);
lean::cnstr_set(x_176, 10, x_158);
x_177 = lean::box(0);
x_178 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_176);
x_179 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_179, 0, x_178);
return x_179;
}
}
default:
{
obj* x_180; obj* x_183; obj* x_186; obj* x_188; obj* x_190; obj* x_192; obj* x_194; obj* x_196; obj* x_198; obj* x_200; obj* x_202; obj* x_204; obj* x_206; obj* x_208; obj* x_211; obj* x_213; obj* x_215; obj* x_217; obj* x_219; obj* x_221; obj* x_224; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; 
x_180 = lean::cnstr_get(x_7, 1);
lean::inc(x_180);
lean::dec(x_7);
x_183 = lean::cnstr_get(x_180, 2);
lean::inc(x_183);
lean::dec(x_180);
x_186 = lean::cnstr_get(x_2, 4);
lean::inc(x_186);
x_188 = lean::cnstr_get(x_186, 6);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_2, 0);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_2, 1);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_2, 2);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_2, 3);
lean::inc(x_196);
x_198 = lean::cnstr_get(x_186, 0);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_186, 1);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_186, 2);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_186, 3);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_186, 4);
lean::inc(x_206);
x_208 = lean::cnstr_get(x_186, 5);
lean::inc(x_208);
lean::dec(x_186);
x_211 = lean::cnstr_get(x_2, 5);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_2, 6);
lean::inc(x_213);
x_215 = lean::cnstr_get(x_2, 7);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_2, 8);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_2, 9);
lean::inc(x_219);
x_221 = lean::cnstr_get(x_2, 10);
lean::inc(x_221);
lean::dec(x_2);
x_224 = lean::cnstr_get(x_8, 0);
lean::inc(x_224);
lean::dec(x_8);
x_227 = l_lean_parser_number_view_to__nat___main(x_224);
x_228 = l_lean_kvmap_set__nat(x_188, x_183, x_227);
x_229 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_229, 0, x_198);
lean::cnstr_set(x_229, 1, x_200);
lean::cnstr_set(x_229, 2, x_202);
lean::cnstr_set(x_229, 3, x_204);
lean::cnstr_set(x_229, 4, x_206);
lean::cnstr_set(x_229, 5, x_208);
lean::cnstr_set(x_229, 6, x_228);
x_230 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_230, 0, x_190);
lean::cnstr_set(x_230, 1, x_192);
lean::cnstr_set(x_230, 2, x_194);
lean::cnstr_set(x_230, 3, x_196);
lean::cnstr_set(x_230, 4, x_229);
lean::cnstr_set(x_230, 5, x_211);
lean::cnstr_set(x_230, 6, x_213);
lean::cnstr_set(x_230, 7, x_215);
lean::cnstr_set(x_230, 8, x_217);
lean::cnstr_set(x_230, 9, x_219);
lean::cnstr_set(x_230, 10, x_221);
x_231 = lean::box(0);
x_232 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_232, 0, x_231);
lean::cnstr_set(x_232, 1, x_230);
x_233 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_233, 0, x_232);
return x_233;
}
}
}
}
obj* l_lean_elaborator_set__option_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_set__option_elaborate(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
lean::dec(x_6);
x_14 = l_lean_parser_syntax_get__pos(x_0);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_option_get__or__else___main___rarg(x_14, x_15);
lean::dec(x_14);
x_18 = l_lean_file__map_to__position(x_11, x_16);
x_19 = lean::box(0);
x_20 = 2;
x_21 = l_string_join___closed__1;
x_22 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_22, 0, x_9);
lean::cnstr_set(x_22, 1, x_18);
lean::cnstr_set(x_22, 2, x_19);
lean::cnstr_set(x_22, 3, x_21);
lean::cnstr_set(x_22, 4, x_1);
lean::cnstr_set_scalar(x_22, sizeof(void*)*5, x_20);
x_23 = x_22;
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed), 6, 0);
return x_1;
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
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
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
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_with__current__command___rarg___boxed), 6, 5);
lean::closure_set(x_18, 0, x_10);
lean::closure_set(x_18, 1, x_15);
lean::closure_set(x_18, 2, x_1);
lean::closure_set(x_18, 3, x_2);
lean::closure_set(x_18, 4, x_3);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___lambda__1), 4, 3);
lean::closure_set(x_19, 0, x_12);
lean::closure_set(x_19, 1, x_1);
lean::closure_set(x_19, 2, x_2);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
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
obj* l_lean_elaborator_no__kind_elaborate___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; 
x_6 = l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1;
x_7 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_1, x_6, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(x_14, x_2, x_3, x_4);
x_18 = lean::apply_1(x_17, x_5);
return x_18;
}
}
}
obj* l_lean_elaborator_no__kind_elaborate___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = l_lean_parser_syntax_as__node___main(x_3);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_no__kind_elaborate___lambda__1___boxed), 6, 5);
lean::closure_set(x_10, 0, x_9);
lean::closure_set(x_10, 1, x_3);
lean::closure_set(x_10, 2, x_0);
lean::closure_set(x_10, 3, x_1);
lean::closure_set(x_10, 4, x_5);
return x_10;
}
}
obj* l_lean_elaborator_no__kind_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_no__kind_elaborate___lambda__2), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_no__kind_elaborate___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_elaborator_no__kind_elaborate___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__2(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = l_lean_elaborator_commands_elaborate___main(x_0, x_1, x_2, x_4);
return x_7;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__3(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___rarg___boxed), 2, 1);
lean::closure_set(x_7, 0, x_4);
x_8 = lean::box(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__2___boxed), 4, 3);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_1);
lean::closure_set(x_9, 2, x_2);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_7);
lean::closure_set(x_11, 1, x_10);
return x_11;
}
}
obj* _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__1___boxed), 1, 0);
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
obj* l_lean_elaborator_commands_elaborate___main___lambda__4(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
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
lean::inc(x_4);
x_10 = l_lean_parser_syntax_as__node___main(x_4);
x_11 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1;
x_12 = l_option_map___rarg(x_11, x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_4);
lean::dec(x_8);
x_15 = lean::box(0);
lean::inc(x_1);
lean::inc(x_0);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1), 5, 4);
lean::closure_set(x_18, 0, x_15);
lean::closure_set(x_18, 1, x_0);
lean::closure_set(x_18, 2, x_1);
lean::closure_set(x_18, 3, x_6);
x_19 = lean::box(x_2);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 4, 3);
lean::closure_set(x_20, 0, x_19);
lean::closure_set(x_20, 1, x_0);
lean::closure_set(x_20, 2, x_1);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_21, 0, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_22, 0, x_18);
lean::closure_set(x_22, 1, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_26; uint8 x_27; 
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
lean::dec(x_12);
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
obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_4);
lean::dec(x_8);
x_33 = lean::box(0);
lean::inc(x_1);
lean::inc(x_0);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1), 5, 4);
lean::closure_set(x_36, 0, x_33);
lean::closure_set(x_36, 1, x_0);
lean::closure_set(x_36, 2, x_1);
lean::closure_set(x_36, 3, x_6);
x_37 = lean::box(x_2);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 4, 3);
lean::closure_set(x_38, 0, x_37);
lean::closure_set(x_38, 1, x_0);
lean::closure_set(x_38, 2, x_1);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_39, 0, x_38);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_40, 0, x_36);
lean::closure_set(x_40, 1, x_39);
return x_40;
}
else
{
if (x_2 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_44 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_8;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_6);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_47, 0, x_46);
return x_47;
}
else
{
obj* x_49; obj* x_50; 
lean::dec(x_8);
x_49 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4;
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_50, 0, x_4);
lean::closure_set(x_50, 1, x_49);
lean::closure_set(x_50, 2, x_0);
lean::closure_set(x_50, 3, x_1);
lean::closure_set(x_50, 4, x_6);
return x_50;
}
}
}
else
{
lean::dec(x_23);
if (x_2 == 0)
{
obj* x_53; obj* x_54; 
lean::dec(x_8);
x_53 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5;
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_54, 0, x_4);
lean::closure_set(x_54, 1, x_53);
lean::closure_set(x_54, 2, x_0);
lean::closure_set(x_54, 3, x_1);
lean::closure_set(x_54, 4, x_6);
return x_54;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_58 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_8;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_6);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_61, 0, x_60);
return x_61;
}
}
}
}
}
obj* l_lean_elaborator_commands_elaborate___main(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::box(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__4___boxed), 4, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_2);
lean::closure_set(x_6, 2, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_commands_elaborate___main___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_lean_elaborator_commands_elaborate___main___lambda__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_lean_elaborator_commands_elaborate___main___lambda__3(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l_lean_elaborator_commands_elaborate___main___lambda__4(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l_lean_elaborator_commands_elaborate___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_lean_elaborator_commands_elaborate___main(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_elaborator_commands_elaborate(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_commands_elaborate___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_commands_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_lean_elaborator_commands_elaborate(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_elaborator_end__scope___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
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
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
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
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
x_19 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_22, 0, x_21);
return x_22;
}
else
{
obj* x_24; 
lean::dec(x_9);
x_24 = lean::box(0);
x_10 = x_24;
goto lbl_11;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_27; 
lean::dec(x_15);
lean::dec(x_9);
x_27 = lean::box(0);
x_10 = x_27;
goto lbl_11;
}
else
{
obj* x_28; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_15, 0);
lean::inc(x_28);
lean::dec(x_15);
x_31 = lean::cnstr_get(x_1, 0);
x_32 = lean_name_dec_eq(x_28, x_31);
lean::dec(x_28);
if (x_32 == 0)
{
obj* x_35; 
lean::dec(x_9);
x_35 = lean::box(0);
x_10 = x_35;
goto lbl_11;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
x_39 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_9;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_7);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_42, 0, x_41);
return x_42;
}
}
}
lbl_11:
{
obj* x_44; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_10);
x_44 = l_lean_parser_command_end_has__view;
x_45 = lean::cnstr_get(x_44, 1);
lean::inc(x_45);
lean::dec(x_44);
x_48 = lean::apply_1(x_45, x_5);
x_49 = l_lean_elaborator_end__scope___lambda__2___closed__1;
x_50 = lean::string_append(x_49, x_0);
x_51 = l_lean_elaborator_end__scope___lambda__2___closed__2;
x_52 = lean::string_append(x_50, x_51);
x_53 = lean::box(0);
x_54 = l_option_get__or__else___main___rarg(x_1, x_53);
x_55 = l_lean_name_to__string___closed__1;
x_56 = l_lean_name_to__string__with__sep___main(x_55, x_54);
x_57 = lean::string_append(x_52, x_56);
lean::dec(x_56);
x_59 = l_char_has__repr___closed__1;
x_60 = lean::string_append(x_57, x_59);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_61, 0, x_48);
lean::closure_set(x_61, 1, x_60);
lean::closure_set(x_61, 2, x_2);
lean::closure_set(x_61, 3, x_3);
lean::closure_set(x_61, 4, x_7);
return x_61;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_elaborator_end__scope___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_13 = x_0;
} else {
 lean::inc(x_11);
 lean::dec(x_0);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_22, 0, x_19);
x_23 = l_lean_elaborator_end__scope___lambda__3___closed__1;
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_24, 0, x_22);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__2___boxed), 5, 4);
lean::closure_set(x_25, 0, x_1);
lean::closure_set(x_25, 1, x_2);
lean::closure_set(x_25, 2, x_3);
lean::closure_set(x_25, 3, x_4);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_26, 0, x_25);
x_27 = l_coroutine_bind___main___rarg(x_24, x_26, x_5);
return x_27;
}
}
}
obj* l_lean_elaborator_end__scope(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_3);
x_6 = l_lean_elaborator_update__parser__config(x_3, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__3), 6, 5);
lean::closure_set(x_7, 0, x_6);
lean::closure_set(x_7, 1, x_0);
lean::closure_set(x_7, 2, x_1);
lean::closure_set(x_7, 3, x_2);
lean::closure_set(x_7, 4, x_3);
return x_7;
}
}
obj* l_lean_elaborator_end__scope___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_elaborator_end__scope___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
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
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = 1;
x_5 = l_lean_elaborator_commands_elaborate___main(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_2 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
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
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_30, 0, x_29);
return x_30;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 4);
lean::inc(x_5);
x_7 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___closed__1;
x_8 = l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg(x_7, x_1, x_2, x_3, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__2), 2, 1);
lean::closure_set(x_9, 0, x_5);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = l_coroutine_bind___main___rarg(x_8, x_10, x_4);
return x_11;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3), 5, 4);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
lean::closure_set(x_4, 2, x_0);
lean::closure_set(x_4, 3, x_1);
return x_4;
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
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
lean::inc(x_1);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3), 5, 4);
lean::closure_set(x_11, 0, x_5);
lean::closure_set(x_11, 1, x_8);
lean::closure_set(x_11, 2, x_0);
lean::closure_set(x_11, 3, x_1);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_section_elaborate___lambda__1), 4, 3);
lean::closure_set(x_12, 0, x_3);
lean::closure_set(x_12, 1, x_0);
lean::closure_set(x_12, 2, x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_13);
return x_14;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_elaborator_section_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_lean_elaborator_section_elaborate___closed__1;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_5, 0, x_3);
lean::closure_set(x_5, 1, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_section_elaborate___lambda__2), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_5);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_11 = x_0;
} else {
 lean::inc(x_9);
 lean::dec(x_0);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_17; obj* x_19; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_43; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_70; uint8 x_71; obj* x_72; obj* x_73; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
lean::dec(x_14);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_19, 2);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_19, 3);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_19, 4);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_30, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_30, 2);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_30, 3);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 1);
lean::inc(x_40);
lean::dec(x_1);
x_43 = lean::cnstr_get(x_40, 2);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_lean_name_append___main(x_17, x_43);
lean::dec(x_17);
x_48 = lean::cnstr_get(x_30, 4);
lean::inc(x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set(x_50, 1, x_48);
x_51 = lean::cnstr_get(x_30, 5);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_30, 6);
lean::inc(x_53);
lean::dec(x_30);
x_56 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_56, 0, x_32);
lean::cnstr_set(x_56, 1, x_34);
lean::cnstr_set(x_56, 2, x_36);
lean::cnstr_set(x_56, 3, x_38);
lean::cnstr_set(x_56, 4, x_50);
lean::cnstr_set(x_56, 5, x_51);
lean::cnstr_set(x_56, 6, x_53);
x_57 = lean::cnstr_get(x_19, 5);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_19, 6);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_19, 7);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_19, 8);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_19, 9);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_19, 10);
lean::inc(x_67);
lean::dec(x_19);
x_70 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_70, 0, x_22);
lean::cnstr_set(x_70, 1, x_24);
lean::cnstr_set(x_70, 2, x_26);
lean::cnstr_set(x_70, 3, x_28);
lean::cnstr_set(x_70, 4, x_56);
lean::cnstr_set(x_70, 5, x_57);
lean::cnstr_set(x_70, 6, x_59);
lean::cnstr_set(x_70, 7, x_61);
lean::cnstr_set(x_70, 8, x_63);
lean::cnstr_set(x_70, 9, x_65);
lean::cnstr_set(x_70, 10, x_67);
x_71 = 1;
x_72 = l_lean_elaborator_commands_elaborate___main(x_71, x_2, x_3, x_70);
x_73 = lean::apply_1(x_72, x_4);
return x_73;
}
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_lean_elaborator_get__namespace___rarg(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__1), 5, 4);
lean::closure_set(x_6, 0, x_5);
lean::closure_set(x_6, 1, x_0);
lean::closure_set(x_6, 2, x_2);
lean::closure_set(x_6, 3, x_3);
return x_6;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 4);
lean::inc(x_5);
x_7 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___closed__1;
x_8 = l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg(x_7, x_1, x_2, x_3, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__2), 2, 1);
lean::closure_set(x_9, 0, x_5);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = l_coroutine_bind___main___rarg(x_8, x_10, x_4);
return x_11;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2___boxed), 5, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__3), 5, 4);
lean::closure_set(x_5, 0, x_3);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_1);
lean::closure_set(x_5, 3, x_2);
return x_5;
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
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_elaborator_namespace_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_lean_elaborator_namespace_elaborate___closed__1;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_5, 0, x_3);
lean::closure_set(x_5, 1, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_namespace_elaborate___lambda__2), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_5);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
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
x_16 = l_lean_name_quick__lt(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__3), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__5), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__7), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__9), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__13), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__15), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__17___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__19___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__21), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__23(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_init__quot_elaborate___closed__1;
x_8 = l_lean_elaborator_old__elab__command(x_2, x_7, x_0, x_4);
lean::dec(x_2);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_10, 0, x_8);
return x_10;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__23), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_0 = l_lean_parser_module_header;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2___boxed), 3, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = l_lean_parser_command_notation;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4___boxed), 3, 0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_lean_parser_command_reserve__notation;
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6___boxed), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_lean_parser_command_universe;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8___boxed), 3, 0);
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
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10___boxed), 3, 0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_lean_parser_command_include;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12___boxed), 3, 0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_lean_parser_command_declaration;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14___boxed), 3, 0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_command_attribute;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16___boxed), 3, 0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_lean_parser_command_open;
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18___boxed), 3, 0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_lean_parser_command_export;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20___boxed), 3, 0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_lean_parser_command_check;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22___boxed), 3, 0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_lean_parser_command_init__quot;
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24___boxed), 3, 0);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_lean_parser_command_set__option;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26___boxed), 3, 0);
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
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__17___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__17(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__19___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__19(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
uint8 l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean_name_dec_eq(x_0, x_3);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(x_0, x_4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; obj* x_3; 
x_2 = 0;
x_3 = lean::box(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_6, 2);
x_8 = lean_name_dec_eq(x_7, x_0);
if (x_8 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
uint8 x_10; obj* x_11; 
x_10 = 1;
x_11 = lean::box(x_10);
return x_11;
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
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_0, 4);
x_5 = lean::cnstr_get(x_4, 4);
x_6 = l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(x_1, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_4, 5);
x_8 = l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(x_1, x_7);
x_9 = lean::unbox(x_8);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
}
obj* l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_is__open__namespace___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_elaborator_is__open__namespace___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
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
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; obj* x_3; 
x_2 = 0;
x_3 = lean::box(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_4, 2);
x_7 = lean_name_dec_eq(x_0, x_6);
if (x_7 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
uint8 x_9; obj* x_10; 
x_9 = 1;
x_10 = lean::box(x_9);
return x_10;
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
obj* x_4; obj* x_7; obj* x_10; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_4, 2);
lean::inc(x_7);
lean::dec(x_4);
x_10 = l_lean_name_append___main(x_7, x_0);
lean::dec(x_7);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_10);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; uint8 x_21; 
x_13 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_15 = x_2;
} else {
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 2);
lean::inc(x_18);
lean::dec(x_16);
x_21 = lean_name_dec_eq(x_0, x_18);
lean::dec(x_18);
if (x_21 == 0)
{
obj* x_23; obj* x_26; uint8 x_28; 
x_23 = lean::cnstr_get(x_13, 2);
lean::inc(x_23);
lean::dec(x_13);
x_26 = l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(x_0, x_23);
lean::dec(x_23);
x_28 = lean::unbox(x_26);
if (x_28 == 0)
{
obj* x_32; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_15);
x_32 = lean::box(0);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_39; obj* x_41; 
x_33 = lean::cnstr_get(x_1, 0);
lean::inc(x_33);
lean::dec(x_1);
x_36 = lean::cnstr_get(x_33, 2);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_lean_name_append___main(x_36, x_0);
lean::dec(x_36);
if (lean::is_scalar(x_15)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_15;
}
lean::cnstr_set(x_41, 0, x_39);
return x_41;
}
}
else
{
obj* x_43; obj* x_46; obj* x_49; obj* x_51; 
lean::dec(x_13);
x_43 = lean::cnstr_get(x_1, 0);
lean::inc(x_43);
lean::dec(x_1);
x_46 = lean::cnstr_get(x_43, 2);
lean::inc(x_46);
lean::dec(x_43);
x_49 = l_lean_name_append___main(x_46, x_0);
lean::dec(x_46);
if (lean::is_scalar(x_15)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_15;
}
lean::cnstr_set(x_51, 0, x_49);
return x_51;
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; uint8 x_14; 
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
x_13 = l_lean_name_append___main(x_5, x_0);
x_14 = lean_environment_contains(x_10, x_13);
if (x_14 == 0)
{
lean::dec(x_9);
lean::dec(x_5);
x_2 = x_7;
goto _start;
}
else
{
obj* x_18; obj* x_19; 
x_18 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_9;
}
lean::cnstr_set(x_19, 0, x_5);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
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
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; uint8 x_9; 
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
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = l_lean_elaborator_is__open__namespace___main(x_0, x_7);
lean::dec(x_7);
if (x_9 == 0)
{
lean::dec(x_6);
lean::dec(x_2);
x_1 = x_4;
goto _start;
}
else
{
obj* x_14; obj* x_15; 
x_14 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(x_0, x_4);
if (lean::is_scalar(x_6)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_6;
}
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
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
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 4);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 2);
lean::inc(x_5);
x_7 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_5, x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_12; 
x_8 = lean::cnstr_get(x_3, 4);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_12 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(x_0, x_2, x_8);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_20; obj* x_22; obj* x_23; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; 
x_13 = l_lean_elaborator_resolve__context___main___closed__1;
x_14 = lean::box(0);
lean::inc(x_0);
x_16 = l_lean_name_replace__prefix___main(x_0, x_13, x_14);
x_17 = lean::cnstr_get(x_2, 8);
lean::inc(x_17);
lean::inc(x_16);
x_20 = lean_environment_contains(x_17, x_16);
lean::inc(x_0);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_match__open__spec), 2, 1);
lean::closure_set(x_22, 0, x_0);
x_23 = lean::cnstr_get(x_3, 5);
lean::inc(x_23);
lean::dec(x_3);
x_26 = l_list_filter__map___main___rarg(x_22, x_23);
lean::inc(x_2);
x_28 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(x_2, x_26);
x_29 = lean::cnstr_get(x_2, 3);
lean::inc(x_29);
x_31 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(x_2, x_29);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_resolve__context___main___lambda__1), 2, 1);
lean::closure_set(x_32, 0, x_0);
x_33 = l_list_filter__map___main___rarg(x_32, x_31);
lean::inc(x_2);
x_35 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(x_2, x_33);
if (x_20 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_16);
x_37 = l_list_append___rarg(x_12, x_28);
x_38 = l_list_append___rarg(x_37, x_35);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_2);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_16);
lean::cnstr_set(x_41, 1, x_12);
x_42 = l_list_append___rarg(x_41, x_28);
x_43 = l_list_append___rarg(x_42, x_35);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_2);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_3);
x_47 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 1);
 x_49 = x_12;
} else {
 lean::inc(x_47);
 lean::dec(x_12);
 x_49 = lean::box(0);
}
x_50 = l_lean_name_append___main(x_47, x_0);
lean::dec(x_47);
x_52 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_49;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_2);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
else
{
obj* x_58; obj* x_61; obj* x_63; obj* x_64; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_3);
lean::dec(x_0);
x_58 = lean::cnstr_get(x_7, 0);
lean::inc(x_58);
lean::dec(x_7);
x_61 = lean::cnstr_get(x_58, 1);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 x_63 = x_58;
} else {
 lean::inc(x_61);
 lean::dec(x_58);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
lean::dec(x_61);
x_67 = lean::box(0);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set(x_68, 1, x_67);
if (lean::is_scalar(x_63)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_63;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_2);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
}
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_elaborator_resolve__context___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_resolve__context___main(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* l_lean_elaborator_resolve__context___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_resolve__context(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
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
x_11 = l_lean_elaborator_preresolve___main(x_6, x_1, x_2);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_8);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_16 = x_11;
} else {
 lean::inc(x_14);
 lean::dec(x_11);
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
obj* x_18; obj* x_21; obj* x_23; obj* x_26; 
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_18, 1);
lean::inc(x_23);
lean::dec(x_18);
x_26 = l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(x_8, x_1, x_23);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_10);
lean::dec(x_21);
x_29 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_31 = x_26;
} else {
 lean::inc(x_29);
 lean::dec(x_26);
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
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_33 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_35 = x_26;
} else {
 lean::inc(x_33);
 lean::dec(x_26);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 0);
x_38 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 x_40 = x_33;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
 lean::dec(x_33);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_41 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_41 = x_10;
}
lean::cnstr_set(x_41, 0, x_21);
lean::cnstr_set(x_41, 1, x_36);
if (lean::is_scalar(x_40)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_40;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_38);
if (lean::is_scalar(x_35)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_35;
}
lean::cnstr_set(x_43, 0, x_42);
return x_43;
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
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_15 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_17 = x_8;
} else {
 lean::inc(x_15);
 lean::dec(x_8);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_15, 0);
x_20 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
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
 x_53 = x_44;
} else {
 lean::inc(x_51);
 lean::dec(x_44);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 0);
x_56 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
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
obj* x_68; obj* x_69; 
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_0);
lean::cnstr_set(x_68, 1, x_2);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_elaborator_preresolve___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_preresolve___main(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* l_lean_elaborator_preresolve___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_preresolve(x_0, x_1, x_2);
lean::dec(x_1);
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
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg___boxed), 4, 0);
return x_1;
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
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_run___spec__6___boxed), 6, 3);
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 3);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 4);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 5);
lean::inc(x_13);
x_15 = l_lean_elaborator_run___lambda__1___closed__1;
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_13);
x_17 = lean::cnstr_get(x_2, 6);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_2, 7);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_2, 8);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 9);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 10);
lean::inc(x_25);
lean::dec(x_2);
x_28 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_28, 0, x_3);
lean::cnstr_set(x_28, 1, x_5);
lean::cnstr_set(x_28, 2, x_7);
lean::cnstr_set(x_28, 3, x_9);
lean::cnstr_set(x_28, 4, x_11);
lean::cnstr_set(x_28, 5, x_16);
lean::cnstr_set(x_28, 6, x_17);
lean::cnstr_set(x_28, 7, x_19);
lean::cnstr_set(x_28, 8, x_21);
lean::cnstr_set(x_28, 9, x_23);
lean::cnstr_set(x_28, 10, x_25);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_32, 0, x_31);
return x_32;
}
}
obj* l_lean_elaborator_run___lambda__2(obj* x_0, obj* x_1) {
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
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_33, 0, x_32);
return x_33;
}
else
{
obj* x_35; 
lean::dec(x_0);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_35, 0, x_1);
return x_35;
}
}
}
obj* _init_l_lean_elaborator_run___lambda__3___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown command: ");
return x_0;
}
}
obj* l_lean_elaborator_run___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_16; 
x_10 = l_lean_name_to__string___closed__1;
x_11 = l_lean_name_to__string__with__sep___main(x_10, x_3);
x_12 = l_lean_elaborator_run___lambda__3___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_16, 0, x_4);
lean::closure_set(x_16, 1, x_13);
lean::closure_set(x_16, 2, x_5);
lean::closure_set(x_16, 3, x_6);
lean::closure_set(x_16, 4, x_0);
x_8 = x_16;
goto lbl_9;
}
else
{
obj* x_19; obj* x_23; 
lean::dec(x_4);
lean::dec(x_3);
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
lean::dec(x_2);
lean::inc(x_0);
x_23 = lean::apply_3(x_19, x_5, x_6, x_0);
x_8 = x_23;
goto lbl_9;
}
lbl_9:
{
obj* x_24; 
x_24 = lean::apply_1(x_8, x_7);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; obj* x_28; 
lean::dec(x_1);
x_26 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_28 = x_24;
} else {
 lean::inc(x_26);
 lean::dec(x_24);
 x_28 = lean::box(0);
}
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_29 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_31 = x_26;
} else {
 lean::inc(x_29);
 lean::dec(x_26);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 2);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_0, 3);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_0, 4);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_0, 5);
lean::inc(x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_29);
lean::cnstr_set(x_44, 1, x_42);
x_45 = lean::cnstr_get(x_0, 6);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_0, 7);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_0, 8);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_0, 9);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_0, 10);
lean::inc(x_53);
lean::dec(x_0);
x_56 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_56, 0, x_32);
lean::cnstr_set(x_56, 1, x_34);
lean::cnstr_set(x_56, 2, x_36);
lean::cnstr_set(x_56, 3, x_38);
lean::cnstr_set(x_56, 4, x_40);
lean::cnstr_set(x_56, 5, x_44);
lean::cnstr_set(x_56, 6, x_45);
lean::cnstr_set(x_56, 7, x_47);
lean::cnstr_set(x_56, 8, x_49);
lean::cnstr_set(x_56, 9, x_51);
lean::cnstr_set(x_56, 10, x_53);
x_57 = lean::box(0);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_56);
if (lean::is_scalar(x_31)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_31;
 lean::cnstr_set_tag(x_31, 1);
}
lean::cnstr_set(x_59, 0, x_58);
if (lean::is_scalar(x_28)) {
 x_60 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_60 = x_28;
}
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
else
{
obj* x_62; 
lean::dec(x_0);
if (lean::is_scalar(x_28)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_28;
}
lean::cnstr_set(x_62, 0, x_26);
return x_62;
}
}
else
{
obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_0);
x_64 = lean::cnstr_get(x_24, 0);
x_66 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_68 = x_24;
} else {
 lean::inc(x_64);
 lean::inc(x_66);
 lean::dec(x_24);
 x_68 = lean::box(0);
}
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_69, 0, x_66);
lean::closure_set(x_69, 1, x_1);
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_64);
lean::cnstr_set(x_70, 1, x_69);
return x_70;
}
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_10);
lean::closure_set(x_12, 2, x_2);
lean::closure_set(x_12, 3, x_3);
lean::closure_set(x_12, 4, x_4);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_23; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = l_lean_elaborator_elaborators;
x_20 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_19, x_16);
lean::inc(x_4);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__2), 2, 1);
lean::closure_set(x_22, 0, x_4);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__3), 8, 7);
lean::closure_set(x_23, 0, x_4);
lean::closure_set(x_23, 1, x_22);
lean::closure_set(x_23, 2, x_20);
lean::closure_set(x_23, 3, x_16);
lean::closure_set(x_23, 4, x_0);
lean::closure_set(x_23, 5, x_2);
lean::closure_set(x_23, 6, x_3);
return x_23;
}
}
}
obj* l_lean_elaborator_run___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_10 = x_0;
} else {
 lean::inc(x_8);
 lean::dec(x_0);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_18; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::dec(x_13);
lean::inc(x_1);
x_22 = l_lean_parser_syntax_as__node___main(x_1);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg___boxed), 4, 1);
lean::closure_set(x_23, 0, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__4), 5, 1);
lean::closure_set(x_24, 0, x_1);
x_25 = l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg(x_23, x_24, x_2, x_3, x_18);
x_26 = lean::apply_1(x_25, x_16);
return x_26;
}
}
}
obj* l_lean_elaborator_run___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = l_lean_elaborator_preresolve___main(x_3, x_0, x_5);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__5___boxed), 5, 4);
lean::closure_set(x_10, 0, x_9);
lean::closure_set(x_10, 1, x_3);
lean::closure_set(x_10, 2, x_1);
lean::closure_set(x_10, 3, x_0);
return x_10;
}
}
obj* l_lean_elaborator_run___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__6), 3, 2);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_elaborator__coe__coelaborator___spec__1___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
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
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
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
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
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
uint8 x_0; obj* x_1; obj* x_2; 
x_0 = 0;
x_1 = lean::box(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_run___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__1___boxed), 3, 0);
return x_0;
}
}
obj* _init_l_lean_elaborator_run___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__7___boxed), 4, 0);
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
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_reader__t_pure___at_lean_elaborator_run___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_run___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_elaborator_run___spec__4(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_run___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_run___spec__6(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_lean_elaborator_run___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_run___lambda__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_elaborator_run___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_elaborator_run___lambda__5(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_elaborator_run___lambda__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_run___lambda__7(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
 l_lean_elaborator_coelaborator__m_monad__coroutine = _init_l_lean_elaborator_coelaborator__m_monad__coroutine();
lean::mark_persistent(l_lean_elaborator_coelaborator__m_monad__coroutine);
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
 l_lean_elaborator_end__scope___lambda__2___closed__1 = _init_l_lean_elaborator_end__scope___lambda__2___closed__1();
lean::mark_persistent(l_lean_elaborator_end__scope___lambda__2___closed__1);
 l_lean_elaborator_end__scope___lambda__2___closed__2 = _init_l_lean_elaborator_end__scope___lambda__2___closed__2();
lean::mark_persistent(l_lean_elaborator_end__scope___lambda__2___closed__2);
 l_lean_elaborator_end__scope___lambda__3___closed__1 = _init_l_lean_elaborator_end__scope___lambda__3___closed__1();
lean::mark_persistent(l_lean_elaborator_end__scope___lambda__3___closed__1);
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___closed__1 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___closed__1();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___closed__1);
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1();
lean::mark_persistent(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1);
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
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1);
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2);
 l_lean_elaborator_run___lambda__1___closed__1 = _init_l_lean_elaborator_run___lambda__1___closed__1();
lean::mark_persistent(l_lean_elaborator_run___lambda__1___closed__1);
 l_lean_elaborator_run___lambda__3___closed__1 = _init_l_lean_elaborator_run___lambda__3___closed__1();
lean::mark_persistent(l_lean_elaborator_run___lambda__3___closed__1);
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
