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
obj* l_lean_elaborator_ordered__rbmap_insert___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___boxed(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7___boxed(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
obj* l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_current__command___boxed(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5;
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6;
obj* l_lean_elaborator_locally___rarg___lambda__2(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7___boxed(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_command_variables;
extern "C" obj* lean_expr_mk_pi(obj*, uint8, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__reader__adapter(obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed(obj*, obj*);
obj* l_lean_elaborator_module_header_elaborate___closed__1;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__9___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_level__get__app__args___main___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_level__get__app__args___main(obj*, obj*, obj*);
obj* l_lean_elaborator_elab__def__like(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___lambda__3___boxed(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4(obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___boxed(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_sort(obj*);
obj* l_lean_elaborator_run___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20___boxed(obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1(obj*, obj*);
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1(obj*);
obj* l_lean_elaborator_attrs__to__pexpr(obj*, obj*, obj*);
obj* l_lean_elaborator_expr_mk__annotation___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2___boxed(obj*, obj*, obj*);
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
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__5___boxed(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___rarg(obj*, obj*);
extern obj* l_lean_parser_level_leading_has__view;
obj* l_except__t_lift___rarg___lambda__1___boxed(obj*);
extern obj* l_lean_parser_command_reserve__notation_has__view;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate___closed__1;
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg___boxed(obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1(obj*, obj*);
obj* l_list_foldl___main___at_lean_expr_mk__app___spec__1(obj*, obj*);
obj* l_lean_elaborator_run___lambda__5(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_run___closed__2;
obj* l_lean_elaborator_end__scope___lambda__3___closed__1;
obj* l_lean_elaborator_resolve__context___main___boxed(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_set__option_elaborate___boxed(obj*, obj*, obj*);
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
obj* l_lean_elaborator_current__command___rarg___closed__1;
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___boxed(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_level__get__app__args(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3;
extern obj* l_lean_parser_command_open;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5;
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1___lambda__1(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2;
obj* l_lean_elaborator_run___lambda__2___closed__1;
obj* l_lean_elaborator_elaborator__config__coe__frontend__config(obj*);
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___closed__1;
obj* l_lean_elaborator_elaborator__coe__coelaborator(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__26;
obj* l_lean_kvmap_set__string(obj*, obj*, obj*);
obj* l_lean_parser_term_get__leading___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1;
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(obj*, obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__15(obj*, obj*);
obj* l_lean_elaborator_notation_elaborate__aux___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_mk__eqns___closed__2;
obj* l_reader__t_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___lambda__3(obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate__aux___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__reader__adapter___boxed(obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___boxed(obj*, obj*, obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_run___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_universe_elaborate___boxed(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__31;
obj* l_lean_elaborator_module_header_elaborate___boxed(obj*, obj*, obj*);
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
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1___boxed(obj*, obj*, obj*);
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
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2(obj*, obj*);
obj* l_lean_elaborator_max__recursion;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18___boxed(obj*, obj*, obj*);
obj* l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1___boxed(obj*, obj*);
obj* l_lean_elaborator_section_elaborate___closed__1;
obj* l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg(obj*, obj*);
obj* l_lean_elaborator_elab__def__like___closed__1;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(obj*);
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__state___boxed(obj*);
obj* l_lean_elaborator_expr_mk__annotation___closed__1;
obj* l_lean_elaborator_get__namespace___rarg___boxed(obj*);
obj* l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(obj*);
obj* l_lean_elaborator_command_elaborate___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main___boxed(obj*, obj*, obj*);
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__6;
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_check_elaborate(obj*, obj*, obj*);
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_parser_rec__t_run___at_lean_elaborator_run___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_old__elab__command___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___boxed(obj*, obj*, obj*);
uint8 l_coe__decidable__eq(uint8);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(obj*, obj*, obj*);
extern obj* l_lean_parser_command_notation;
obj* l_lean_elaborator_elaborator__t;
obj* l_lean_elaborator_current__command(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24(obj*, obj*, obj*);
obj* l_lean_kvmap_set__name(obj*, obj*, obj*);
uint8 l_lean_elaborator_is__open__namespace(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborators;
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate(uint8, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_string__lit_has__view;
extern obj* l_lean_parser_term_pi_has__view;
obj* l_lean_elaborator_export_elaborate___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command___lambda__3___boxed(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_find___rarg(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_resolve__context___main___lambda__1(obj*, obj*);
extern obj* l_lean_parser_command_universe_has__view;
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
obj* l_lean_elaborator_locally___rarg(obj*, obj*, obj*);
obj* l_state__t_monad__state___rarg(obj*);
obj* l_lean_elaborator_elaborator__m;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
extern "C" obj* lean_expr_mk_lambda(obj*, uint8, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___boxed(obj*, obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___boxed(obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__16___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_command_reserve__notation;
obj* l_lean_elaborator_elaborator__t_monad__reader___boxed(obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1___boxed(obj*, obj*);
obj* l_except__t_monad__except___rarg(obj*);
extern obj* l_lean_parser_term_have_has__view;
obj* l_lean_elaborator_init__quot_elaborate(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
extern obj* l_lean_parser_command_variables_has__view;
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__32;
obj* l_lean_elaborator_end__scope___lambda__1(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_lean_parser_trie_insert___rarg(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___lambda__2___boxed(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t___at_lean_elaborator_command_elaborate___spec__2;
obj* l_lean_elaborator_preresolve___main(obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind___rarg___closed__1;
obj* l_dlist_singleton___rarg___boxed(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__5;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1___boxed(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_yield__to__outside___rarg(obj*);
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__3;
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(obj*, obj*);
obj* l_lean_elaborator_expr_mk__annotation(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___lambda__1(obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25(obj*, obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__1___boxed(obj*);
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
obj* l_lean_elaborator_commands_elaborate___main___lambda__5(obj*, obj*, obj*);
obj* l_lean_elaborator_yield__to__outside___boxed(obj*, obj*);
obj* l_lean_parser_syntax_get__pos(obj*);
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__5(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___boxed(obj*, obj*, obj*);
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
obj* l_lean_elaborator_commands_elaborate___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_list_zip___rarg___lambda__1___boxed(obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___rarg(obj*, obj*, obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4___boxed(obj*, obj*);
obj* l_lean_elaborator_attrs__to__pexpr___boxed(obj*, obj*, obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
obj* l_reader__t_pure___at_lean_elaborator_run___spec__3___boxed(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__17;
extern obj* l_lean_parser_module_header;
obj* l_lean_elaborator_level__get__app__args___main___boxed(obj*, obj*, obj*);
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
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__tokens(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__10;
obj* l_rbmap_insert___main___at_lean_elaborator_include_elaborate___spec__1(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(obj*, obj*);
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m(obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_run(obj*);
obj* l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1___boxed(obj*);
obj* l_lean_elaborator_match__precedence___boxed(obj*, obj*);
extern obj* l_lean_message__log_empty;
obj* l_lean_elaborator_register__notation__macro___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_export_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_yield__to__outside___rarg___boxed(obj*);
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
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__9(obj*, obj*, obj*);
extern obj* l_lean_expander_binding__annotation__update;
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___boxed(obj*);
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
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___boxed(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__13(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(obj*, obj*, obj*, obj*);
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
obj* l_lean_elaborator_elaborator__t_monad__except___boxed(obj*);
obj* l_lean_elaborator_elaborator__coe__coelaborator___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_set__option_elaborate(obj*, obj*, obj*);
obj* l_reader__t_read___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(obj*, obj*, obj*);
obj* l_lean_elaborator_run___lambda__1(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_no__kind_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_resolve__context___main(obj*, obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_run___spec__6(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_max__prec;
obj* l_lean_elaborator_notation_elaborate__aux(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__7(obj*, obj*);
obj* l_lean_elaborator_end__scope___lambda__2___closed__2;
extern obj* l_lean_options_mk;
obj* l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_universe_elaborate___closed__1;
obj* l_monad__state__trans___rarg(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__20;
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1;
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__7___boxed(obj*, obj*);
obj* l_lean_expander_get__opt__type___main(obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4;
obj* l_coroutine_pure___rarg___boxed(obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2(obj*, obj*);
extern obj* l_lean_parser_term_struct__inst_has__view;
obj* l_coroutine_yield___rarg___boxed(obj*, obj*);
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
obj* l_lean_elaborator_with__current__command___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg(obj*);
extern "C" obj* lean_expr_mk_let(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_app_has__view;
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2___boxed(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(obj*, obj*, obj*, obj*);
obj* l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15___boxed(obj*);
obj* l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___boxed(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
obj* l_reader__t_monad__reader__adapter___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main(obj*, obj*, obj*);
extern obj* l_lean_parser_ident__univs_has__view;
obj* l_lean_elaborator_to__pexpr___main___closed__9;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(obj*);
obj* l_state__t_monad__except___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_end__scope(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1___boxed(obj*, obj*);
extern obj* l_lean_parser_term_sort__app_has__view;
obj* l_lean_elaborator_to__pexpr___main___lambda__1(obj*);
extern obj* l_lean_parser_term_explicit_has__view;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3(obj*, obj*);
obj* l_lean_elaborator_current__command___rarg(obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___boxed(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_prec__to__nat(obj*);
obj* l_lean_elaborator_end__scope___lambda__2___closed__1;
extern obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
obj* l_state__t_lift___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__24;
obj* l_lean_elaborator_ordered__rbmap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_reserve__notation_elaborate___boxed(obj*, obj*, obj*);
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
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2___boxed(obj*, obj*, obj*);
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
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___boxed(obj*, obj*, obj*);
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
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5___boxed(obj*, obj*, obj*);
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
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_current__command___rarg___lambda__1___boxed(obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_preresolve(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___boxed(obj*, obj*, obj*);
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
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_struct__inst__item_has__view;
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__2(obj*);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_match__precedence___main___boxed(obj*, obj*);
extern obj* l_lean_parser_term_borrowed_has__view;
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11___boxed(obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad___boxed(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_term_binders_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___lambda__1___boxed(obj*);
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(obj*);
obj* l_lean_level_of__nat___main(obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1;
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
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_attribute_elaborate___closed__1;
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(obj*);
uint8 l_lean_elaborator_match__precedence(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
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
obj* l_lean_elaborator_current__command___rarg___lambda__1(obj*, obj*);
obj* l_lean_elaborator_level__get__app__args___boxed(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_locally(obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_check_elaborate___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
obj* l_lean_elaborator_to__level___main___closed__2;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__5(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(obj*, obj*, obj*);
extern obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
obj* l_lean_elaborator_open_elaborate___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__5___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
obj* l_lean_elaborator_commands_elaborate___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_match__spec(obj*, obj*);
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
obj* l_lean_elaborator_simple__binders__to__pexpr___boxed(obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_expr_mk__capp(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1___boxed(obj*, obj*, obj*);
extern "C" obj* level_mk_mvar(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__2(uint8, obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18___boxed(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3___boxed(obj*, obj*, obj*);
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
obj* l_lean_elaborator_elaborator__m__coe__coelaborator__m___boxed(obj*);
extern obj* l_lean_parser_command_end_has__view;
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__4(obj*, obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(obj*);
obj* l_lean_expander_mk__notation__transformer___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13;
extern obj* l_lean_parser_term_anonymous__constructor_has__view;
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2;
obj* l_list_map___main___at_lean_elaborator_export_elaborate___spec__1___boxed(obj*, obj*);
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
obj* l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__3(obj*, obj*);
obj* l_lean_elaborator_section_elaborate___lambda__2(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__coe__coelaborator___lambda__1(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__21(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11___boxed(obj*, obj*, obj*);
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
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3___boxed(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(obj*);
obj* l_lean_elaborator_old__elab__command(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___boxed(obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1(obj*);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
extern "C" obj* level_mk_param(obj*);
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
extern "C" obj* lean_elaborator_elaborate_command(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20(obj*, obj*, obj*);
extern obj* l_lean_expander_get__opt__type___main___closed__1;
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__10(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_level_trailing_has__view;
obj* l_rbmap_insert___main___at_lean_elaborator_include_elaborate___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_no__kind_elaborate___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___closed__1;
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_attribute_elaborate___boxed(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25___boxed(obj*, obj*);
obj* l_except__t_lift___rarg___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__29;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_option_map___rarg(obj*, obj*);
extern obj* l_lean_expander_no__expansion___closed__1;
extern "C" obj* lean_expr_mk_bvar(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__40;
obj* l_lean_elaborator_run___lambda__3___boxed(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(obj*);
extern "C" obj* lean_expr_mk_mvar(obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1(obj*);
obj* l_lean_elaborator_command_elaborate(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_prec__to__nat___main(obj*);
obj* l_lean_elaborator_with__current__command___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_view_value(obj*);
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2___boxed(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4(obj*, obj*, uint8, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__42;
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1;
extern "C" uint8 lean_environment_contains(obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1(obj*, obj*, obj*);
extern obj* l_lean_parser_command_notation_has__view;
extern obj* l_lean_parser_command_check;
obj* l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1___boxed(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__1(obj*, obj*);
obj* l_lean_elaborator_max__commands;
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__10___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_command_export;
obj* l_lean_elaborator_ordered__rbmap_of__list___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__state___rarg(obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__44;
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9___boxed(obj*, obj*, obj*, obj*);
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
uint8 x_5; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_5 = 0;
lean::inc(x_3);
x_7 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_3);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set_scalar(x_7, sizeof(void*)*4, x_5);
x_8 = x_7;
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_22; uint8 x_23; 
x_10 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
x_14 = lean::cnstr_get(x_1, 2);
x_16 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_2);
lean::inc(x_0);
x_22 = lean::apply_2(x_0, x_2, x_12);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_27; uint8 x_28; 
lean::inc(x_2);
lean::inc(x_12);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_12, x_2);
x_28 = lean::unbox(x_27);
if (x_28 == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_12);
lean::inc(x_3);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_33 = x_18;
}
lean::cnstr_set(x_33, 0, x_10);
lean::cnstr_set(x_33, 1, x_2);
lean::cnstr_set(x_33, 2, x_3);
lean::cnstr_set(x_33, 3, x_16);
lean::cnstr_set_scalar(x_33, sizeof(void*)*4, x_9);
x_34 = x_33;
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_16, x_2, x_3);
if (lean::is_scalar(x_18)) {
 x_36 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_36 = x_18;
}
lean::cnstr_set(x_36, 0, x_10);
lean::cnstr_set(x_36, 1, x_12);
lean::cnstr_set(x_36, 2, x_14);
lean::cnstr_set(x_36, 3, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_9);
x_37 = x_36;
return x_37;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_10, x_2, x_3);
if (lean::is_scalar(x_18)) {
 x_39 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_39 = x_18;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_12);
lean::cnstr_set(x_39, 2, x_14);
lean::cnstr_set(x_39, 3, x_16);
lean::cnstr_set_scalar(x_39, sizeof(void*)*4, x_9);
x_40 = x_39;
return x_40;
}
}
else
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_53; uint8 x_54; 
x_41 = lean::cnstr_get(x_1, 0);
x_43 = lean::cnstr_get(x_1, 1);
x_45 = lean::cnstr_get(x_1, 2);
x_47 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_49 = x_1;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_1);
 x_49 = lean::box(0);
}
lean::inc(x_43);
lean::inc(x_2);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_2, x_43);
x_54 = lean::unbox(x_53);
if (x_54 == 0)
{
obj* x_58; uint8 x_59; 
lean::inc(x_2);
lean::inc(x_43);
lean::inc(x_0);
x_58 = lean::apply_2(x_0, x_43, x_2);
x_59 = lean::unbox(x_58);
if (x_59 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_0);
lean::dec(x_45);
lean::dec(x_43);
lean::inc(x_3);
if (lean::is_scalar(x_49)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_49;
}
lean::cnstr_set(x_64, 0, x_41);
lean::cnstr_set(x_64, 1, x_2);
lean::cnstr_set(x_64, 2, x_3);
lean::cnstr_set(x_64, 3, x_47);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_9);
x_65 = x_64;
return x_65;
}
else
{
uint8 x_66; 
x_66 = l_rbnode_is__red___main___rarg(x_47);
if (x_66 == 0)
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_47, x_2, x_3);
if (lean::is_scalar(x_49)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_49;
}
lean::cnstr_set(x_68, 0, x_41);
lean::cnstr_set(x_68, 1, x_43);
lean::cnstr_set(x_68, 2, x_45);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_9);
x_69 = x_68;
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_70 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_71 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_71 = x_49;
}
lean::cnstr_set(x_71, 0, x_41);
lean::cnstr_set(x_71, 1, x_43);
lean::cnstr_set(x_71, 2, x_45);
lean::cnstr_set(x_71, 3, x_70);
lean::cnstr_set_scalar(x_71, sizeof(void*)*4, x_9);
x_72 = x_71;
x_73 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_47, x_2, x_3);
x_74 = l_rbnode_balance2___main___rarg(x_72, x_73);
return x_74;
}
}
}
else
{
uint8 x_75; 
x_75 = l_rbnode_is__red___main___rarg(x_41);
if (x_75 == 0)
{
obj* x_76; obj* x_77; obj* x_78; 
x_76 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_41, x_2, x_3);
if (lean::is_scalar(x_49)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_49;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_43);
lean::cnstr_set(x_77, 2, x_45);
lean::cnstr_set(x_77, 3, x_47);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_9);
x_78 = x_77;
return x_78;
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_79 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_80 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_80 = x_49;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_43);
lean::cnstr_set(x_80, 2, x_45);
lean::cnstr_set(x_80, 3, x_47);
lean::cnstr_set_scalar(x_80, sizeof(void*)*4, x_9);
x_81 = x_80;
x_82 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_41, x_2, x_3);
x_83 = l_rbnode_balance1___main___rarg(x_81, x_82);
return x_83;
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_5 = 0;
lean::inc(x_3);
x_7 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_3);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set_scalar(x_7, sizeof(void*)*4, x_5);
x_8 = x_7;
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_22; uint8 x_23; 
x_10 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
x_14 = lean::cnstr_get(x_1, 2);
x_16 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_2);
lean::inc(x_0);
x_22 = lean::apply_2(x_0, x_2, x_12);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_27; uint8 x_28; 
lean::inc(x_2);
lean::inc(x_12);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_12, x_2);
x_28 = lean::unbox(x_27);
if (x_28 == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_12);
lean::inc(x_3);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_33 = x_18;
}
lean::cnstr_set(x_33, 0, x_10);
lean::cnstr_set(x_33, 1, x_2);
lean::cnstr_set(x_33, 2, x_3);
lean::cnstr_set(x_33, 3, x_16);
lean::cnstr_set_scalar(x_33, sizeof(void*)*4, x_9);
x_34 = x_33;
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_16, x_2, x_3);
if (lean::is_scalar(x_18)) {
 x_36 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_36 = x_18;
}
lean::cnstr_set(x_36, 0, x_10);
lean::cnstr_set(x_36, 1, x_12);
lean::cnstr_set(x_36, 2, x_14);
lean::cnstr_set(x_36, 3, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_9);
x_37 = x_36;
return x_37;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_10, x_2, x_3);
if (lean::is_scalar(x_18)) {
 x_39 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_39 = x_18;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_12);
lean::cnstr_set(x_39, 2, x_14);
lean::cnstr_set(x_39, 3, x_16);
lean::cnstr_set_scalar(x_39, sizeof(void*)*4, x_9);
x_40 = x_39;
return x_40;
}
}
else
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_53; uint8 x_54; 
x_41 = lean::cnstr_get(x_1, 0);
x_43 = lean::cnstr_get(x_1, 1);
x_45 = lean::cnstr_get(x_1, 2);
x_47 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_49 = x_1;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_1);
 x_49 = lean::box(0);
}
lean::inc(x_43);
lean::inc(x_2);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_2, x_43);
x_54 = lean::unbox(x_53);
if (x_54 == 0)
{
obj* x_58; uint8 x_59; 
lean::inc(x_2);
lean::inc(x_43);
lean::inc(x_0);
x_58 = lean::apply_2(x_0, x_43, x_2);
x_59 = lean::unbox(x_58);
if (x_59 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_0);
lean::dec(x_45);
lean::dec(x_43);
lean::inc(x_3);
if (lean::is_scalar(x_49)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_49;
}
lean::cnstr_set(x_64, 0, x_41);
lean::cnstr_set(x_64, 1, x_2);
lean::cnstr_set(x_64, 2, x_3);
lean::cnstr_set(x_64, 3, x_47);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_9);
x_65 = x_64;
return x_65;
}
else
{
uint8 x_66; 
x_66 = l_rbnode_is__red___main___rarg(x_47);
if (x_66 == 0)
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_47, x_2, x_3);
if (lean::is_scalar(x_49)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_49;
}
lean::cnstr_set(x_68, 0, x_41);
lean::cnstr_set(x_68, 1, x_43);
lean::cnstr_set(x_68, 2, x_45);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_9);
x_69 = x_68;
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_70 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_71 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_71 = x_49;
}
lean::cnstr_set(x_71, 0, x_41);
lean::cnstr_set(x_71, 1, x_43);
lean::cnstr_set(x_71, 2, x_45);
lean::cnstr_set(x_71, 3, x_70);
lean::cnstr_set_scalar(x_71, sizeof(void*)*4, x_9);
x_72 = x_71;
x_73 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_47, x_2, x_3);
x_74 = l_rbnode_balance2___main___rarg(x_72, x_73);
return x_74;
}
}
}
else
{
uint8 x_75; 
x_75 = l_rbnode_is__red___main___rarg(x_41);
if (x_75 == 0)
{
obj* x_76; obj* x_77; obj* x_78; 
x_76 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_41, x_2, x_3);
if (lean::is_scalar(x_49)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_49;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_43);
lean::cnstr_set(x_77, 2, x_45);
lean::cnstr_set(x_77, 3, x_47);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_9);
x_78 = x_77;
return x_78;
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_79 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_80 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_80 = x_49;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_43);
lean::cnstr_set(x_80, 2, x_45);
lean::cnstr_set(x_80, 3, x_47);
lean::cnstr_set_scalar(x_80, sizeof(void*)*4, x_9);
x_81 = x_80;
x_82 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_41, x_2, x_3);
x_83 = l_rbnode_balance1___main___rarg(x_81, x_82);
return x_83;
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg___boxed), 4, 0);
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg___boxed), 4, 0);
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
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
lean::inc(x_3);
lean::inc(x_12);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_3);
x_18 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(x_0, x_10, x_2, x_17);
lean::dec(x_17);
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_add(x_12, x_20);
lean::dec(x_12);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_9);
lean::cnstr_set(x_23, 1, x_18);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_insert___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
obj* l_lean_elaborator_ordered__rbmap_insert___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_ordered__rbmap_insert___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
uint8 x_5; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_5 = 0;
lean::inc(x_3);
x_7 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_3);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set_scalar(x_7, sizeof(void*)*4, x_5);
x_8 = x_7;
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_22; uint8 x_23; 
x_10 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
x_14 = lean::cnstr_get(x_1, 2);
x_16 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_2);
lean::inc(x_0);
x_22 = lean::apply_2(x_0, x_2, x_12);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_27; uint8 x_28; 
lean::inc(x_2);
lean::inc(x_12);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_12, x_2);
x_28 = lean::unbox(x_27);
if (x_28 == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_12);
lean::inc(x_3);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_33 = x_18;
}
lean::cnstr_set(x_33, 0, x_10);
lean::cnstr_set(x_33, 1, x_2);
lean::cnstr_set(x_33, 2, x_3);
lean::cnstr_set(x_33, 3, x_16);
lean::cnstr_set_scalar(x_33, sizeof(void*)*4, x_9);
x_34 = x_33;
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_16, x_2, x_3);
if (lean::is_scalar(x_18)) {
 x_36 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_36 = x_18;
}
lean::cnstr_set(x_36, 0, x_10);
lean::cnstr_set(x_36, 1, x_12);
lean::cnstr_set(x_36, 2, x_14);
lean::cnstr_set(x_36, 3, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_9);
x_37 = x_36;
return x_37;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_10, x_2, x_3);
if (lean::is_scalar(x_18)) {
 x_39 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_39 = x_18;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_12);
lean::cnstr_set(x_39, 2, x_14);
lean::cnstr_set(x_39, 3, x_16);
lean::cnstr_set_scalar(x_39, sizeof(void*)*4, x_9);
x_40 = x_39;
return x_40;
}
}
else
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_53; uint8 x_54; 
x_41 = lean::cnstr_get(x_1, 0);
x_43 = lean::cnstr_get(x_1, 1);
x_45 = lean::cnstr_get(x_1, 2);
x_47 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_49 = x_1;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_1);
 x_49 = lean::box(0);
}
lean::inc(x_43);
lean::inc(x_2);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_2, x_43);
x_54 = lean::unbox(x_53);
if (x_54 == 0)
{
obj* x_58; uint8 x_59; 
lean::inc(x_2);
lean::inc(x_43);
lean::inc(x_0);
x_58 = lean::apply_2(x_0, x_43, x_2);
x_59 = lean::unbox(x_58);
if (x_59 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_0);
lean::dec(x_45);
lean::dec(x_43);
lean::inc(x_3);
if (lean::is_scalar(x_49)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_49;
}
lean::cnstr_set(x_64, 0, x_41);
lean::cnstr_set(x_64, 1, x_2);
lean::cnstr_set(x_64, 2, x_3);
lean::cnstr_set(x_64, 3, x_47);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_9);
x_65 = x_64;
return x_65;
}
else
{
uint8 x_66; 
x_66 = l_rbnode_is__red___main___rarg(x_47);
if (x_66 == 0)
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_47, x_2, x_3);
if (lean::is_scalar(x_49)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_49;
}
lean::cnstr_set(x_68, 0, x_41);
lean::cnstr_set(x_68, 1, x_43);
lean::cnstr_set(x_68, 2, x_45);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_9);
x_69 = x_68;
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_70 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_71 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_71 = x_49;
}
lean::cnstr_set(x_71, 0, x_41);
lean::cnstr_set(x_71, 1, x_43);
lean::cnstr_set(x_71, 2, x_45);
lean::cnstr_set(x_71, 3, x_70);
lean::cnstr_set_scalar(x_71, sizeof(void*)*4, x_9);
x_72 = x_71;
x_73 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_47, x_2, x_3);
x_74 = l_rbnode_balance2___main___rarg(x_72, x_73);
return x_74;
}
}
}
else
{
uint8 x_75; 
x_75 = l_rbnode_is__red___main___rarg(x_41);
if (x_75 == 0)
{
obj* x_76; obj* x_77; obj* x_78; 
x_76 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_41, x_2, x_3);
if (lean::is_scalar(x_49)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_49;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_43);
lean::cnstr_set(x_77, 2, x_45);
lean::cnstr_set(x_77, 3, x_47);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_9);
x_78 = x_77;
return x_78;
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_79 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_80 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_80 = x_49;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_43);
lean::cnstr_set(x_80, 2, x_45);
lean::cnstr_set(x_80, 3, x_47);
lean::cnstr_set_scalar(x_80, sizeof(void*)*4, x_9);
x_81 = x_80;
x_82 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_41, x_2, x_3);
x_83 = l_rbnode_balance1___main___rarg(x_81, x_82);
return x_83;
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_5 = 0;
lean::inc(x_3);
x_7 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_3);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set_scalar(x_7, sizeof(void*)*4, x_5);
x_8 = x_7;
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_22; uint8 x_23; 
x_10 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
x_14 = lean::cnstr_get(x_1, 2);
x_16 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_2);
lean::inc(x_0);
x_22 = lean::apply_2(x_0, x_2, x_12);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_27; uint8 x_28; 
lean::inc(x_2);
lean::inc(x_12);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_12, x_2);
x_28 = lean::unbox(x_27);
if (x_28 == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_12);
lean::inc(x_3);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_33 = x_18;
}
lean::cnstr_set(x_33, 0, x_10);
lean::cnstr_set(x_33, 1, x_2);
lean::cnstr_set(x_33, 2, x_3);
lean::cnstr_set(x_33, 3, x_16);
lean::cnstr_set_scalar(x_33, sizeof(void*)*4, x_9);
x_34 = x_33;
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_16, x_2, x_3);
if (lean::is_scalar(x_18)) {
 x_36 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_36 = x_18;
}
lean::cnstr_set(x_36, 0, x_10);
lean::cnstr_set(x_36, 1, x_12);
lean::cnstr_set(x_36, 2, x_14);
lean::cnstr_set(x_36, 3, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_9);
x_37 = x_36;
return x_37;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_10, x_2, x_3);
if (lean::is_scalar(x_18)) {
 x_39 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_39 = x_18;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_12);
lean::cnstr_set(x_39, 2, x_14);
lean::cnstr_set(x_39, 3, x_16);
lean::cnstr_set_scalar(x_39, sizeof(void*)*4, x_9);
x_40 = x_39;
return x_40;
}
}
else
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_53; uint8 x_54; 
x_41 = lean::cnstr_get(x_1, 0);
x_43 = lean::cnstr_get(x_1, 1);
x_45 = lean::cnstr_get(x_1, 2);
x_47 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_49 = x_1;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_1);
 x_49 = lean::box(0);
}
lean::inc(x_43);
lean::inc(x_2);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_2, x_43);
x_54 = lean::unbox(x_53);
if (x_54 == 0)
{
obj* x_58; uint8 x_59; 
lean::inc(x_2);
lean::inc(x_43);
lean::inc(x_0);
x_58 = lean::apply_2(x_0, x_43, x_2);
x_59 = lean::unbox(x_58);
if (x_59 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_0);
lean::dec(x_45);
lean::dec(x_43);
lean::inc(x_3);
if (lean::is_scalar(x_49)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_49;
}
lean::cnstr_set(x_64, 0, x_41);
lean::cnstr_set(x_64, 1, x_2);
lean::cnstr_set(x_64, 2, x_3);
lean::cnstr_set(x_64, 3, x_47);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_9);
x_65 = x_64;
return x_65;
}
else
{
uint8 x_66; 
x_66 = l_rbnode_is__red___main___rarg(x_47);
if (x_66 == 0)
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_47, x_2, x_3);
if (lean::is_scalar(x_49)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_49;
}
lean::cnstr_set(x_68, 0, x_41);
lean::cnstr_set(x_68, 1, x_43);
lean::cnstr_set(x_68, 2, x_45);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_9);
x_69 = x_68;
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_70 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_71 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_71 = x_49;
}
lean::cnstr_set(x_71, 0, x_41);
lean::cnstr_set(x_71, 1, x_43);
lean::cnstr_set(x_71, 2, x_45);
lean::cnstr_set(x_71, 3, x_70);
lean::cnstr_set_scalar(x_71, sizeof(void*)*4, x_9);
x_72 = x_71;
x_73 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_47, x_2, x_3);
x_74 = l_rbnode_balance2___main___rarg(x_72, x_73);
return x_74;
}
}
}
else
{
uint8 x_75; 
x_75 = l_rbnode_is__red___main___rarg(x_41);
if (x_75 == 0)
{
obj* x_76; obj* x_77; obj* x_78; 
x_76 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_41, x_2, x_3);
if (lean::is_scalar(x_49)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_49;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_43);
lean::cnstr_set(x_77, 2, x_45);
lean::cnstr_set(x_77, 3, x_47);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_9);
x_78 = x_77;
return x_78;
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_79 = lean::box(0);
if (lean::is_scalar(x_49)) {
 x_80 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_80 = x_49;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_43);
lean::cnstr_set(x_80, 2, x_45);
lean::cnstr_set(x_80, 3, x_47);
lean::cnstr_set_scalar(x_80, sizeof(void*)*4, x_9);
x_81 = x_80;
x_82 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_41, x_2, x_3);
x_83 = l_rbnode_balance1___main___rarg(x_81, x_82);
return x_83;
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg___boxed), 4, 0);
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg___boxed), 4, 0);
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
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
lean::inc(x_3);
lean::inc(x_12);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_3);
x_18 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(x_0, x_10, x_2, x_17);
lean::dec(x_17);
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_add(x_12, x_20);
lean::dec(x_12);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_9);
lean::cnstr_set(x_23, 1, x_18);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg___boxed), 4, 0);
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
lean::dec(x_11);
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
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 0);
return x_2;
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::inc(x_3);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_2);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_10);
return x_11;
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
obj* l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_elaborator_command_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_command_elaborate(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
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
obj* l_lean_elaborator_current__command___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
lean::inc(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_0);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_lean_elaborator_current__command___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pure___rarg___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg___lambda__1___boxed), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__1___boxed), 1, 0);
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg___lambda__1___boxed), 2, 1);
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_elaborator_current__command___rarg___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_current__command___rarg___lambda__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
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
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
}
}
obj* l_lean_elaborator_elaborator__coe__coelaborator(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = l_lean_elaborator_current__command___rarg(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elaborator__coe__coelaborator___lambda__1), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_4);
lean::closure_set(x_7, 1, x_6);
return x_7;
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; uint8 x_14; obj* x_15; obj* x_18; obj* x_19; obj* x_20; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_4, 0);
x_6 = lean::cnstr_get(x_4, 2);
x_7 = l_lean_parser_syntax_get__pos(x_0);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_option_get__or__else___main___rarg(x_7, x_8);
lean::dec(x_7);
x_11 = l_lean_file__map_to__position(x_6, x_9);
lean::dec(x_9);
x_13 = lean::box(0);
x_14 = 2;
x_15 = l_string_join___closed__1;
lean::inc(x_1);
lean::inc(x_5);
x_18 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_11);
lean::cnstr_set(x_18, 2, x_13);
lean::cnstr_set(x_18, 3, x_15);
lean::cnstr_set(x_18, 4, x_1);
lean::cnstr_set_scalar(x_18, sizeof(void*)*5, x_14);
x_19 = x_18;
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
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
obj* x_3; 
x_3 = l_lean_parser_syntax_kind___main(x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; 
lean::inc(x_0);
x_5 = l_lean_parser_syntax_to__format___main(x_0);
x_6 = lean::mk_nat_obj(80u);
x_7 = l_lean_format_pretty(x_5, x_6);
lean::dec(x_5);
x_9 = l_lean_elaborator_level__get__app__args___main___closed__1;
x_10 = lean::string_append(x_9, x_7);
lean::dec(x_7);
x_12 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_10, x_1, x_2);
lean::dec(x_10);
lean::dec(x_0);
return x_12;
}
else
{
obj* x_15; obj* x_18; uint8 x_19; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
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
obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_31; 
lean::inc(x_0);
x_24 = l_lean_parser_syntax_to__format___main(x_0);
x_25 = lean::mk_nat_obj(80u);
x_26 = l_lean_format_pretty(x_24, x_25);
lean::dec(x_24);
x_28 = l_lean_elaborator_level__get__app__args___main___closed__1;
x_29 = lean::string_append(x_28, x_26);
lean::dec(x_26);
x_31 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_29, x_1, x_2);
lean::dec(x_29);
lean::dec(x_0);
return x_31;
}
else
{
obj* x_34; obj* x_35; obj* x_39; 
x_34 = l_lean_parser_level_trailing_has__view;
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
lean::dec(x_34);
lean::inc(x_0);
x_39 = lean::apply_1(x_35, x_0);
if (lean::obj_tag(x_39) == 0)
{
obj* x_41; obj* x_44; obj* x_46; 
lean::dec(x_0);
x_41 = lean::cnstr_get(x_39, 0);
lean::inc(x_41);
lean::dec(x_39);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = l_lean_elaborator_level__get__app__args___main(x_44, x_1, x_2);
if (lean::obj_tag(x_46) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_41);
x_48 = lean::cnstr_get(x_46, 0);
if (lean::is_exclusive(x_46)) {
 x_50 = x_46;
} else {
 lean::inc(x_48);
 lean::dec(x_46);
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
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_52 = lean::cnstr_get(x_46, 0);
if (lean::is_exclusive(x_46)) {
 x_54 = x_46;
} else {
 lean::inc(x_52);
 lean::dec(x_46);
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
x_60 = lean::cnstr_get(x_55, 0);
x_62 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 x_64 = x_55;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_55);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_41, 1);
lean::inc(x_65);
lean::dec(x_41);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set(x_68, 1, x_62);
if (lean::is_scalar(x_64)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_64;
}
lean::cnstr_set(x_69, 0, x_60);
lean::cnstr_set(x_69, 1, x_68);
if (lean::is_scalar(x_59)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_59;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_57);
if (lean::is_scalar(x_54)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_54;
}
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
}
else
{
obj* x_73; obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_39);
x_73 = lean::box(0);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_0);
lean::cnstr_set(x_74, 1, x_73);
lean::inc(x_2);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_2);
x_77 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
obj* x_79; obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_15);
x_79 = lean::box(0);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_0);
lean::cnstr_set(x_80, 1, x_79);
lean::inc(x_2);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_2);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
return x_83;
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
lean::dec(x_1);
lean::dec(x_2);
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
obj* l_lean_elaborator_level__get__app__args___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_level__get__app__args___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* l_lean_elaborator_level__get__app__args___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_level__get__app__args(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
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
x_12 = l_lean_elaborator_to__level___main(x_7, x_1, x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_9);
lean::dec(x_11);
x_15 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_17 = x_12;
} else {
 lean::inc(x_15);
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
obj* x_19; obj* x_22; obj* x_24; obj* x_27; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_9, x_1, x_24);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_11);
lean::dec(x_22);
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
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_35 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_37 = x_27;
} else {
 lean::inc(x_35);
 lean::dec(x_27);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_35, 0);
x_40 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_42 = x_35;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_35);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_11;
}
lean::cnstr_set(x_43, 0, x_22);
lean::cnstr_set(x_43, 1, x_38);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_40);
if (lean::is_scalar(x_37)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_37;
}
lean::cnstr_set(x_45, 0, x_44);
return x_45;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
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
x_12 = l_lean_elaborator_to__level___main(x_7, x_1, x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_9);
lean::dec(x_11);
x_15 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_17 = x_12;
} else {
 lean::inc(x_15);
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
obj* x_19; obj* x_22; obj* x_24; obj* x_27; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_9, x_1, x_24);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_11);
lean::dec(x_22);
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
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_35 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_37 = x_27;
} else {
 lean::inc(x_35);
 lean::dec(x_27);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_35, 0);
x_40 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_42 = x_35;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_35);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_11;
}
lean::cnstr_set(x_43, 0, x_22);
lean::cnstr_set(x_43, 1, x_38);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_40);
if (lean::is_scalar(x_37)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_37;
}
lean::cnstr_set(x_45, 0, x_44);
return x_45;
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
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_2, x_1);
return x_3;
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
obj* x_4; 
lean::inc(x_0);
x_4 = l_lean_elaborator_level__get__app__args___main(x_0, x_1, x_2);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_18; obj* x_20; obj* x_22; obj* x_23; 
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
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::dec(x_10);
x_18 = lean::cnstr_get(x_13, 0);
x_20 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 lean::cnstr_set(x_13, 1, lean::box(0));
 x_22 = x_13;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
x_23 = l_lean_parser_syntax_kind___main(x_18);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_36; 
lean::dec(x_12);
lean::dec(x_22);
lean::dec(x_18);
lean::dec(x_20);
lean::inc(x_0);
x_29 = l_lean_parser_syntax_to__format___main(x_0);
x_30 = lean::mk_nat_obj(80u);
x_31 = l_lean_format_pretty(x_29, x_30);
lean::dec(x_29);
x_33 = l_lean_elaborator_to__level___main___closed__1;
x_34 = lean::string_append(x_33, x_31);
lean::dec(x_31);
x_36 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_34, x_1, x_15);
lean::dec(x_15);
lean::dec(x_34);
lean::dec(x_0);
return x_36;
}
else
{
obj* x_40; obj* x_43; uint8 x_44; 
x_40 = lean::cnstr_get(x_23, 0);
lean::inc(x_40);
lean::dec(x_23);
x_43 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_44 = lean_name_dec_eq(x_40, x_43);
if (x_44 == 0)
{
obj* x_47; uint8 x_48; 
lean::dec(x_12);
lean::dec(x_22);
x_47 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_48 = lean_name_dec_eq(x_40, x_47);
lean::dec(x_40);
if (x_48 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_18);
lean::dec(x_20);
lean::inc(x_0);
x_53 = l_lean_parser_syntax_to__format___main(x_0);
x_54 = lean::mk_nat_obj(80u);
x_55 = l_lean_format_pretty(x_53, x_54);
lean::dec(x_53);
x_57 = l_lean_elaborator_to__level___main___closed__1;
x_58 = lean::string_append(x_57, x_55);
lean::dec(x_55);
x_60 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_58, x_1, x_15);
lean::dec(x_15);
lean::dec(x_58);
lean::dec(x_0);
return x_60;
}
else
{
obj* x_64; obj* x_65; obj* x_68; 
x_64 = l_lean_parser_level_trailing_has__view;
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
lean::dec(x_64);
x_68 = lean::apply_1(x_65, x_18);
if (lean::obj_tag(x_68) == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_68);
lean::dec(x_20);
x_71 = l_lean_elaborator_to__level___main___closed__2;
x_72 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_71, x_1, x_15);
lean::dec(x_15);
lean::dec(x_0);
return x_72;
}
else
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_76; obj* x_79; obj* x_81; 
lean::dec(x_0);
x_76 = lean::cnstr_get(x_68, 0);
lean::inc(x_76);
lean::dec(x_68);
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
x_81 = l_lean_elaborator_to__level___main(x_79, x_1, x_15);
lean::dec(x_15);
if (lean::obj_tag(x_81) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_76);
x_84 = lean::cnstr_get(x_81, 0);
if (lean::is_exclusive(x_81)) {
 x_86 = x_81;
} else {
 lean::inc(x_84);
 lean::dec(x_81);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
return x_87;
}
else
{
obj* x_88; obj* x_90; obj* x_91; obj* x_93; obj* x_95; obj* x_96; obj* x_99; obj* x_100; obj* x_103; obj* x_104; 
x_88 = lean::cnstr_get(x_81, 0);
if (lean::is_exclusive(x_81)) {
 x_90 = x_81;
} else {
 lean::inc(x_88);
 lean::dec(x_81);
 x_90 = lean::box(0);
}
x_91 = lean::cnstr_get(x_88, 0);
x_93 = lean::cnstr_get(x_88, 1);
if (lean::is_exclusive(x_88)) {
 x_95 = x_88;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_88);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_76, 2);
lean::inc(x_96);
lean::dec(x_76);
x_99 = l_lean_parser_number_view_to__nat___main(x_96);
x_100 = l_lean_elaborator_level__add___main(x_91, x_99);
lean::dec(x_99);
lean::dec(x_91);
if (lean::is_scalar(x_95)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_95;
}
lean::cnstr_set(x_103, 0, x_100);
lean::cnstr_set(x_103, 1, x_93);
if (lean::is_scalar(x_90)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_90;
}
lean::cnstr_set(x_104, 0, x_103);
return x_104;
}
}
else
{
obj* x_107; obj* x_108; 
lean::dec(x_68);
lean::dec(x_20);
x_107 = l_lean_elaborator_to__level___main___closed__2;
x_108 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_107, x_1, x_15);
lean::dec(x_15);
lean::dec(x_0);
return x_108;
}
}
}
}
else
{
obj* x_112; obj* x_113; obj* x_116; 
lean::dec(x_40);
x_112 = l_lean_parser_level_leading_has__view;
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
lean::dec(x_112);
x_116 = lean::apply_1(x_113, x_18);
switch (lean::obj_tag(x_116)) {
case 0:
{
lean::dec(x_12);
lean::dec(x_22);
lean::dec(x_116);
if (lean::obj_tag(x_20) == 0)
{
obj* x_120; obj* x_121; 
x_120 = l_lean_elaborator_to__level___main___closed__2;
x_121 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_120, x_1, x_15);
lean::dec(x_15);
lean::dec(x_0);
return x_121;
}
else
{
obj* x_125; obj* x_127; obj* x_130; 
lean::dec(x_0);
x_125 = lean::cnstr_get(x_20, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_20, 1);
lean::inc(x_127);
lean::dec(x_20);
x_130 = l_lean_elaborator_to__level___main(x_125, x_1, x_15);
lean::dec(x_15);
if (lean::obj_tag(x_130) == 0)
{
obj* x_133; obj* x_135; obj* x_136; 
lean::dec(x_127);
x_133 = lean::cnstr_get(x_130, 0);
if (lean::is_exclusive(x_130)) {
 x_135 = x_130;
} else {
 lean::inc(x_133);
 lean::dec(x_130);
 x_135 = lean::box(0);
}
if (lean::is_scalar(x_135)) {
 x_136 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_136 = x_135;
}
lean::cnstr_set(x_136, 0, x_133);
return x_136;
}
else
{
obj* x_137; obj* x_140; obj* x_142; obj* x_145; 
x_137 = lean::cnstr_get(x_130, 0);
lean::inc(x_137);
lean::dec(x_130);
x_140 = lean::cnstr_get(x_137, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_137, 1);
lean::inc(x_142);
lean::dec(x_137);
x_145 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_127, x_1, x_142);
lean::dec(x_142);
if (lean::obj_tag(x_145) == 0)
{
obj* x_148; obj* x_150; obj* x_151; 
lean::dec(x_140);
x_148 = lean::cnstr_get(x_145, 0);
if (lean::is_exclusive(x_145)) {
 x_150 = x_145;
} else {
 lean::inc(x_148);
 lean::dec(x_145);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
return x_151;
}
else
{
obj* x_152; obj* x_154; obj* x_155; obj* x_157; obj* x_159; obj* x_160; obj* x_162; obj* x_163; 
x_152 = lean::cnstr_get(x_145, 0);
if (lean::is_exclusive(x_145)) {
 x_154 = x_145;
} else {
 lean::inc(x_152);
 lean::dec(x_145);
 x_154 = lean::box(0);
}
x_155 = lean::cnstr_get(x_152, 0);
x_157 = lean::cnstr_get(x_152, 1);
if (lean::is_exclusive(x_152)) {
 x_159 = x_152;
} else {
 lean::inc(x_155);
 lean::inc(x_157);
 lean::dec(x_152);
 x_159 = lean::box(0);
}
x_160 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(x_140, x_155);
lean::dec(x_140);
if (lean::is_scalar(x_159)) {
 x_162 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_162 = x_159;
}
lean::cnstr_set(x_162, 0, x_160);
lean::cnstr_set(x_162, 1, x_157);
if (lean::is_scalar(x_154)) {
 x_163 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_163 = x_154;
}
lean::cnstr_set(x_163, 0, x_162);
return x_163;
}
}
}
}
case 1:
{
lean::dec(x_12);
lean::dec(x_22);
lean::dec(x_116);
if (lean::obj_tag(x_20) == 0)
{
obj* x_167; obj* x_168; 
x_167 = l_lean_elaborator_to__level___main___closed__2;
x_168 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_167, x_1, x_15);
lean::dec(x_15);
lean::dec(x_0);
return x_168;
}
else
{
obj* x_172; obj* x_174; obj* x_177; 
lean::dec(x_0);
x_172 = lean::cnstr_get(x_20, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_20, 1);
lean::inc(x_174);
lean::dec(x_20);
x_177 = l_lean_elaborator_to__level___main(x_172, x_1, x_15);
lean::dec(x_15);
if (lean::obj_tag(x_177) == 0)
{
obj* x_180; obj* x_182; obj* x_183; 
lean::dec(x_174);
x_180 = lean::cnstr_get(x_177, 0);
if (lean::is_exclusive(x_177)) {
 x_182 = x_177;
} else {
 lean::inc(x_180);
 lean::dec(x_177);
 x_182 = lean::box(0);
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_180);
return x_183;
}
else
{
obj* x_184; obj* x_187; obj* x_189; obj* x_192; 
x_184 = lean::cnstr_get(x_177, 0);
lean::inc(x_184);
lean::dec(x_177);
x_187 = lean::cnstr_get(x_184, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_184, 1);
lean::inc(x_189);
lean::dec(x_184);
x_192 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_174, x_1, x_189);
lean::dec(x_189);
if (lean::obj_tag(x_192) == 0)
{
obj* x_195; obj* x_197; obj* x_198; 
lean::dec(x_187);
x_195 = lean::cnstr_get(x_192, 0);
if (lean::is_exclusive(x_192)) {
 x_197 = x_192;
} else {
 lean::inc(x_195);
 lean::dec(x_192);
 x_197 = lean::box(0);
}
if (lean::is_scalar(x_197)) {
 x_198 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_198 = x_197;
}
lean::cnstr_set(x_198, 0, x_195);
return x_198;
}
else
{
obj* x_199; obj* x_201; obj* x_202; obj* x_204; obj* x_206; obj* x_207; obj* x_209; obj* x_210; 
x_199 = lean::cnstr_get(x_192, 0);
if (lean::is_exclusive(x_192)) {
 x_201 = x_192;
} else {
 lean::inc(x_199);
 lean::dec(x_192);
 x_201 = lean::box(0);
}
x_202 = lean::cnstr_get(x_199, 0);
x_204 = lean::cnstr_get(x_199, 1);
if (lean::is_exclusive(x_199)) {
 x_206 = x_199;
} else {
 lean::inc(x_202);
 lean::inc(x_204);
 lean::dec(x_199);
 x_206 = lean::box(0);
}
x_207 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(x_187, x_202);
lean::dec(x_187);
if (lean::is_scalar(x_206)) {
 x_209 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_209 = x_206;
}
lean::cnstr_set(x_209, 0, x_207);
lean::cnstr_set(x_209, 1, x_204);
if (lean::is_scalar(x_201)) {
 x_210 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_210 = x_201;
}
lean::cnstr_set(x_210, 0, x_209);
return x_210;
}
}
}
}
case 2:
{
lean::dec(x_116);
if (lean::obj_tag(x_20) == 0)
{
obj* x_213; obj* x_214; obj* x_215; 
lean::dec(x_0);
x_213 = l_lean_elaborator_to__level___main___closed__3;
if (lean::is_scalar(x_22)) {
 x_214 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_214 = x_22;
}
lean::cnstr_set(x_214, 0, x_213);
lean::cnstr_set(x_214, 1, x_15);
if (lean::is_scalar(x_12)) {
 x_215 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_215 = x_12;
}
lean::cnstr_set(x_215, 0, x_214);
return x_215;
}
else
{
obj* x_219; obj* x_220; 
lean::dec(x_12);
lean::dec(x_22);
lean::dec(x_20);
x_219 = l_lean_elaborator_to__level___main___closed__2;
x_220 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_219, x_1, x_15);
lean::dec(x_15);
lean::dec(x_0);
return x_220;
}
}
case 3:
{
obj* x_227; obj* x_228; 
lean::dec(x_12);
lean::dec(x_22);
lean::dec(x_20);
lean::dec(x_116);
x_227 = l_lean_elaborator_to__level___main___closed__2;
x_228 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_227, x_1, x_15);
lean::dec(x_15);
lean::dec(x_0);
return x_228;
}
case 4:
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_232; obj* x_235; obj* x_236; obj* x_238; obj* x_239; 
lean::dec(x_0);
x_232 = lean::cnstr_get(x_116, 0);
lean::inc(x_232);
lean::dec(x_116);
x_235 = l_lean_parser_number_view_to__nat___main(x_232);
x_236 = l_lean_level_of__nat___main(x_235);
lean::dec(x_235);
if (lean::is_scalar(x_22)) {
 x_238 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_238 = x_22;
}
lean::cnstr_set(x_238, 0, x_236);
lean::cnstr_set(x_238, 1, x_15);
if (lean::is_scalar(x_12)) {
 x_239 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_239 = x_12;
}
lean::cnstr_set(x_239, 0, x_238);
return x_239;
}
else
{
obj* x_244; obj* x_245; 
lean::dec(x_12);
lean::dec(x_22);
lean::dec(x_20);
lean::dec(x_116);
x_244 = l_lean_elaborator_to__level___main___closed__2;
x_245 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_244, x_1, x_15);
lean::dec(x_15);
lean::dec(x_0);
return x_245;
}
}
default:
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_248; obj* x_251; obj* x_252; obj* x_254; obj* x_257; 
x_248 = lean::cnstr_get(x_116, 0);
lean::inc(x_248);
lean::dec(x_116);
x_251 = l_lean_elaborator_mangle__ident(x_248);
x_252 = lean::cnstr_get(x_15, 4);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_252, 1);
lean::inc(x_254);
lean::dec(x_252);
x_257 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_254, x_251);
lean::dec(x_254);
if (lean::obj_tag(x_257) == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_266; obj* x_267; obj* x_268; 
lean::dec(x_12);
lean::dec(x_22);
x_261 = l_lean_name_to__string___closed__1;
x_262 = l_lean_name_to__string__with__sep___main(x_261, x_251);
x_263 = l_lean_elaborator_to__level___main___closed__4;
x_264 = lean::string_append(x_263, x_262);
lean::dec(x_262);
x_266 = l_char_has__repr___closed__1;
x_267 = lean::string_append(x_264, x_266);
x_268 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_267, x_1, x_15);
lean::dec(x_15);
lean::dec(x_267);
lean::dec(x_0);
return x_268;
}
else
{
obj* x_274; obj* x_275; obj* x_276; 
lean::dec(x_0);
lean::dec(x_257);
x_274 = level_mk_param(x_251);
if (lean::is_scalar(x_22)) {
 x_275 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_275 = x_22;
}
lean::cnstr_set(x_275, 0, x_274);
lean::cnstr_set(x_275, 1, x_15);
if (lean::is_scalar(x_12)) {
 x_276 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_276 = x_12;
}
lean::cnstr_set(x_276, 0, x_275);
return x_276;
}
}
else
{
obj* x_281; obj* x_282; 
lean::dec(x_12);
lean::dec(x_22);
lean::dec(x_20);
lean::dec(x_116);
x_281 = l_lean_elaborator_to__level___main___closed__2;
x_282 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_281, x_1, x_15);
lean::dec(x_15);
lean::dec(x_0);
return x_282;
}
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_to__level___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_to__level___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* l_lean_elaborator_to__level___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_to__level(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
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
obj* l_lean_elaborator_expr_mk__annotation___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_expr_mk__annotation(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
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
lean::dec(x_7);
x_15 = l_lean_elaborator_to__pexpr___main(x_12, x_1, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
x_18 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_20 = x_15;
} else {
 lean::inc(x_18);
 lean::dec(x_15);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_30; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
lean::dec(x_15);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(x_9, x_1, x_27);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_11);
lean::dec(x_25);
x_34 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_36 = x_30;
} else {
 lean::inc(x_34);
 lean::dec(x_30);
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
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_38 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_40 = x_30;
} else {
 lean::inc(x_38);
 lean::dec(x_30);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_38, 0);
x_43 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 x_45 = x_38;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::dec(x_38);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_11;
}
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_41);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_40)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_40;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; 
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
x_14 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(x_12, x_1, x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
x_18 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_20 = x_14;
} else {
 lean::inc(x_18);
 lean::dec(x_14);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_33; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
lean::dec(x_14);
x_25 = lean::cnstr_get(x_22, 0);
x_27 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 lean::cnstr_set(x_22, 1, lean::box(0));
 x_29 = x_22;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_22);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_7, 2);
lean::inc(x_30);
lean::dec(x_7);
x_33 = l_lean_elaborator_to__pexpr___main(x_30, x_1, x_27);
lean::dec(x_27);
if (lean::obj_tag(x_33) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_25);
lean::dec(x_29);
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
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
obj* x_43; obj* x_46; obj* x_48; obj* x_50; obj* x_51; 
x_43 = lean::cnstr_get(x_33, 0);
lean::inc(x_43);
lean::dec(x_33);
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_set(x_43, 0, lean::box(0));
 lean::cnstr_set(x_43, 1, lean::box(0));
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_9, x_1, x_48);
lean::dec(x_48);
if (lean::obj_tag(x_51) == 0)
{
obj* x_58; obj* x_60; obj* x_61; 
lean::dec(x_11);
lean::dec(x_25);
lean::dec(x_29);
lean::dec(x_46);
lean::dec(x_50);
x_58 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_60 = x_51;
} else {
 lean::inc(x_58);
 lean::dec(x_51);
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
obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_62 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_64 = x_51;
} else {
 lean::inc(x_62);
 lean::dec(x_51);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_62, 0);
x_67 = lean::cnstr_get(x_62, 1);
if (lean::is_exclusive(x_62)) {
 x_69 = x_62;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_62);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_25);
lean::cnstr_set(x_70, 1, x_46);
x_71 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1;
if (lean::is_scalar(x_50)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_50;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_70);
if (lean::is_scalar(x_11)) {
 x_73 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_73 = x_11;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_65);
if (lean::is_scalar(x_29)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_29;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_67);
if (lean::is_scalar(x_64)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_64;
}
lean::cnstr_set(x_75, 0, x_74);
return x_75;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
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
lean::dec(x_7);
x_15 = l_lean_elaborator_to__pexpr___main(x_12, x_1, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
x_18 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_20 = x_15;
} else {
 lean::inc(x_18);
 lean::dec(x_15);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_30; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
lean::dec(x_15);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_9, x_1, x_27);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_11);
lean::dec(x_25);
x_34 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_36 = x_30;
} else {
 lean::inc(x_34);
 lean::dec(x_30);
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
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_38 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_40 = x_30;
} else {
 lean::inc(x_38);
 lean::dec(x_30);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_38, 0);
x_43 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 x_45 = x_38;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::dec(x_38);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_11;
}
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_41);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_40)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_40;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
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
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
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
obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_21; 
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
x_21 = l_lean_elaborator_to__pexpr___main(x_19, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_16);
x_25 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_27 = x_21;
} else {
 lean::inc(x_25);
 lean::dec(x_21);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_21, 0);
lean::inc(x_29);
lean::dec(x_21);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_13, x_2, x_34);
lean::dec(x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_32);
lean::dec(x_15);
lean::dec(x_16);
x_42 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_42);
 lean::dec(x_37);
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
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_46 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_48 = x_37;
} else {
 lean::inc(x_46);
 lean::dec(x_37);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_46, 0);
x_51 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 x_53 = x_46;
} else {
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_46);
 x_53 = lean::box(0);
}
x_54 = lean::box(0);
x_55 = lean::cnstr_get(x_16, 0);
lean::inc(x_55);
lean::dec(x_16);
x_58 = l_lean_elaborator_mangle__ident(x_55);
x_59 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_60 = l_lean_kvmap_set__name(x_54, x_59, x_58);
lean::dec(x_58);
x_62 = lean_expr_mk_mdata(x_60, x_32);
if (lean::is_scalar(x_15)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_15;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_49);
if (lean::is_scalar(x_53)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_53;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_51);
if (lean::is_scalar(x_48)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_48;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
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
x_71 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_67);
lean::dec(x_69);
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
obj* x_78; obj* x_81; obj* x_83; obj* x_86; 
x_78 = lean::cnstr_get(x_71, 0);
lean::inc(x_78);
lean::dec(x_71);
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 1);
lean::inc(x_83);
lean::dec(x_78);
x_86 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_67, x_2, x_83);
lean::dec(x_83);
if (lean::obj_tag(x_86) == 0)
{
obj* x_90; obj* x_92; obj* x_93; 
lean::dec(x_69);
lean::dec(x_81);
x_90 = lean::cnstr_get(x_86, 0);
if (lean::is_exclusive(x_86)) {
 x_92 = x_86;
} else {
 lean::inc(x_90);
 lean::dec(x_86);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
return x_93;
}
else
{
obj* x_94; obj* x_96; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_94 = lean::cnstr_get(x_86, 0);
if (lean::is_exclusive(x_86)) {
 x_96 = x_86;
} else {
 lean::inc(x_94);
 lean::dec(x_86);
 x_96 = lean::box(0);
}
x_97 = lean::cnstr_get(x_94, 0);
x_99 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 x_101 = x_94;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_94);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_102 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_102 = x_69;
}
lean::cnstr_set(x_102, 0, x_81);
lean::cnstr_set(x_102, 1, x_97);
if (lean::is_scalar(x_101)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_101;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_99);
if (lean::is_scalar(x_96)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_96;
}
lean::cnstr_set(x_104, 0, x_103);
return x_104;
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
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
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
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
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
x_18 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_17, x_2, x_3);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_14);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_23 = x_18;
} else {
 lean::inc(x_21);
 lean::dec(x_18);
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
obj* x_25; obj* x_28; obj* x_30; obj* x_33; 
x_25 = lean::cnstr_get(x_18, 0);
lean::inc(x_25);
lean::dec(x_18);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_14, x_2, x_30);
lean::dec(x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_28);
lean::dec(x_16);
x_37 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_39 = x_33;
} else {
 lean::inc(x_37);
 lean::dec(x_33);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_43 = x_33;
} else {
 lean::inc(x_41);
 lean::dec(x_33);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_41, 0);
x_46 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 x_48 = x_41;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_41);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_16;
}
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_44);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
if (lean::is_scalar(x_43)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_43;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
obj* x_52; obj* x_55; 
x_52 = lean::cnstr_get(x_10, 0);
lean::inc(x_52);
lean::dec(x_10);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
x_58 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_60 = x_1;
} else {
 lean::inc(x_58);
 lean::dec(x_1);
 x_60 = lean::box(0);
}
x_61 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
x_62 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_61, x_2, x_3);
if (lean::obj_tag(x_62) == 0)
{
obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_60);
lean::dec(x_58);
x_65 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_67 = x_62;
} else {
 lean::inc(x_65);
 lean::dec(x_62);
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
obj* x_69; obj* x_72; obj* x_74; obj* x_77; 
x_69 = lean::cnstr_get(x_62, 0);
lean::inc(x_69);
lean::dec(x_62);
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
x_77 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_58, x_2, x_74);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_60);
lean::dec(x_72);
x_81 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_83 = x_77;
} else {
 lean::inc(x_81);
 lean::dec(x_77);
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
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_85 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_87 = x_77;
} else {
 lean::inc(x_85);
 lean::dec(x_77);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_85, 0);
x_90 = lean::cnstr_get(x_85, 1);
if (lean::is_exclusive(x_85)) {
 x_92 = x_85;
} else {
 lean::inc(x_88);
 lean::inc(x_90);
 lean::dec(x_85);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_93 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_93 = x_60;
}
lean::cnstr_set(x_93, 0, x_72);
lean::cnstr_set(x_93, 1, x_88);
if (lean::is_scalar(x_92)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_92;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_90);
if (lean::is_scalar(x_87)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_87;
}
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
obj* x_96; obj* x_98; obj* x_99; obj* x_102; 
x_96 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_98 = x_1;
} else {
 lean::inc(x_96);
 lean::dec(x_1);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_55, 0);
lean::inc(x_99);
lean::dec(x_55);
x_102 = l_lean_elaborator_to__pexpr___main(x_99, x_2, x_3);
if (lean::obj_tag(x_102) == 0)
{
obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_96);
lean::dec(x_98);
x_105 = lean::cnstr_get(x_102, 0);
if (lean::is_exclusive(x_102)) {
 x_107 = x_102;
} else {
 lean::inc(x_105);
 lean::dec(x_102);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
return x_108;
}
else
{
obj* x_109; obj* x_112; obj* x_114; obj* x_117; 
x_109 = lean::cnstr_get(x_102, 0);
lean::inc(x_109);
lean::dec(x_102);
x_112 = lean::cnstr_get(x_109, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_109, 1);
lean::inc(x_114);
lean::dec(x_109);
x_117 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_96, x_2, x_114);
lean::dec(x_114);
if (lean::obj_tag(x_117) == 0)
{
obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_112);
lean::dec(x_98);
x_121 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_123 = x_117;
} else {
 lean::inc(x_121);
 lean::dec(x_117);
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
x_125 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_127 = x_117;
} else {
 lean::inc(x_125);
 lean::dec(x_117);
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
if (lean::is_scalar(x_98)) {
 x_133 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_133 = x_98;
}
lean::cnstr_set(x_133, 0, x_112);
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
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
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
obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_21; 
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
x_21 = l_lean_elaborator_to__pexpr___main(x_19, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_16);
x_25 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_27 = x_21;
} else {
 lean::inc(x_25);
 lean::dec(x_21);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_21, 0);
lean::inc(x_29);
lean::dec(x_21);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_13, x_2, x_34);
lean::dec(x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_32);
lean::dec(x_15);
lean::dec(x_16);
x_42 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_42);
 lean::dec(x_37);
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
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_46 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_48 = x_37;
} else {
 lean::inc(x_46);
 lean::dec(x_37);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_46, 0);
x_51 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 x_53 = x_46;
} else {
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_46);
 x_53 = lean::box(0);
}
x_54 = lean::box(0);
x_55 = lean::cnstr_get(x_16, 0);
lean::inc(x_55);
lean::dec(x_16);
x_58 = l_lean_elaborator_mangle__ident(x_55);
x_59 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_60 = l_lean_kvmap_set__name(x_54, x_59, x_58);
lean::dec(x_58);
x_62 = lean_expr_mk_mdata(x_60, x_32);
if (lean::is_scalar(x_15)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_15;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_49);
if (lean::is_scalar(x_53)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_53;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_51);
if (lean::is_scalar(x_48)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_48;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
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
x_71 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_67);
lean::dec(x_69);
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
obj* x_78; obj* x_81; obj* x_83; obj* x_86; 
x_78 = lean::cnstr_get(x_71, 0);
lean::inc(x_78);
lean::dec(x_71);
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 1);
lean::inc(x_83);
lean::dec(x_78);
x_86 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_67, x_2, x_83);
lean::dec(x_83);
if (lean::obj_tag(x_86) == 0)
{
obj* x_90; obj* x_92; obj* x_93; 
lean::dec(x_69);
lean::dec(x_81);
x_90 = lean::cnstr_get(x_86, 0);
if (lean::is_exclusive(x_86)) {
 x_92 = x_86;
} else {
 lean::inc(x_90);
 lean::dec(x_86);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
return x_93;
}
else
{
obj* x_94; obj* x_96; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_94 = lean::cnstr_get(x_86, 0);
if (lean::is_exclusive(x_86)) {
 x_96 = x_86;
} else {
 lean::inc(x_94);
 lean::dec(x_86);
 x_96 = lean::box(0);
}
x_97 = lean::cnstr_get(x_94, 0);
x_99 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 x_101 = x_94;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_94);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_102 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_102 = x_69;
}
lean::cnstr_set(x_102, 0, x_81);
lean::cnstr_set(x_102, 1, x_97);
if (lean::is_scalar(x_101)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_101;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_99);
if (lean::is_scalar(x_96)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_96;
}
lean::cnstr_set(x_104, 0, x_103);
return x_104;
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
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
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
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
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
x_18 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_17, x_2, x_3);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_14);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_23 = x_18;
} else {
 lean::inc(x_21);
 lean::dec(x_18);
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
obj* x_25; obj* x_28; obj* x_30; obj* x_33; 
x_25 = lean::cnstr_get(x_18, 0);
lean::inc(x_25);
lean::dec(x_18);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_14, x_2, x_30);
lean::dec(x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_28);
lean::dec(x_16);
x_37 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_39 = x_33;
} else {
 lean::inc(x_37);
 lean::dec(x_33);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_43 = x_33;
} else {
 lean::inc(x_41);
 lean::dec(x_33);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_41, 0);
x_46 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 x_48 = x_41;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_41);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_16;
}
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_44);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
if (lean::is_scalar(x_43)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_43;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
obj* x_52; obj* x_55; 
x_52 = lean::cnstr_get(x_10, 0);
lean::inc(x_52);
lean::dec(x_10);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
x_58 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_60 = x_1;
} else {
 lean::inc(x_58);
 lean::dec(x_1);
 x_60 = lean::box(0);
}
x_61 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
x_62 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_61, x_2, x_3);
if (lean::obj_tag(x_62) == 0)
{
obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_60);
lean::dec(x_58);
x_65 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_67 = x_62;
} else {
 lean::inc(x_65);
 lean::dec(x_62);
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
obj* x_69; obj* x_72; obj* x_74; obj* x_77; 
x_69 = lean::cnstr_get(x_62, 0);
lean::inc(x_69);
lean::dec(x_62);
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
x_77 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_58, x_2, x_74);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_60);
lean::dec(x_72);
x_81 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_83 = x_77;
} else {
 lean::inc(x_81);
 lean::dec(x_77);
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
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_85 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_87 = x_77;
} else {
 lean::inc(x_85);
 lean::dec(x_77);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_85, 0);
x_90 = lean::cnstr_get(x_85, 1);
if (lean::is_exclusive(x_85)) {
 x_92 = x_85;
} else {
 lean::inc(x_88);
 lean::inc(x_90);
 lean::dec(x_85);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_93 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_93 = x_60;
}
lean::cnstr_set(x_93, 0, x_72);
lean::cnstr_set(x_93, 1, x_88);
if (lean::is_scalar(x_92)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_92;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_90);
if (lean::is_scalar(x_87)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_87;
}
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
obj* x_96; obj* x_98; obj* x_99; obj* x_102; 
x_96 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_98 = x_1;
} else {
 lean::inc(x_96);
 lean::dec(x_1);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_55, 0);
lean::inc(x_99);
lean::dec(x_55);
x_102 = l_lean_elaborator_to__pexpr___main(x_99, x_2, x_3);
if (lean::obj_tag(x_102) == 0)
{
obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_96);
lean::dec(x_98);
x_105 = lean::cnstr_get(x_102, 0);
if (lean::is_exclusive(x_102)) {
 x_107 = x_102;
} else {
 lean::inc(x_105);
 lean::dec(x_102);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
return x_108;
}
else
{
obj* x_109; obj* x_112; obj* x_114; obj* x_117; 
x_109 = lean::cnstr_get(x_102, 0);
lean::inc(x_109);
lean::dec(x_102);
x_112 = lean::cnstr_get(x_109, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_109, 1);
lean::inc(x_114);
lean::dec(x_109);
x_117 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_96, x_2, x_114);
lean::dec(x_114);
if (lean::obj_tag(x_117) == 0)
{
obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_112);
lean::dec(x_98);
x_121 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_123 = x_117;
} else {
 lean::inc(x_121);
 lean::dec(x_117);
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
x_125 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_127 = x_117;
} else {
 lean::inc(x_125);
 lean::dec(x_117);
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
if (lean::is_scalar(x_98)) {
 x_133 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_133 = x_98;
}
lean::cnstr_set(x_133, 0, x_112);
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
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
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
obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_21; 
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
x_21 = l_lean_elaborator_to__pexpr___main(x_19, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_16);
x_25 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_27 = x_21;
} else {
 lean::inc(x_25);
 lean::dec(x_21);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_21, 0);
lean::inc(x_29);
lean::dec(x_21);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_13, x_2, x_34);
lean::dec(x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_32);
lean::dec(x_15);
lean::dec(x_16);
x_42 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_42);
 lean::dec(x_37);
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
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_46 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_48 = x_37;
} else {
 lean::inc(x_46);
 lean::dec(x_37);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_46, 0);
x_51 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 x_53 = x_46;
} else {
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_46);
 x_53 = lean::box(0);
}
x_54 = lean::box(0);
x_55 = lean::cnstr_get(x_16, 0);
lean::inc(x_55);
lean::dec(x_16);
x_58 = l_lean_elaborator_mangle__ident(x_55);
x_59 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_60 = l_lean_kvmap_set__name(x_54, x_59, x_58);
lean::dec(x_58);
x_62 = lean_expr_mk_mdata(x_60, x_32);
if (lean::is_scalar(x_15)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_15;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_49);
if (lean::is_scalar(x_53)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_53;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_51);
if (lean::is_scalar(x_48)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_48;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
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
x_71 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_67);
lean::dec(x_69);
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
obj* x_78; obj* x_81; obj* x_83; obj* x_86; 
x_78 = lean::cnstr_get(x_71, 0);
lean::inc(x_78);
lean::dec(x_71);
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 1);
lean::inc(x_83);
lean::dec(x_78);
x_86 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_67, x_2, x_83);
lean::dec(x_83);
if (lean::obj_tag(x_86) == 0)
{
obj* x_90; obj* x_92; obj* x_93; 
lean::dec(x_69);
lean::dec(x_81);
x_90 = lean::cnstr_get(x_86, 0);
if (lean::is_exclusive(x_86)) {
 x_92 = x_86;
} else {
 lean::inc(x_90);
 lean::dec(x_86);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
return x_93;
}
else
{
obj* x_94; obj* x_96; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_94 = lean::cnstr_get(x_86, 0);
if (lean::is_exclusive(x_86)) {
 x_96 = x_86;
} else {
 lean::inc(x_94);
 lean::dec(x_86);
 x_96 = lean::box(0);
}
x_97 = lean::cnstr_get(x_94, 0);
x_99 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 x_101 = x_94;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_94);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_102 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_102 = x_69;
}
lean::cnstr_set(x_102, 0, x_81);
lean::cnstr_set(x_102, 1, x_97);
if (lean::is_scalar(x_101)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_101;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_99);
if (lean::is_scalar(x_96)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_96;
}
lean::cnstr_set(x_104, 0, x_103);
return x_104;
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
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
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
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
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
x_18 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_17, x_2, x_3);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_14);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_23 = x_18;
} else {
 lean::inc(x_21);
 lean::dec(x_18);
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
obj* x_25; obj* x_28; obj* x_30; obj* x_33; 
x_25 = lean::cnstr_get(x_18, 0);
lean::inc(x_25);
lean::dec(x_18);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_14, x_2, x_30);
lean::dec(x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_28);
lean::dec(x_16);
x_37 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_39 = x_33;
} else {
 lean::inc(x_37);
 lean::dec(x_33);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_43 = x_33;
} else {
 lean::inc(x_41);
 lean::dec(x_33);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_41, 0);
x_46 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 x_48 = x_41;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_41);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_16;
}
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_44);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
if (lean::is_scalar(x_43)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_43;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
obj* x_52; obj* x_55; 
x_52 = lean::cnstr_get(x_10, 0);
lean::inc(x_52);
lean::dec(x_10);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
x_58 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_60 = x_1;
} else {
 lean::inc(x_58);
 lean::dec(x_1);
 x_60 = lean::box(0);
}
x_61 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
x_62 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_61, x_2, x_3);
if (lean::obj_tag(x_62) == 0)
{
obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_60);
lean::dec(x_58);
x_65 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_67 = x_62;
} else {
 lean::inc(x_65);
 lean::dec(x_62);
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
obj* x_69; obj* x_72; obj* x_74; obj* x_77; 
x_69 = lean::cnstr_get(x_62, 0);
lean::inc(x_69);
lean::dec(x_62);
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
x_77 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_58, x_2, x_74);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_60);
lean::dec(x_72);
x_81 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_83 = x_77;
} else {
 lean::inc(x_81);
 lean::dec(x_77);
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
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_85 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_87 = x_77;
} else {
 lean::inc(x_85);
 lean::dec(x_77);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_85, 0);
x_90 = lean::cnstr_get(x_85, 1);
if (lean::is_exclusive(x_85)) {
 x_92 = x_85;
} else {
 lean::inc(x_88);
 lean::inc(x_90);
 lean::dec(x_85);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_93 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_93 = x_60;
}
lean::cnstr_set(x_93, 0, x_72);
lean::cnstr_set(x_93, 1, x_88);
if (lean::is_scalar(x_92)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_92;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_90);
if (lean::is_scalar(x_87)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_87;
}
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
obj* x_96; obj* x_98; obj* x_99; obj* x_102; 
x_96 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_98 = x_1;
} else {
 lean::inc(x_96);
 lean::dec(x_1);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_55, 0);
lean::inc(x_99);
lean::dec(x_55);
x_102 = l_lean_elaborator_to__pexpr___main(x_99, x_2, x_3);
if (lean::obj_tag(x_102) == 0)
{
obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_96);
lean::dec(x_98);
x_105 = lean::cnstr_get(x_102, 0);
if (lean::is_exclusive(x_102)) {
 x_107 = x_102;
} else {
 lean::inc(x_105);
 lean::dec(x_102);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
return x_108;
}
else
{
obj* x_109; obj* x_112; obj* x_114; obj* x_117; 
x_109 = lean::cnstr_get(x_102, 0);
lean::inc(x_109);
lean::dec(x_102);
x_112 = lean::cnstr_get(x_109, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_109, 1);
lean::inc(x_114);
lean::dec(x_109);
x_117 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_96, x_2, x_114);
lean::dec(x_114);
if (lean::obj_tag(x_117) == 0)
{
obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_112);
lean::dec(x_98);
x_121 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_123 = x_117;
} else {
 lean::inc(x_121);
 lean::dec(x_117);
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
x_125 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_127 = x_117;
} else {
 lean::inc(x_125);
 lean::dec(x_117);
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
if (lean::is_scalar(x_98)) {
 x_133 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_133 = x_98;
}
lean::cnstr_set(x_133, 0, x_112);
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
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
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
obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_21; 
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
x_21 = l_lean_elaborator_to__pexpr___main(x_19, x_2, x_3);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_16);
x_25 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_27 = x_21;
} else {
 lean::inc(x_25);
 lean::dec(x_21);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_21, 0);
lean::inc(x_29);
lean::dec(x_21);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_13, x_2, x_34);
lean::dec(x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_32);
lean::dec(x_15);
lean::dec(x_16);
x_42 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_42);
 lean::dec(x_37);
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
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_46 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_48 = x_37;
} else {
 lean::inc(x_46);
 lean::dec(x_37);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_46, 0);
x_51 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 x_53 = x_46;
} else {
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_46);
 x_53 = lean::box(0);
}
x_54 = lean::box(0);
x_55 = lean::cnstr_get(x_16, 0);
lean::inc(x_55);
lean::dec(x_16);
x_58 = l_lean_elaborator_mangle__ident(x_55);
x_59 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_60 = l_lean_kvmap_set__name(x_54, x_59, x_58);
lean::dec(x_58);
x_62 = lean_expr_mk_mdata(x_60, x_32);
if (lean::is_scalar(x_15)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_15;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_49);
if (lean::is_scalar(x_53)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_53;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_51);
if (lean::is_scalar(x_48)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_48;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
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
x_71 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_70, x_2, x_3);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_67);
lean::dec(x_69);
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
obj* x_78; obj* x_81; obj* x_83; obj* x_86; 
x_78 = lean::cnstr_get(x_71, 0);
lean::inc(x_78);
lean::dec(x_71);
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 1);
lean::inc(x_83);
lean::dec(x_78);
x_86 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_67, x_2, x_83);
lean::dec(x_83);
if (lean::obj_tag(x_86) == 0)
{
obj* x_90; obj* x_92; obj* x_93; 
lean::dec(x_69);
lean::dec(x_81);
x_90 = lean::cnstr_get(x_86, 0);
if (lean::is_exclusive(x_86)) {
 x_92 = x_86;
} else {
 lean::inc(x_90);
 lean::dec(x_86);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
return x_93;
}
else
{
obj* x_94; obj* x_96; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_94 = lean::cnstr_get(x_86, 0);
if (lean::is_exclusive(x_86)) {
 x_96 = x_86;
} else {
 lean::inc(x_94);
 lean::dec(x_86);
 x_96 = lean::box(0);
}
x_97 = lean::cnstr_get(x_94, 0);
x_99 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 x_101 = x_94;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_94);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_102 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_102 = x_69;
}
lean::cnstr_set(x_102, 0, x_81);
lean::cnstr_set(x_102, 1, x_97);
if (lean::is_scalar(x_101)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_101;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_99);
if (lean::is_scalar(x_96)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_96;
}
lean::cnstr_set(x_104, 0, x_103);
return x_104;
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
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
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
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
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
x_18 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_17, x_2, x_3);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_14);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_23 = x_18;
} else {
 lean::inc(x_21);
 lean::dec(x_18);
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
obj* x_25; obj* x_28; obj* x_30; obj* x_33; 
x_25 = lean::cnstr_get(x_18, 0);
lean::inc(x_25);
lean::dec(x_18);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_14, x_2, x_30);
lean::dec(x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_28);
lean::dec(x_16);
x_37 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_39 = x_33;
} else {
 lean::inc(x_37);
 lean::dec(x_33);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_43 = x_33;
} else {
 lean::inc(x_41);
 lean::dec(x_33);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_41, 0);
x_46 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 x_48 = x_41;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_41);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_16;
}
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_44);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
if (lean::is_scalar(x_43)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_43;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
obj* x_52; obj* x_55; 
x_52 = lean::cnstr_get(x_10, 0);
lean::inc(x_52);
lean::dec(x_10);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
x_58 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_60 = x_1;
} else {
 lean::inc(x_58);
 lean::dec(x_1);
 x_60 = lean::box(0);
}
x_61 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
x_62 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_61, x_2, x_3);
if (lean::obj_tag(x_62) == 0)
{
obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_60);
lean::dec(x_58);
x_65 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_67 = x_62;
} else {
 lean::inc(x_65);
 lean::dec(x_62);
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
obj* x_69; obj* x_72; obj* x_74; obj* x_77; 
x_69 = lean::cnstr_get(x_62, 0);
lean::inc(x_69);
lean::dec(x_62);
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
x_77 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_58, x_2, x_74);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_60);
lean::dec(x_72);
x_81 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_83 = x_77;
} else {
 lean::inc(x_81);
 lean::dec(x_77);
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
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_85 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_87 = x_77;
} else {
 lean::inc(x_85);
 lean::dec(x_77);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_85, 0);
x_90 = lean::cnstr_get(x_85, 1);
if (lean::is_exclusive(x_85)) {
 x_92 = x_85;
} else {
 lean::inc(x_88);
 lean::inc(x_90);
 lean::dec(x_85);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_93 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_93 = x_60;
}
lean::cnstr_set(x_93, 0, x_72);
lean::cnstr_set(x_93, 1, x_88);
if (lean::is_scalar(x_92)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_92;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_90);
if (lean::is_scalar(x_87)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_87;
}
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
}
}
else
{
obj* x_96; obj* x_98; obj* x_99; obj* x_102; 
x_96 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_98 = x_1;
} else {
 lean::inc(x_96);
 lean::dec(x_1);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_55, 0);
lean::inc(x_99);
lean::dec(x_55);
x_102 = l_lean_elaborator_to__pexpr___main(x_99, x_2, x_3);
if (lean::obj_tag(x_102) == 0)
{
obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_96);
lean::dec(x_98);
x_105 = lean::cnstr_get(x_102, 0);
if (lean::is_exclusive(x_102)) {
 x_107 = x_102;
} else {
 lean::inc(x_105);
 lean::dec(x_102);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
return x_108;
}
else
{
obj* x_109; obj* x_112; obj* x_114; obj* x_117; 
x_109 = lean::cnstr_get(x_102, 0);
lean::inc(x_109);
lean::dec(x_102);
x_112 = lean::cnstr_get(x_109, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_109, 1);
lean::inc(x_114);
lean::dec(x_109);
x_117 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_96, x_2, x_114);
lean::dec(x_114);
if (lean::obj_tag(x_117) == 0)
{
obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_112);
lean::dec(x_98);
x_121 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_123 = x_117;
} else {
 lean::inc(x_121);
 lean::dec(x_117);
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
x_125 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_127 = x_117;
} else {
 lean::inc(x_125);
 lean::dec(x_117);
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
if (lean::is_scalar(x_98)) {
 x_133 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_133 = x_98;
}
lean::cnstr_set(x_133, 0, x_112);
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
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
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
x_12 = l_lean_elaborator_to__pexpr___main(x_7, x_1, x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_9);
lean::dec(x_11);
x_15 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_17 = x_12;
} else {
 lean::inc(x_15);
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
obj* x_19; obj* x_22; obj* x_24; obj* x_27; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_9, x_1, x_24);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_11);
lean::dec(x_22);
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
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_35 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_37 = x_27;
} else {
 lean::inc(x_35);
 lean::dec(x_27);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_35, 0);
x_40 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_42 = x_35;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_35);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_11;
}
lean::cnstr_set(x_43, 0, x_22);
lean::cnstr_set(x_43, 1, x_38);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_40);
if (lean::is_scalar(x_37)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_37;
}
lean::cnstr_set(x_45, 0, x_44);
return x_45;
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
lean::dec(x_9);
lean::dec(x_13);
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
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
x_12 = l_lean_elaborator_to__level___main(x_7, x_1, x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_9);
lean::dec(x_11);
x_15 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_17 = x_12;
} else {
 lean::inc(x_15);
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
obj* x_19; obj* x_22; obj* x_24; obj* x_27; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_9, x_1, x_24);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_11);
lean::dec(x_22);
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
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_35 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_37 = x_27;
} else {
 lean::inc(x_35);
 lean::dec(x_27);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_35, 0);
x_40 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_42 = x_35;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_35);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_11;
}
lean::cnstr_set(x_43, 0, x_22);
lean::cnstr_set(x_43, 1, x_38);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_40);
if (lean::is_scalar(x_37)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_37;
}
lean::cnstr_set(x_45, 0, x_44);
return x_45;
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
lean::dec(x_9);
lean::dec(x_13);
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
lean::dec(x_5);
lean::dec(x_3);
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
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_64; 
x_59 = l_lean_name_to__string___closed__1;
x_60 = l_lean_name_to__string__with__sep___main(x_59, x_7);
x_61 = l_lean_elaborator_to__pexpr___main___closed__23;
x_62 = lean::string_append(x_61, x_60);
lean::dec(x_60);
x_64 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_62, x_1, x_2);
lean::dec(x_62);
if (lean::obj_tag(x_64) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_0);
x_67 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_69 = x_64;
} else {
 lean::inc(x_67);
 lean::dec(x_64);
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
obj* x_71; obj* x_73; 
x_71 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_set(x_64, 0, lean::box(0));
 x_73 = x_64;
} else {
 lean::inc(x_71);
 lean::dec(x_64);
 x_73 = lean::box(0);
}
if (x_21 == 0)
{
obj* x_74; obj* x_76; obj* x_78; obj* x_79; 
x_74 = lean::cnstr_get(x_71, 0);
x_76 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_set(x_71, 0, lean::box(0));
 lean::cnstr_set(x_71, 1, lean::box(0));
 x_78 = x_71;
} else {
 lean::inc(x_74);
 lean::inc(x_76);
 lean::dec(x_71);
 x_78 = lean::box(0);
}
x_79 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_79) == 0)
{
obj* x_81; obj* x_82; 
if (lean::is_scalar(x_78)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_78;
}
lean::cnstr_set(x_81, 0, x_74);
lean::cnstr_set(x_81, 1, x_76);
if (lean::is_scalar(x_73)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_73;
}
lean::cnstr_set(x_82, 0, x_81);
return x_82;
}
else
{
obj* x_83; obj* x_86; obj* x_87; obj* x_88; obj* x_90; obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_104; 
x_83 = lean::cnstr_get(x_79, 0);
lean::inc(x_83);
lean::dec(x_79);
x_86 = lean::cnstr_get(x_1, 0);
x_87 = lean::cnstr_get(x_86, 2);
x_88 = l_lean_file__map_to__position(x_87, x_83);
lean::dec(x_83);
x_90 = lean::box(0);
x_91 = lean::cnstr_get(x_88, 1);
lean::inc(x_91);
x_93 = l_lean_elaborator_to__pexpr___main___closed__3;
x_94 = l_lean_kvmap_set__nat(x_90, x_93, x_91);
lean::dec(x_91);
x_96 = lean::cnstr_get(x_88, 0);
lean::inc(x_96);
lean::dec(x_88);
x_99 = l_lean_elaborator_to__pexpr___main___closed__4;
x_100 = l_lean_kvmap_set__nat(x_94, x_99, x_96);
lean::dec(x_96);
x_102 = lean_expr_mk_mdata(x_100, x_74);
if (lean::is_scalar(x_78)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_78;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_76);
if (lean::is_scalar(x_73)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_73;
}
lean::cnstr_set(x_104, 0, x_103);
return x_104;
}
}
else
{
obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_0);
x_106 = lean::cnstr_get(x_71, 0);
x_108 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 x_110 = x_71;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_71);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_106);
lean::cnstr_set(x_111, 1, x_108);
if (lean::is_scalar(x_73)) {
 x_112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_112 = x_73;
}
lean::cnstr_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
obj* x_113; obj* x_114; obj* x_118; obj* x_119; obj* x_121; obj* x_122; 
x_113 = l_lean_parser_term_match_has__view;
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
lean::dec(x_113);
lean::inc(x_0);
x_118 = lean::apply_1(x_114, x_0);
x_119 = lean::cnstr_get(x_118, 5);
lean::inc(x_119);
x_121 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(x_119);
x_122 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_121, x_1, x_2);
if (lean::obj_tag(x_122) == 0)
{
obj* x_124; obj* x_126; obj* x_127; 
lean::dec(x_118);
x_124 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
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
obj* x_128; obj* x_131; obj* x_133; obj* x_136; obj* x_138; obj* x_140; 
x_128 = lean::cnstr_get(x_122, 0);
lean::inc(x_128);
lean::dec(x_122);
x_131 = lean::cnstr_get(x_128, 0);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_128, 1);
lean::inc(x_133);
lean::dec(x_128);
x_136 = lean::cnstr_get(x_118, 2);
lean::inc(x_136);
x_138 = l_lean_expander_get__opt__type___main(x_136);
lean::dec(x_136);
x_140 = l_lean_elaborator_to__pexpr___main(x_138, x_1, x_133);
lean::dec(x_133);
if (lean::obj_tag(x_140) == 0)
{
obj* x_144; obj* x_146; obj* x_147; 
lean::dec(x_118);
lean::dec(x_131);
x_144 = lean::cnstr_get(x_140, 0);
if (lean::is_exclusive(x_140)) {
 x_146 = x_140;
} else {
 lean::inc(x_144);
 lean::dec(x_140);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_147 = x_146;
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
obj* x_157; obj* x_159; obj* x_162; obj* x_165; 
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_156, 1);
lean::inc(x_159);
lean::dec(x_156);
x_162 = lean::cnstr_get(x_118, 1);
lean::inc(x_162);
lean::dec(x_118);
x_165 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_162, x_1, x_153);
lean::dec(x_153);
if (lean::obj_tag(x_165) == 0)
{
obj* x_169; obj* x_171; obj* x_172; 
lean::dec(x_159);
lean::dec(x_157);
x_169 = lean::cnstr_get(x_165, 0);
if (lean::is_exclusive(x_165)) {
 x_171 = x_165;
} else {
 lean::inc(x_169);
 lean::dec(x_165);
 x_171 = lean::box(0);
}
if (lean::is_scalar(x_171)) {
 x_172 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_172 = x_171;
}
lean::cnstr_set(x_172, 0, x_169);
x_12 = x_172;
goto lbl_13;
}
else
{
obj* x_173; obj* x_175; obj* x_176; obj* x_178; obj* x_180; obj* x_181; uint8 x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; 
x_173 = lean::cnstr_get(x_165, 0);
if (lean::is_exclusive(x_165)) {
 x_175 = x_165;
} else {
 lean::inc(x_173);
 lean::dec(x_165);
 x_175 = lean::box(0);
}
x_176 = lean::cnstr_get(x_173, 0);
x_178 = lean::cnstr_get(x_173, 1);
if (lean::is_exclusive(x_173)) {
 x_180 = x_173;
} else {
 lean::inc(x_176);
 lean::inc(x_178);
 lean::dec(x_173);
 x_180 = lean::box(0);
}
x_181 = l_lean_elaborator_to__pexpr___main___closed__24;
x_182 = 1;
x_183 = l_lean_kvmap_set__bool(x_157, x_181, x_182);
x_184 = lean_expr_mk_mdata(x_183, x_159);
x_185 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_184, x_176);
if (lean::is_scalar(x_180)) {
 x_186 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_186 = x_180;
}
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_178);
if (lean::is_scalar(x_175)) {
 x_187 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_187 = x_175;
}
lean::cnstr_set(x_187, 0, x_186);
x_12 = x_187;
goto lbl_13;
}
}
default:
{
obj* x_190; obj* x_191; 
lean::dec(x_156);
lean::dec(x_118);
x_190 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__2;
x_191 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_190, x_1, x_153);
lean::dec(x_153);
x_12 = x_191;
goto lbl_13;
}
}
}
}
}
}
else
{
obj* x_193; obj* x_194; obj* x_198; obj* x_199; obj* x_201; obj* x_202; obj* x_204; obj* x_207; obj* x_208; 
x_193 = l_lean_parser_term_struct__inst_has__view;
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
lean::dec(x_193);
lean::inc(x_0);
x_198 = lean::apply_1(x_194, x_0);
x_199 = lean::cnstr_get(x_198, 3);
lean::inc(x_199);
x_201 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_199);
x_202 = lean::cnstr_get(x_201, 0);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_201, 1);
lean::inc(x_204);
lean::dec(x_201);
x_207 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_204);
x_208 = lean::cnstr_get(x_207, 1);
lean::inc(x_208);
if (lean::obj_tag(x_208) == 0)
{
obj* x_210; obj* x_213; 
x_210 = lean::cnstr_get(x_207, 0);
lean::inc(x_210);
lean::dec(x_207);
x_213 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_202, x_1, x_2);
if (lean::obj_tag(x_213) == 0)
{
obj* x_218; obj* x_220; obj* x_221; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_198);
lean::dec(x_210);
x_218 = lean::cnstr_get(x_213, 0);
if (lean::is_exclusive(x_213)) {
 x_220 = x_213;
} else {
 lean::inc(x_218);
 lean::dec(x_213);
 x_220 = lean::box(0);
}
if (lean::is_scalar(x_220)) {
 x_221 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_221 = x_220;
}
lean::cnstr_set(x_221, 0, x_218);
return x_221;
}
else
{
obj* x_222; obj* x_225; obj* x_227; obj* x_230; obj* x_232; 
x_222 = lean::cnstr_get(x_213, 0);
lean::inc(x_222);
lean::dec(x_213);
x_225 = lean::cnstr_get(x_222, 0);
lean::inc(x_225);
x_227 = lean::cnstr_get(x_222, 1);
lean::inc(x_227);
lean::dec(x_222);
x_232 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_210, x_1, x_227);
lean::dec(x_227);
if (lean::obj_tag(x_232) == 0)
{
obj* x_238; obj* x_240; obj* x_241; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_198);
lean::dec(x_225);
x_238 = lean::cnstr_get(x_232, 0);
if (lean::is_exclusive(x_232)) {
 x_240 = x_232;
} else {
 lean::inc(x_238);
 lean::dec(x_232);
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
obj* x_242; obj* x_245; 
x_242 = lean::cnstr_get(x_232, 0);
lean::inc(x_242);
lean::dec(x_232);
x_245 = lean::cnstr_get(x_198, 2);
lean::inc(x_245);
if (lean::obj_tag(x_245) == 0)
{
obj* x_247; obj* x_249; obj* x_251; obj* x_252; 
x_247 = lean::cnstr_get(x_242, 0);
x_249 = lean::cnstr_get(x_242, 1);
if (lean::is_exclusive(x_242)) {
 x_251 = x_242;
} else {
 lean::inc(x_247);
 lean::inc(x_249);
 lean::dec(x_242);
 x_251 = lean::box(0);
}
if (lean::is_scalar(x_251)) {
 x_252 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_252 = x_251;
}
lean::cnstr_set(x_252, 0, x_247);
lean::cnstr_set(x_252, 1, x_249);
x_230 = x_252;
goto lbl_231;
}
else
{
obj* x_253; obj* x_255; obj* x_258; obj* x_261; obj* x_264; 
x_253 = lean::cnstr_get(x_242, 0);
lean::inc(x_253);
x_255 = lean::cnstr_get(x_242, 1);
lean::inc(x_255);
lean::dec(x_242);
x_258 = lean::cnstr_get(x_245, 0);
lean::inc(x_258);
lean::dec(x_245);
x_261 = lean::cnstr_get(x_258, 0);
lean::inc(x_261);
lean::dec(x_258);
x_264 = l_lean_elaborator_to__pexpr___main(x_261, x_1, x_255);
lean::dec(x_255);
if (lean::obj_tag(x_264) == 0)
{
obj* x_271; obj* x_273; obj* x_274; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_198);
lean::dec(x_225);
lean::dec(x_253);
x_271 = lean::cnstr_get(x_264, 0);
if (lean::is_exclusive(x_264)) {
 x_273 = x_264;
} else {
 lean::inc(x_271);
 lean::dec(x_264);
 x_273 = lean::box(0);
}
if (lean::is_scalar(x_273)) {
 x_274 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_274 = x_273;
}
lean::cnstr_set(x_274, 0, x_271);
return x_274;
}
else
{
obj* x_275; obj* x_278; obj* x_280; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; 
x_275 = lean::cnstr_get(x_264, 0);
lean::inc(x_275);
lean::dec(x_264);
x_278 = lean::cnstr_get(x_275, 0);
x_280 = lean::cnstr_get(x_275, 1);
if (lean::is_exclusive(x_275)) {
 x_282 = x_275;
} else {
 lean::inc(x_278);
 lean::inc(x_280);
 lean::dec(x_275);
 x_282 = lean::box(0);
}
x_283 = lean::box(0);
x_284 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_284, 0, x_278);
lean::cnstr_set(x_284, 1, x_283);
x_285 = l_list_append___rarg(x_253, x_284);
if (lean::is_scalar(x_282)) {
 x_286 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_286 = x_282;
}
lean::cnstr_set(x_286, 0, x_285);
lean::cnstr_set(x_286, 1, x_280);
x_230 = x_286;
goto lbl_231;
}
}
}
lbl_231:
{
obj* x_287; obj* x_289; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_298; uint8 x_299; obj* x_300; obj* x_301; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_311; obj* x_312; obj* x_314; obj* x_315; obj* x_316; obj* x_317; 
x_287 = lean::cnstr_get(x_230, 0);
x_289 = lean::cnstr_get(x_230, 1);
if (lean::is_exclusive(x_230)) {
 x_291 = x_230;
} else {
 lean::inc(x_287);
 lean::inc(x_289);
 lean::dec(x_230);
 x_291 = lean::box(0);
}
x_292 = lean::box(0);
x_293 = lean::mk_nat_obj(0u);
x_294 = l_list_length__aux___main___rarg(x_225, x_293);
x_295 = l_lean_elaborator_to__pexpr___main___closed__25;
x_296 = l_lean_kvmap_set__nat(x_292, x_295, x_294);
lean::dec(x_294);
x_298 = l_lean_elaborator_to__pexpr___main___closed__26;
x_299 = 0;
x_300 = l_lean_kvmap_set__bool(x_296, x_298, x_299);
x_301 = lean::cnstr_get(x_198, 1);
lean::inc(x_301);
lean::dec(x_198);
x_304 = l_lean_elaborator_to__pexpr___main___closed__27;
x_305 = l_option_map___rarg(x_304, x_301);
x_306 = l_lean_elaborator_to__pexpr___main___closed__28;
x_307 = l_option_map___rarg(x_306, x_305);
x_308 = lean::box(0);
x_309 = l_option_get__or__else___main___rarg(x_307, x_308);
lean::dec(x_307);
x_311 = l_lean_elaborator_to__pexpr___main___closed__29;
x_312 = l_lean_kvmap_set__name(x_300, x_311, x_309);
lean::dec(x_309);
x_314 = l_list_append___rarg(x_225, x_287);
x_315 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(x_314);
x_316 = lean_expr_mk_mdata(x_312, x_315);
if (lean::is_scalar(x_291)) {
 x_317 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_317 = x_291;
}
lean::cnstr_set(x_317, 0, x_316);
lean::cnstr_set(x_317, 1, x_289);
x_14 = x_317;
goto lbl_15;
}
}
}
else
{
obj* x_318; obj* x_320; 
x_318 = lean::cnstr_get(x_208, 0);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_318, 0);
lean::inc(x_320);
lean::dec(x_318);
if (lean::obj_tag(x_320) == 0)
{
obj* x_323; obj* x_324; obj* x_327; obj* x_328; obj* x_331; obj* x_332; obj* x_333; 
if (lean::is_exclusive(x_208)) {
 lean::cnstr_release(x_208, 0);
 lean::cnstr_release(x_208, 1);
 x_323 = x_208;
} else {
 lean::dec(x_208);
 x_323 = lean::box(0);
}
x_324 = lean::cnstr_get(x_207, 0);
lean::inc(x_324);
lean::dec(x_207);
x_327 = l_lean_parser_term_struct__inst__item_has__view;
x_328 = lean::cnstr_get(x_327, 1);
lean::inc(x_328);
lean::dec(x_327);
x_331 = lean::apply_1(x_328, x_320);
x_332 = l_lean_elaborator_to__pexpr___main___closed__30;
x_333 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_331, x_332, x_1, x_2);
lean::dec(x_331);
if (lean::obj_tag(x_333) == 0)
{
obj* x_341; obj* x_343; obj* x_344; 
lean::dec(x_323);
lean::dec(x_324);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_198);
x_341 = lean::cnstr_get(x_333, 0);
if (lean::is_exclusive(x_333)) {
 x_343 = x_333;
} else {
 lean::inc(x_341);
 lean::dec(x_333);
 x_343 = lean::box(0);
}
if (lean::is_scalar(x_343)) {
 x_344 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_344 = x_343;
}
lean::cnstr_set(x_344, 0, x_341);
return x_344;
}
else
{
obj* x_345; obj* x_348; obj* x_350; obj* x_353; 
x_345 = lean::cnstr_get(x_333, 0);
lean::inc(x_345);
lean::dec(x_333);
x_348 = lean::cnstr_get(x_345, 0);
lean::inc(x_348);
x_350 = lean::cnstr_get(x_345, 1);
lean::inc(x_350);
lean::dec(x_345);
x_353 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_202, x_1, x_350);
lean::dec(x_350);
if (lean::obj_tag(x_353) == 0)
{
obj* x_361; obj* x_363; obj* x_364; 
lean::dec(x_323);
lean::dec(x_324);
lean::dec(x_348);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_198);
x_361 = lean::cnstr_get(x_353, 0);
if (lean::is_exclusive(x_353)) {
 x_363 = x_353;
} else {
 lean::inc(x_361);
 lean::dec(x_353);
 x_363 = lean::box(0);
}
if (lean::is_scalar(x_363)) {
 x_364 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_364 = x_363;
}
lean::cnstr_set(x_364, 0, x_361);
return x_364;
}
else
{
obj* x_365; obj* x_368; obj* x_370; obj* x_373; obj* x_375; 
x_365 = lean::cnstr_get(x_353, 0);
lean::inc(x_365);
lean::dec(x_353);
x_368 = lean::cnstr_get(x_365, 0);
lean::inc(x_368);
x_370 = lean::cnstr_get(x_365, 1);
lean::inc(x_370);
lean::dec(x_365);
x_375 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_324, x_1, x_370);
lean::dec(x_370);
if (lean::obj_tag(x_375) == 0)
{
obj* x_383; obj* x_385; obj* x_386; 
lean::dec(x_323);
lean::dec(x_348);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_368);
lean::dec(x_198);
x_383 = lean::cnstr_get(x_375, 0);
if (lean::is_exclusive(x_375)) {
 x_385 = x_375;
} else {
 lean::inc(x_383);
 lean::dec(x_375);
 x_385 = lean::box(0);
}
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_383);
return x_386;
}
else
{
obj* x_387; obj* x_390; 
x_387 = lean::cnstr_get(x_375, 0);
lean::inc(x_387);
lean::dec(x_375);
x_390 = lean::cnstr_get(x_198, 2);
lean::inc(x_390);
if (lean::obj_tag(x_390) == 0)
{
obj* x_393; obj* x_395; obj* x_397; obj* x_398; 
lean::dec(x_323);
x_393 = lean::cnstr_get(x_387, 0);
x_395 = lean::cnstr_get(x_387, 1);
if (lean::is_exclusive(x_387)) {
 x_397 = x_387;
} else {
 lean::inc(x_393);
 lean::inc(x_395);
 lean::dec(x_387);
 x_397 = lean::box(0);
}
if (lean::is_scalar(x_397)) {
 x_398 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_398 = x_397;
}
lean::cnstr_set(x_398, 0, x_393);
lean::cnstr_set(x_398, 1, x_395);
x_373 = x_398;
goto lbl_374;
}
else
{
obj* x_399; obj* x_401; obj* x_404; obj* x_407; obj* x_410; 
x_399 = lean::cnstr_get(x_387, 0);
lean::inc(x_399);
x_401 = lean::cnstr_get(x_387, 1);
lean::inc(x_401);
lean::dec(x_387);
x_404 = lean::cnstr_get(x_390, 0);
lean::inc(x_404);
lean::dec(x_390);
x_407 = lean::cnstr_get(x_404, 0);
lean::inc(x_407);
lean::dec(x_404);
x_410 = l_lean_elaborator_to__pexpr___main(x_407, x_1, x_401);
lean::dec(x_401);
if (lean::obj_tag(x_410) == 0)
{
obj* x_419; obj* x_421; obj* x_422; 
lean::dec(x_323);
lean::dec(x_348);
lean::dec(x_399);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_368);
lean::dec(x_198);
x_419 = lean::cnstr_get(x_410, 0);
if (lean::is_exclusive(x_410)) {
 x_421 = x_410;
} else {
 lean::inc(x_419);
 lean::dec(x_410);
 x_421 = lean::box(0);
}
if (lean::is_scalar(x_421)) {
 x_422 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_422 = x_421;
}
lean::cnstr_set(x_422, 0, x_419);
return x_422;
}
else
{
obj* x_423; obj* x_426; obj* x_428; obj* x_430; obj* x_431; obj* x_432; obj* x_433; obj* x_434; 
x_423 = lean::cnstr_get(x_410, 0);
lean::inc(x_423);
lean::dec(x_410);
x_426 = lean::cnstr_get(x_423, 0);
x_428 = lean::cnstr_get(x_423, 1);
if (lean::is_exclusive(x_423)) {
 x_430 = x_423;
} else {
 lean::inc(x_426);
 lean::inc(x_428);
 lean::dec(x_423);
 x_430 = lean::box(0);
}
x_431 = lean::box(0);
if (lean::is_scalar(x_323)) {
 x_432 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_432 = x_323;
}
lean::cnstr_set(x_432, 0, x_426);
lean::cnstr_set(x_432, 1, x_431);
x_433 = l_list_append___rarg(x_399, x_432);
if (lean::is_scalar(x_430)) {
 x_434 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_434 = x_430;
}
lean::cnstr_set(x_434, 0, x_433);
lean::cnstr_set(x_434, 1, x_428);
x_373 = x_434;
goto lbl_374;
}
}
}
lbl_374:
{
obj* x_435; obj* x_437; obj* x_439; obj* x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_446; uint8 x_447; obj* x_448; obj* x_449; obj* x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_459; obj* x_460; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_435 = lean::cnstr_get(x_373, 0);
x_437 = lean::cnstr_get(x_373, 1);
if (lean::is_exclusive(x_373)) {
 x_439 = x_373;
} else {
 lean::inc(x_435);
 lean::inc(x_437);
 lean::dec(x_373);
 x_439 = lean::box(0);
}
x_440 = lean::box(0);
x_441 = lean::mk_nat_obj(0u);
x_442 = l_list_length__aux___main___rarg(x_368, x_441);
x_443 = l_lean_elaborator_to__pexpr___main___closed__25;
x_444 = l_lean_kvmap_set__nat(x_440, x_443, x_442);
lean::dec(x_442);
x_446 = l_lean_elaborator_to__pexpr___main___closed__26;
x_447 = lean::unbox(x_348);
x_448 = l_lean_kvmap_set__bool(x_444, x_446, x_447);
x_449 = lean::cnstr_get(x_198, 1);
lean::inc(x_449);
lean::dec(x_198);
x_452 = l_lean_elaborator_to__pexpr___main___closed__27;
x_453 = l_option_map___rarg(x_452, x_449);
x_454 = l_lean_elaborator_to__pexpr___main___closed__28;
x_455 = l_option_map___rarg(x_454, x_453);
x_456 = lean::box(0);
x_457 = l_option_get__or__else___main___rarg(x_455, x_456);
lean::dec(x_455);
x_459 = l_lean_elaborator_to__pexpr___main___closed__29;
x_460 = l_lean_kvmap_set__name(x_448, x_459, x_457);
lean::dec(x_457);
x_462 = l_list_append___rarg(x_368, x_435);
x_463 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_462);
x_464 = lean_expr_mk_mdata(x_460, x_463);
if (lean::is_scalar(x_439)) {
 x_465 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_465 = x_439;
}
lean::cnstr_set(x_465, 0, x_464);
lean::cnstr_set(x_465, 1, x_437);
x_14 = x_465;
goto lbl_15;
}
}
}
}
else
{
obj* x_466; obj* x_468; 
x_466 = lean::cnstr_get(x_208, 1);
if (lean::is_exclusive(x_208)) {
 lean::cnstr_release(x_208, 0);
 lean::cnstr_set(x_208, 1, lean::box(0));
 x_468 = x_208;
} else {
 lean::inc(x_466);
 lean::dec(x_208);
 x_468 = lean::box(0);
}
if (lean::obj_tag(x_466) == 0)
{
obj* x_470; obj* x_473; 
lean::dec(x_320);
x_470 = lean::cnstr_get(x_207, 0);
lean::inc(x_470);
lean::dec(x_207);
x_473 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_202, x_1, x_2);
if (lean::obj_tag(x_473) == 0)
{
obj* x_479; obj* x_481; obj* x_482; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_198);
lean::dec(x_468);
lean::dec(x_470);
x_479 = lean::cnstr_get(x_473, 0);
if (lean::is_exclusive(x_473)) {
 x_481 = x_473;
} else {
 lean::inc(x_479);
 lean::dec(x_473);
 x_481 = lean::box(0);
}
if (lean::is_scalar(x_481)) {
 x_482 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_482 = x_481;
}
lean::cnstr_set(x_482, 0, x_479);
return x_482;
}
else
{
obj* x_483; obj* x_486; obj* x_488; obj* x_491; obj* x_493; 
x_483 = lean::cnstr_get(x_473, 0);
lean::inc(x_483);
lean::dec(x_473);
x_486 = lean::cnstr_get(x_483, 0);
lean::inc(x_486);
x_488 = lean::cnstr_get(x_483, 1);
lean::inc(x_488);
lean::dec(x_483);
x_493 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_470, x_1, x_488);
lean::dec(x_488);
if (lean::obj_tag(x_493) == 0)
{
obj* x_500; obj* x_502; obj* x_503; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_198);
lean::dec(x_468);
lean::dec(x_486);
x_500 = lean::cnstr_get(x_493, 0);
if (lean::is_exclusive(x_493)) {
 x_502 = x_493;
} else {
 lean::inc(x_500);
 lean::dec(x_493);
 x_502 = lean::box(0);
}
if (lean::is_scalar(x_502)) {
 x_503 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_503 = x_502;
}
lean::cnstr_set(x_503, 0, x_500);
return x_503;
}
else
{
obj* x_504; obj* x_507; 
x_504 = lean::cnstr_get(x_493, 0);
lean::inc(x_504);
lean::dec(x_493);
x_507 = lean::cnstr_get(x_198, 2);
lean::inc(x_507);
if (lean::obj_tag(x_507) == 0)
{
obj* x_510; obj* x_512; obj* x_514; obj* x_515; 
lean::dec(x_468);
x_510 = lean::cnstr_get(x_504, 0);
x_512 = lean::cnstr_get(x_504, 1);
if (lean::is_exclusive(x_504)) {
 x_514 = x_504;
} else {
 lean::inc(x_510);
 lean::inc(x_512);
 lean::dec(x_504);
 x_514 = lean::box(0);
}
if (lean::is_scalar(x_514)) {
 x_515 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_515 = x_514;
}
lean::cnstr_set(x_515, 0, x_510);
lean::cnstr_set(x_515, 1, x_512);
x_491 = x_515;
goto lbl_492;
}
else
{
obj* x_516; obj* x_518; obj* x_521; obj* x_524; obj* x_527; 
x_516 = lean::cnstr_get(x_504, 0);
lean::inc(x_516);
x_518 = lean::cnstr_get(x_504, 1);
lean::inc(x_518);
lean::dec(x_504);
x_521 = lean::cnstr_get(x_507, 0);
lean::inc(x_521);
lean::dec(x_507);
x_524 = lean::cnstr_get(x_521, 0);
lean::inc(x_524);
lean::dec(x_521);
x_527 = l_lean_elaborator_to__pexpr___main(x_524, x_1, x_518);
lean::dec(x_518);
if (lean::obj_tag(x_527) == 0)
{
obj* x_535; obj* x_537; obj* x_538; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_198);
lean::dec(x_468);
lean::dec(x_516);
lean::dec(x_486);
x_535 = lean::cnstr_get(x_527, 0);
if (lean::is_exclusive(x_527)) {
 x_537 = x_527;
} else {
 lean::inc(x_535);
 lean::dec(x_527);
 x_537 = lean::box(0);
}
if (lean::is_scalar(x_537)) {
 x_538 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_538 = x_537;
}
lean::cnstr_set(x_538, 0, x_535);
return x_538;
}
else
{
obj* x_539; obj* x_542; obj* x_544; obj* x_546; obj* x_547; obj* x_548; obj* x_549; obj* x_550; 
x_539 = lean::cnstr_get(x_527, 0);
lean::inc(x_539);
lean::dec(x_527);
x_542 = lean::cnstr_get(x_539, 0);
x_544 = lean::cnstr_get(x_539, 1);
if (lean::is_exclusive(x_539)) {
 x_546 = x_539;
} else {
 lean::inc(x_542);
 lean::inc(x_544);
 lean::dec(x_539);
 x_546 = lean::box(0);
}
x_547 = lean::box(0);
if (lean::is_scalar(x_468)) {
 x_548 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_548 = x_468;
}
lean::cnstr_set(x_548, 0, x_542);
lean::cnstr_set(x_548, 1, x_547);
x_549 = l_list_append___rarg(x_516, x_548);
if (lean::is_scalar(x_546)) {
 x_550 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_550 = x_546;
}
lean::cnstr_set(x_550, 0, x_549);
lean::cnstr_set(x_550, 1, x_544);
x_491 = x_550;
goto lbl_492;
}
}
}
lbl_492:
{
obj* x_551; obj* x_553; obj* x_555; obj* x_556; obj* x_557; obj* x_558; obj* x_559; obj* x_560; obj* x_562; uint8 x_563; obj* x_564; obj* x_565; obj* x_568; obj* x_569; obj* x_570; obj* x_571; obj* x_572; obj* x_573; obj* x_575; obj* x_576; obj* x_578; obj* x_579; obj* x_580; obj* x_581; 
x_551 = lean::cnstr_get(x_491, 0);
x_553 = lean::cnstr_get(x_491, 1);
if (lean::is_exclusive(x_491)) {
 x_555 = x_491;
} else {
 lean::inc(x_551);
 lean::inc(x_553);
 lean::dec(x_491);
 x_555 = lean::box(0);
}
x_556 = lean::box(0);
x_557 = lean::mk_nat_obj(0u);
x_558 = l_list_length__aux___main___rarg(x_486, x_557);
x_559 = l_lean_elaborator_to__pexpr___main___closed__25;
x_560 = l_lean_kvmap_set__nat(x_556, x_559, x_558);
lean::dec(x_558);
x_562 = l_lean_elaborator_to__pexpr___main___closed__26;
x_563 = 1;
x_564 = l_lean_kvmap_set__bool(x_560, x_562, x_563);
x_565 = lean::cnstr_get(x_198, 1);
lean::inc(x_565);
lean::dec(x_198);
x_568 = l_lean_elaborator_to__pexpr___main___closed__27;
x_569 = l_option_map___rarg(x_568, x_565);
x_570 = l_lean_elaborator_to__pexpr___main___closed__28;
x_571 = l_option_map___rarg(x_570, x_569);
x_572 = lean::box(0);
x_573 = l_option_get__or__else___main___rarg(x_571, x_572);
lean::dec(x_571);
x_575 = l_lean_elaborator_to__pexpr___main___closed__29;
x_576 = l_lean_kvmap_set__name(x_564, x_575, x_573);
lean::dec(x_573);
x_578 = l_list_append___rarg(x_486, x_551);
x_579 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_578);
x_580 = lean_expr_mk_mdata(x_576, x_579);
if (lean::is_scalar(x_555)) {
 x_581 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_581 = x_555;
}
lean::cnstr_set(x_581, 0, x_580);
lean::cnstr_set(x_581, 1, x_553);
x_14 = x_581;
goto lbl_15;
}
}
}
else
{
obj* x_583; obj* x_584; obj* x_587; obj* x_588; obj* x_591; obj* x_592; obj* x_593; 
lean::dec(x_468);
if (lean::is_exclusive(x_466)) {
 lean::cnstr_release(x_466, 0);
 lean::cnstr_release(x_466, 1);
 x_583 = x_466;
} else {
 lean::dec(x_466);
 x_583 = lean::box(0);
}
x_584 = lean::cnstr_get(x_207, 0);
lean::inc(x_584);
lean::dec(x_207);
x_587 = l_lean_parser_term_struct__inst__item_has__view;
x_588 = lean::cnstr_get(x_587, 1);
lean::inc(x_588);
lean::dec(x_587);
x_591 = lean::apply_1(x_588, x_320);
x_592 = l_lean_elaborator_to__pexpr___main___closed__30;
x_593 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_591, x_592, x_1, x_2);
lean::dec(x_591);
if (lean::obj_tag(x_593) == 0)
{
obj* x_601; obj* x_603; obj* x_604; 
lean::dec(x_583);
lean::dec(x_584);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_202);
lean::dec(x_198);
x_601 = lean::cnstr_get(x_593, 0);
if (lean::is_exclusive(x_593)) {
 x_603 = x_593;
} else {
 lean::inc(x_601);
 lean::dec(x_593);
 x_603 = lean::box(0);
}
if (lean::is_scalar(x_603)) {
 x_604 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_604 = x_603;
}
lean::cnstr_set(x_604, 0, x_601);
return x_604;
}
else
{
obj* x_605; obj* x_608; obj* x_610; obj* x_613; 
x_605 = lean::cnstr_get(x_593, 0);
lean::inc(x_605);
lean::dec(x_593);
x_608 = lean::cnstr_get(x_605, 0);
lean::inc(x_608);
x_610 = lean::cnstr_get(x_605, 1);
lean::inc(x_610);
lean::dec(x_605);
x_613 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_202, x_1, x_610);
lean::dec(x_610);
if (lean::obj_tag(x_613) == 0)
{
obj* x_621; obj* x_623; obj* x_624; 
lean::dec(x_583);
lean::dec(x_584);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_608);
lean::dec(x_198);
x_621 = lean::cnstr_get(x_613, 0);
if (lean::is_exclusive(x_613)) {
 x_623 = x_613;
} else {
 lean::inc(x_621);
 lean::dec(x_613);
 x_623 = lean::box(0);
}
if (lean::is_scalar(x_623)) {
 x_624 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_624 = x_623;
}
lean::cnstr_set(x_624, 0, x_621);
return x_624;
}
else
{
obj* x_625; obj* x_628; obj* x_630; obj* x_633; obj* x_635; 
x_625 = lean::cnstr_get(x_613, 0);
lean::inc(x_625);
lean::dec(x_613);
x_628 = lean::cnstr_get(x_625, 0);
lean::inc(x_628);
x_630 = lean::cnstr_get(x_625, 1);
lean::inc(x_630);
lean::dec(x_625);
x_635 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_584, x_1, x_630);
lean::dec(x_630);
if (lean::obj_tag(x_635) == 0)
{
obj* x_643; obj* x_645; obj* x_646; 
lean::dec(x_583);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_608);
lean::dec(x_628);
lean::dec(x_198);
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
obj* x_647; obj* x_650; 
x_647 = lean::cnstr_get(x_635, 0);
lean::inc(x_647);
lean::dec(x_635);
x_650 = lean::cnstr_get(x_198, 2);
lean::inc(x_650);
if (lean::obj_tag(x_650) == 0)
{
obj* x_653; obj* x_655; obj* x_657; obj* x_658; 
lean::dec(x_583);
x_653 = lean::cnstr_get(x_647, 0);
x_655 = lean::cnstr_get(x_647, 1);
if (lean::is_exclusive(x_647)) {
 x_657 = x_647;
} else {
 lean::inc(x_653);
 lean::inc(x_655);
 lean::dec(x_647);
 x_657 = lean::box(0);
}
if (lean::is_scalar(x_657)) {
 x_658 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_658 = x_657;
}
lean::cnstr_set(x_658, 0, x_653);
lean::cnstr_set(x_658, 1, x_655);
x_633 = x_658;
goto lbl_634;
}
else
{
obj* x_659; obj* x_661; obj* x_664; obj* x_667; obj* x_670; 
x_659 = lean::cnstr_get(x_647, 0);
lean::inc(x_659);
x_661 = lean::cnstr_get(x_647, 1);
lean::inc(x_661);
lean::dec(x_647);
x_664 = lean::cnstr_get(x_650, 0);
lean::inc(x_664);
lean::dec(x_650);
x_667 = lean::cnstr_get(x_664, 0);
lean::inc(x_667);
lean::dec(x_664);
x_670 = l_lean_elaborator_to__pexpr___main(x_667, x_1, x_661);
lean::dec(x_661);
if (lean::obj_tag(x_670) == 0)
{
obj* x_679; obj* x_681; obj* x_682; 
lean::dec(x_583);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_608);
lean::dec(x_628);
lean::dec(x_198);
lean::dec(x_659);
x_679 = lean::cnstr_get(x_670, 0);
if (lean::is_exclusive(x_670)) {
 x_681 = x_670;
} else {
 lean::inc(x_679);
 lean::dec(x_670);
 x_681 = lean::box(0);
}
if (lean::is_scalar(x_681)) {
 x_682 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_682 = x_681;
}
lean::cnstr_set(x_682, 0, x_679);
return x_682;
}
else
{
obj* x_683; obj* x_686; obj* x_688; obj* x_690; obj* x_691; obj* x_692; obj* x_693; obj* x_694; 
x_683 = lean::cnstr_get(x_670, 0);
lean::inc(x_683);
lean::dec(x_670);
x_686 = lean::cnstr_get(x_683, 0);
x_688 = lean::cnstr_get(x_683, 1);
if (lean::is_exclusive(x_683)) {
 x_690 = x_683;
} else {
 lean::inc(x_686);
 lean::inc(x_688);
 lean::dec(x_683);
 x_690 = lean::box(0);
}
x_691 = lean::box(0);
if (lean::is_scalar(x_583)) {
 x_692 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_692 = x_583;
}
lean::cnstr_set(x_692, 0, x_686);
lean::cnstr_set(x_692, 1, x_691);
x_693 = l_list_append___rarg(x_659, x_692);
if (lean::is_scalar(x_690)) {
 x_694 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_694 = x_690;
}
lean::cnstr_set(x_694, 0, x_693);
lean::cnstr_set(x_694, 1, x_688);
x_633 = x_694;
goto lbl_634;
}
}
}
lbl_634:
{
obj* x_695; obj* x_697; obj* x_699; obj* x_700; obj* x_701; obj* x_702; obj* x_703; obj* x_704; obj* x_706; uint8 x_707; obj* x_708; obj* x_709; obj* x_712; obj* x_713; obj* x_714; obj* x_715; obj* x_716; obj* x_717; obj* x_719; obj* x_720; obj* x_722; obj* x_723; obj* x_724; obj* x_725; 
x_695 = lean::cnstr_get(x_633, 0);
x_697 = lean::cnstr_get(x_633, 1);
if (lean::is_exclusive(x_633)) {
 x_699 = x_633;
} else {
 lean::inc(x_695);
 lean::inc(x_697);
 lean::dec(x_633);
 x_699 = lean::box(0);
}
x_700 = lean::box(0);
x_701 = lean::mk_nat_obj(0u);
x_702 = l_list_length__aux___main___rarg(x_628, x_701);
x_703 = l_lean_elaborator_to__pexpr___main___closed__25;
x_704 = l_lean_kvmap_set__nat(x_700, x_703, x_702);
lean::dec(x_702);
x_706 = l_lean_elaborator_to__pexpr___main___closed__26;
x_707 = lean::unbox(x_608);
x_708 = l_lean_kvmap_set__bool(x_704, x_706, x_707);
x_709 = lean::cnstr_get(x_198, 1);
lean::inc(x_709);
lean::dec(x_198);
x_712 = l_lean_elaborator_to__pexpr___main___closed__27;
x_713 = l_option_map___rarg(x_712, x_709);
x_714 = l_lean_elaborator_to__pexpr___main___closed__28;
x_715 = l_option_map___rarg(x_714, x_713);
x_716 = lean::box(0);
x_717 = l_option_get__or__else___main___rarg(x_715, x_716);
lean::dec(x_715);
x_719 = l_lean_elaborator_to__pexpr___main___closed__29;
x_720 = l_lean_kvmap_set__name(x_708, x_719, x_717);
lean::dec(x_717);
x_722 = l_list_append___rarg(x_628, x_695);
x_723 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_722);
x_724 = lean_expr_mk_mdata(x_720, x_723);
if (lean::is_scalar(x_699)) {
 x_725 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_725 = x_699;
}
lean::cnstr_set(x_725, 0, x_724);
lean::cnstr_set(x_725, 1, x_697);
x_14 = x_725;
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
obj* x_727; 
lean::inc(x_9);
x_727 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_9, x_1, x_2);
if (lean::obj_tag(x_727) == 0)
{
obj* x_731; obj* x_733; obj* x_734; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_0);
x_731 = lean::cnstr_get(x_727, 0);
if (lean::is_exclusive(x_727)) {
 x_733 = x_727;
} else {
 lean::inc(x_731);
 lean::dec(x_727);
 x_733 = lean::box(0);
}
if (lean::is_scalar(x_733)) {
 x_734 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_734 = x_733;
}
lean::cnstr_set(x_734, 0, x_731);
return x_734;
}
else
{
obj* x_735; obj* x_738; obj* x_740; obj* x_742; obj* x_743; obj* x_744; 
x_735 = lean::cnstr_get(x_727, 0);
lean::inc(x_735);
lean::dec(x_727);
x_738 = lean::cnstr_get(x_735, 0);
x_740 = lean::cnstr_get(x_735, 1);
if (lean::is_exclusive(x_735)) {
 x_742 = x_735;
} else {
 lean::inc(x_738);
 lean::inc(x_740);
 lean::dec(x_735);
 x_742 = lean::box(0);
}
x_743 = l_list_reverse___rarg(x_738);
if (lean::is_scalar(x_742)) {
 x_744 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_744 = x_742;
}
lean::cnstr_set(x_744, 0, x_743);
lean::cnstr_set(x_744, 1, x_740);
x_16 = x_744;
goto lbl_17;
}
}
}
else
{
obj* x_747; obj* x_748; obj* x_752; obj* x_753; obj* x_754; obj* x_755; obj* x_757; obj* x_758; 
lean::dec(x_9);
lean::dec(x_7);
x_747 = l_lean_parser_string__lit_has__view;
x_748 = lean::cnstr_get(x_747, 0);
lean::inc(x_748);
lean::dec(x_747);
lean::inc(x_0);
x_752 = lean::apply_1(x_748, x_0);
x_753 = l_lean_parser_string__lit_view_value(x_752);
x_754 = l_lean_elaborator_to__pexpr___main___closed__31;
x_755 = l_option_get__or__else___main___rarg(x_753, x_754);
lean::dec(x_753);
x_757 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_757, 0, x_755);
x_758 = lean_expr_mk_lit(x_757);
if (x_21 == 0)
{
obj* x_759; 
x_759 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_759) == 0)
{
obj* x_762; obj* x_763; 
lean::inc(x_2);
x_762 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_762, 0, x_758);
lean::cnstr_set(x_762, 1, x_2);
x_763 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_763, 0, x_762);
return x_763;
}
else
{
obj* x_764; obj* x_767; obj* x_768; obj* x_769; obj* x_771; obj* x_772; obj* x_774; obj* x_775; obj* x_777; obj* x_780; obj* x_781; obj* x_783; obj* x_785; obj* x_786; 
x_764 = lean::cnstr_get(x_759, 0);
lean::inc(x_764);
lean::dec(x_759);
x_767 = lean::cnstr_get(x_1, 0);
x_768 = lean::cnstr_get(x_767, 2);
x_769 = l_lean_file__map_to__position(x_768, x_764);
lean::dec(x_764);
x_771 = lean::box(0);
x_772 = lean::cnstr_get(x_769, 1);
lean::inc(x_772);
x_774 = l_lean_elaborator_to__pexpr___main___closed__3;
x_775 = l_lean_kvmap_set__nat(x_771, x_774, x_772);
lean::dec(x_772);
x_777 = lean::cnstr_get(x_769, 0);
lean::inc(x_777);
lean::dec(x_769);
x_780 = l_lean_elaborator_to__pexpr___main___closed__4;
x_781 = l_lean_kvmap_set__nat(x_775, x_780, x_777);
lean::dec(x_777);
x_783 = lean_expr_mk_mdata(x_781, x_758);
lean::inc(x_2);
x_785 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_785, 0, x_783);
lean::cnstr_set(x_785, 1, x_2);
x_786 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_786, 0, x_785);
return x_786;
}
}
else
{
obj* x_789; obj* x_790; 
lean::dec(x_0);
lean::inc(x_2);
x_789 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_789, 0, x_758);
lean::cnstr_set(x_789, 1, x_2);
x_790 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_790, 0, x_789);
return x_790;
}
}
}
else
{
obj* x_793; obj* x_794; obj* x_798; obj* x_799; obj* x_800; obj* x_801; 
lean::dec(x_9);
lean::dec(x_7);
x_793 = l_lean_parser_number_has__view;
x_794 = lean::cnstr_get(x_793, 0);
lean::inc(x_794);
lean::dec(x_793);
lean::inc(x_0);
x_798 = lean::apply_1(x_794, x_0);
x_799 = l_lean_parser_number_view_to__nat___main(x_798);
x_800 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_800, 0, x_799);
x_801 = lean_expr_mk_lit(x_800);
if (x_21 == 0)
{
obj* x_802; 
x_802 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_802) == 0)
{
obj* x_805; obj* x_806; 
lean::inc(x_2);
x_805 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_805, 0, x_801);
lean::cnstr_set(x_805, 1, x_2);
x_806 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_806, 0, x_805);
return x_806;
}
else
{
obj* x_807; obj* x_810; obj* x_811; obj* x_812; obj* x_814; obj* x_815; obj* x_817; obj* x_818; obj* x_820; obj* x_823; obj* x_824; obj* x_826; obj* x_828; obj* x_829; 
x_807 = lean::cnstr_get(x_802, 0);
lean::inc(x_807);
lean::dec(x_802);
x_810 = lean::cnstr_get(x_1, 0);
x_811 = lean::cnstr_get(x_810, 2);
x_812 = l_lean_file__map_to__position(x_811, x_807);
lean::dec(x_807);
x_814 = lean::box(0);
x_815 = lean::cnstr_get(x_812, 1);
lean::inc(x_815);
x_817 = l_lean_elaborator_to__pexpr___main___closed__3;
x_818 = l_lean_kvmap_set__nat(x_814, x_817, x_815);
lean::dec(x_815);
x_820 = lean::cnstr_get(x_812, 0);
lean::inc(x_820);
lean::dec(x_812);
x_823 = l_lean_elaborator_to__pexpr___main___closed__4;
x_824 = l_lean_kvmap_set__nat(x_818, x_823, x_820);
lean::dec(x_820);
x_826 = lean_expr_mk_mdata(x_824, x_801);
lean::inc(x_2);
x_828 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_828, 0, x_826);
lean::cnstr_set(x_828, 1, x_2);
x_829 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_829, 0, x_828);
return x_829;
}
}
else
{
obj* x_832; obj* x_833; 
lean::dec(x_0);
lean::inc(x_2);
x_832 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_832, 0, x_801);
lean::cnstr_set(x_832, 1, x_2);
x_833 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_833, 0, x_832);
return x_833;
}
}
}
else
{
obj* x_835; obj* x_836; obj* x_840; obj* x_841; obj* x_844; 
lean::dec(x_9);
x_835 = l_lean_parser_term_borrowed_has__view;
x_836 = lean::cnstr_get(x_835, 0);
lean::inc(x_836);
lean::dec(x_835);
lean::inc(x_0);
x_840 = lean::apply_1(x_836, x_0);
x_841 = lean::cnstr_get(x_840, 1);
lean::inc(x_841);
lean::dec(x_840);
x_844 = l_lean_elaborator_to__pexpr___main(x_841, x_1, x_2);
if (lean::obj_tag(x_844) == 0)
{
obj* x_847; obj* x_849; obj* x_850; 
lean::dec(x_7);
lean::dec(x_0);
x_847 = lean::cnstr_get(x_844, 0);
if (lean::is_exclusive(x_844)) {
 x_849 = x_844;
} else {
 lean::inc(x_847);
 lean::dec(x_844);
 x_849 = lean::box(0);
}
if (lean::is_scalar(x_849)) {
 x_850 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_850 = x_849;
}
lean::cnstr_set(x_850, 0, x_847);
return x_850;
}
else
{
obj* x_851; obj* x_854; obj* x_856; obj* x_858; obj* x_859; obj* x_860; obj* x_861; 
x_851 = lean::cnstr_get(x_844, 0);
lean::inc(x_851);
lean::dec(x_844);
x_854 = lean::cnstr_get(x_851, 0);
x_856 = lean::cnstr_get(x_851, 1);
if (lean::is_exclusive(x_851)) {
 x_858 = x_851;
} else {
 lean::inc(x_854);
 lean::inc(x_856);
 lean::dec(x_851);
 x_858 = lean::box(0);
}
x_859 = l_lean_elaborator_to__pexpr___main___closed__32;
x_860 = l_lean_elaborator_expr_mk__annotation(x_859, x_854);
if (lean::is_scalar(x_858)) {
 x_861 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_861 = x_858;
}
lean::cnstr_set(x_861, 0, x_860);
lean::cnstr_set(x_861, 1, x_856);
x_14 = x_861;
goto lbl_15;
}
}
}
else
{
obj* x_863; obj* x_864; obj* x_868; obj* x_869; obj* x_872; 
lean::dec(x_9);
x_863 = l_lean_parser_term_inaccessible_has__view;
x_864 = lean::cnstr_get(x_863, 0);
lean::inc(x_864);
lean::dec(x_863);
lean::inc(x_0);
x_868 = lean::apply_1(x_864, x_0);
x_869 = lean::cnstr_get(x_868, 1);
lean::inc(x_869);
lean::dec(x_868);
x_872 = l_lean_elaborator_to__pexpr___main(x_869, x_1, x_2);
if (lean::obj_tag(x_872) == 0)
{
obj* x_875; obj* x_877; obj* x_878; 
lean::dec(x_7);
lean::dec(x_0);
x_875 = lean::cnstr_get(x_872, 0);
if (lean::is_exclusive(x_872)) {
 x_877 = x_872;
} else {
 lean::inc(x_875);
 lean::dec(x_872);
 x_877 = lean::box(0);
}
if (lean::is_scalar(x_877)) {
 x_878 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_878 = x_877;
}
lean::cnstr_set(x_878, 0, x_875);
return x_878;
}
else
{
obj* x_879; obj* x_882; obj* x_884; obj* x_886; obj* x_887; obj* x_888; obj* x_889; 
x_879 = lean::cnstr_get(x_872, 0);
lean::inc(x_879);
lean::dec(x_872);
x_882 = lean::cnstr_get(x_879, 0);
x_884 = lean::cnstr_get(x_879, 1);
if (lean::is_exclusive(x_879)) {
 x_886 = x_879;
} else {
 lean::inc(x_882);
 lean::inc(x_884);
 lean::dec(x_879);
 x_886 = lean::box(0);
}
x_887 = l_lean_elaborator_to__pexpr___main___closed__33;
x_888 = l_lean_elaborator_expr_mk__annotation(x_887, x_882);
if (lean::is_scalar(x_886)) {
 x_889 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_889 = x_886;
}
lean::cnstr_set(x_889, 0, x_888);
lean::cnstr_set(x_889, 1, x_884);
x_14 = x_889;
goto lbl_15;
}
}
}
else
{
obj* x_891; obj* x_892; obj* x_896; obj* x_897; obj* x_899; obj* x_900; obj* x_903; obj* x_906; 
lean::dec(x_9);
x_891 = l_lean_parser_term_explicit_has__view;
x_892 = lean::cnstr_get(x_891, 0);
lean::inc(x_892);
lean::dec(x_891);
lean::inc(x_0);
x_896 = lean::apply_1(x_892, x_0);
x_897 = lean::cnstr_get(x_896, 0);
lean::inc(x_897);
x_899 = l_lean_parser_ident__univs_has__view;
x_900 = lean::cnstr_get(x_899, 1);
lean::inc(x_900);
lean::dec(x_899);
x_903 = lean::cnstr_get(x_896, 1);
lean::inc(x_903);
lean::dec(x_896);
x_906 = lean::apply_1(x_900, x_903);
if (lean::obj_tag(x_897) == 0)
{
obj* x_908; 
lean::dec(x_897);
x_908 = l_lean_elaborator_to__pexpr___main(x_906, x_1, x_2);
if (lean::obj_tag(x_908) == 0)
{
obj* x_911; obj* x_913; obj* x_914; 
lean::dec(x_7);
lean::dec(x_0);
x_911 = lean::cnstr_get(x_908, 0);
if (lean::is_exclusive(x_908)) {
 x_913 = x_908;
} else {
 lean::inc(x_911);
 lean::dec(x_908);
 x_913 = lean::box(0);
}
if (lean::is_scalar(x_913)) {
 x_914 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_914 = x_913;
}
lean::cnstr_set(x_914, 0, x_911);
return x_914;
}
else
{
obj* x_915; obj* x_918; obj* x_920; obj* x_922; obj* x_923; obj* x_924; obj* x_925; 
x_915 = lean::cnstr_get(x_908, 0);
lean::inc(x_915);
lean::dec(x_908);
x_918 = lean::cnstr_get(x_915, 0);
x_920 = lean::cnstr_get(x_915, 1);
if (lean::is_exclusive(x_915)) {
 x_922 = x_915;
} else {
 lean::inc(x_918);
 lean::inc(x_920);
 lean::dec(x_915);
 x_922 = lean::box(0);
}
x_923 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
x_924 = l_lean_elaborator_expr_mk__annotation(x_923, x_918);
if (lean::is_scalar(x_922)) {
 x_925 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_925 = x_922;
}
lean::cnstr_set(x_925, 0, x_924);
lean::cnstr_set(x_925, 1, x_920);
x_14 = x_925;
goto lbl_15;
}
}
else
{
obj* x_927; 
lean::dec(x_897);
x_927 = l_lean_elaborator_to__pexpr___main(x_906, x_1, x_2);
if (lean::obj_tag(x_927) == 0)
{
obj* x_930; obj* x_932; obj* x_933; 
lean::dec(x_7);
lean::dec(x_0);
x_930 = lean::cnstr_get(x_927, 0);
if (lean::is_exclusive(x_927)) {
 x_932 = x_927;
} else {
 lean::inc(x_930);
 lean::dec(x_927);
 x_932 = lean::box(0);
}
if (lean::is_scalar(x_932)) {
 x_933 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_933 = x_932;
}
lean::cnstr_set(x_933, 0, x_930);
return x_933;
}
else
{
obj* x_934; obj* x_937; obj* x_939; obj* x_941; obj* x_942; obj* x_943; obj* x_944; 
x_934 = lean::cnstr_get(x_927, 0);
lean::inc(x_934);
lean::dec(x_927);
x_937 = lean::cnstr_get(x_934, 0);
x_939 = lean::cnstr_get(x_934, 1);
if (lean::is_exclusive(x_934)) {
 x_941 = x_934;
} else {
 lean::inc(x_937);
 lean::inc(x_939);
 lean::dec(x_934);
 x_941 = lean::box(0);
}
x_942 = l_lean_elaborator_to__pexpr___main___closed__34;
x_943 = l_lean_elaborator_expr_mk__annotation(x_942, x_937);
if (lean::is_scalar(x_941)) {
 x_944 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_944 = x_941;
}
lean::cnstr_set(x_944, 0, x_943);
lean::cnstr_set(x_944, 1, x_939);
x_14 = x_944;
goto lbl_15;
}
}
}
}
else
{
obj* x_946; obj* x_947; obj* x_951; obj* x_952; 
lean::dec(x_9);
x_946 = l_lean_parser_term_projection_has__view;
x_947 = lean::cnstr_get(x_946, 0);
lean::inc(x_947);
lean::dec(x_946);
lean::inc(x_0);
x_951 = lean::apply_1(x_947, x_0);
x_952 = lean::cnstr_get(x_951, 2);
lean::inc(x_952);
if (lean::obj_tag(x_952) == 0)
{
obj* x_954; obj* x_957; obj* x_960; 
x_954 = lean::cnstr_get(x_951, 0);
lean::inc(x_954);
lean::dec(x_951);
x_957 = lean::cnstr_get(x_952, 0);
lean::inc(x_957);
lean::dec(x_952);
x_960 = l_lean_elaborator_to__pexpr___main(x_954, x_1, x_2);
if (lean::obj_tag(x_960) == 0)
{
obj* x_964; obj* x_966; obj* x_967; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_957);
x_964 = lean::cnstr_get(x_960, 0);
if (lean::is_exclusive(x_960)) {
 x_966 = x_960;
} else {
 lean::inc(x_964);
 lean::dec(x_960);
 x_966 = lean::box(0);
}
if (lean::is_scalar(x_966)) {
 x_967 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_967 = x_966;
}
lean::cnstr_set(x_967, 0, x_964);
return x_967;
}
else
{
obj* x_968; obj* x_971; obj* x_973; obj* x_975; obj* x_976; obj* x_979; obj* x_980; obj* x_981; obj* x_982; obj* x_984; obj* x_985; 
x_968 = lean::cnstr_get(x_960, 0);
lean::inc(x_968);
lean::dec(x_960);
x_971 = lean::cnstr_get(x_968, 0);
x_973 = lean::cnstr_get(x_968, 1);
if (lean::is_exclusive(x_968)) {
 x_975 = x_968;
} else {
 lean::inc(x_971);
 lean::inc(x_973);
 lean::dec(x_968);
 x_975 = lean::box(0);
}
x_976 = lean::cnstr_get(x_957, 2);
lean::inc(x_976);
lean::dec(x_957);
x_979 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_979, 0, x_976);
x_980 = lean::box(0);
x_981 = l_lean_elaborator_to__pexpr___main___closed__35;
x_982 = l_lean_kvmap_insert__core___main(x_980, x_981, x_979);
lean::dec(x_979);
x_984 = lean_expr_mk_mdata(x_982, x_971);
if (lean::is_scalar(x_975)) {
 x_985 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_985 = x_975;
}
lean::cnstr_set(x_985, 0, x_984);
lean::cnstr_set(x_985, 1, x_973);
x_14 = x_985;
goto lbl_15;
}
}
else
{
obj* x_986; obj* x_989; obj* x_992; 
x_986 = lean::cnstr_get(x_951, 0);
lean::inc(x_986);
lean::dec(x_951);
x_989 = lean::cnstr_get(x_952, 0);
lean::inc(x_989);
lean::dec(x_952);
x_992 = l_lean_elaborator_to__pexpr___main(x_986, x_1, x_2);
if (lean::obj_tag(x_992) == 0)
{
obj* x_996; obj* x_998; obj* x_999; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_989);
x_996 = lean::cnstr_get(x_992, 0);
if (lean::is_exclusive(x_992)) {
 x_998 = x_992;
} else {
 lean::inc(x_996);
 lean::dec(x_992);
 x_998 = lean::box(0);
}
if (lean::is_scalar(x_998)) {
 x_999 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_999 = x_998;
}
lean::cnstr_set(x_999, 0, x_996);
return x_999;
}
else
{
obj* x_1000; obj* x_1003; obj* x_1005; obj* x_1007; obj* x_1008; obj* x_1009; obj* x_1010; obj* x_1011; obj* x_1012; obj* x_1014; obj* x_1015; 
x_1000 = lean::cnstr_get(x_992, 0);
lean::inc(x_1000);
lean::dec(x_992);
x_1003 = lean::cnstr_get(x_1000, 0);
x_1005 = lean::cnstr_get(x_1000, 1);
if (lean::is_exclusive(x_1000)) {
 x_1007 = x_1000;
} else {
 lean::inc(x_1003);
 lean::inc(x_1005);
 lean::dec(x_1000);
 x_1007 = lean::box(0);
}
x_1008 = l_lean_parser_number_view_to__nat___main(x_989);
x_1009 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1009, 0, x_1008);
x_1010 = lean::box(0);
x_1011 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1012 = l_lean_kvmap_insert__core___main(x_1010, x_1011, x_1009);
lean::dec(x_1009);
x_1014 = lean_expr_mk_mdata(x_1012, x_1003);
if (lean::is_scalar(x_1007)) {
 x_1015 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1015 = x_1007;
}
lean::cnstr_set(x_1015, 0, x_1014);
lean::cnstr_set(x_1015, 1, x_1005);
x_14 = x_1015;
goto lbl_15;
}
}
}
}
else
{
obj* x_1017; obj* x_1018; obj* x_1022; obj* x_1023; 
lean::dec(x_9);
x_1017 = l_lean_parser_term_let_has__view;
x_1018 = lean::cnstr_get(x_1017, 0);
lean::inc(x_1018);
lean::dec(x_1017);
lean::inc(x_0);
x_1022 = lean::apply_1(x_1018, x_0);
x_1023 = lean::cnstr_get(x_1022, 1);
lean::inc(x_1023);
if (lean::obj_tag(x_1023) == 0)
{
obj* x_1025; obj* x_1028; 
x_1025 = lean::cnstr_get(x_1023, 0);
lean::inc(x_1025);
lean::dec(x_1023);
x_1028 = lean::cnstr_get(x_1025, 1);
lean::inc(x_1028);
if (lean::obj_tag(x_1028) == 0)
{
obj* x_1030; 
x_1030 = lean::cnstr_get(x_1025, 2);
lean::inc(x_1030);
if (lean::obj_tag(x_1030) == 0)
{
obj* x_1034; obj* x_1035; 
lean::dec(x_1022);
lean::dec(x_1025);
x_1034 = l_lean_elaborator_to__pexpr___main___closed__36;
x_1035 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1034, x_1, x_2);
if (lean::obj_tag(x_1035) == 0)
{
obj* x_1038; obj* x_1040; obj* x_1041; 
lean::dec(x_7);
lean::dec(x_0);
x_1038 = lean::cnstr_get(x_1035, 0);
if (lean::is_exclusive(x_1035)) {
 x_1040 = x_1035;
} else {
 lean::inc(x_1038);
 lean::dec(x_1035);
 x_1040 = lean::box(0);
}
if (lean::is_scalar(x_1040)) {
 x_1041 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1041 = x_1040;
}
lean::cnstr_set(x_1041, 0, x_1038);
return x_1041;
}
else
{
obj* x_1042; 
x_1042 = lean::cnstr_get(x_1035, 0);
lean::inc(x_1042);
lean::dec(x_1035);
x_14 = x_1042;
goto lbl_15;
}
}
else
{
obj* x_1045; obj* x_1048; obj* x_1051; obj* x_1054; 
x_1045 = lean::cnstr_get(x_1025, 0);
lean::inc(x_1045);
lean::dec(x_1025);
x_1048 = lean::cnstr_get(x_1030, 0);
lean::inc(x_1048);
lean::dec(x_1030);
x_1051 = lean::cnstr_get(x_1048, 1);
lean::inc(x_1051);
lean::dec(x_1048);
x_1054 = l_lean_elaborator_to__pexpr___main(x_1051, x_1, x_2);
if (lean::obj_tag(x_1054) == 0)
{
obj* x_1059; obj* x_1061; obj* x_1062; 
lean::dec(x_1045);
lean::dec(x_1022);
lean::dec(x_7);
lean::dec(x_0);
x_1059 = lean::cnstr_get(x_1054, 0);
if (lean::is_exclusive(x_1054)) {
 x_1061 = x_1054;
} else {
 lean::inc(x_1059);
 lean::dec(x_1054);
 x_1061 = lean::box(0);
}
if (lean::is_scalar(x_1061)) {
 x_1062 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1062 = x_1061;
}
lean::cnstr_set(x_1062, 0, x_1059);
return x_1062;
}
else
{
obj* x_1063; obj* x_1066; obj* x_1068; obj* x_1071; obj* x_1073; 
x_1063 = lean::cnstr_get(x_1054, 0);
lean::inc(x_1063);
lean::dec(x_1054);
x_1066 = lean::cnstr_get(x_1063, 0);
lean::inc(x_1066);
x_1068 = lean::cnstr_get(x_1063, 1);
lean::inc(x_1068);
lean::dec(x_1063);
x_1071 = lean::cnstr_get(x_1022, 3);
lean::inc(x_1071);
x_1073 = l_lean_elaborator_to__pexpr___main(x_1071, x_1, x_1068);
lean::dec(x_1068);
if (lean::obj_tag(x_1073) == 0)
{
obj* x_1080; obj* x_1082; obj* x_1083; 
lean::dec(x_1045);
lean::dec(x_1022);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1066);
x_1080 = lean::cnstr_get(x_1073, 0);
if (lean::is_exclusive(x_1073)) {
 x_1082 = x_1073;
} else {
 lean::inc(x_1080);
 lean::dec(x_1073);
 x_1082 = lean::box(0);
}
if (lean::is_scalar(x_1082)) {
 x_1083 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1083 = x_1082;
}
lean::cnstr_set(x_1083, 0, x_1080);
return x_1083;
}
else
{
obj* x_1084; obj* x_1087; obj* x_1089; obj* x_1092; obj* x_1095; 
x_1084 = lean::cnstr_get(x_1073, 0);
lean::inc(x_1084);
lean::dec(x_1073);
x_1087 = lean::cnstr_get(x_1084, 0);
lean::inc(x_1087);
x_1089 = lean::cnstr_get(x_1084, 1);
lean::inc(x_1089);
lean::dec(x_1084);
x_1092 = lean::cnstr_get(x_1022, 5);
lean::inc(x_1092);
lean::dec(x_1022);
x_1095 = l_lean_elaborator_to__pexpr___main(x_1092, x_1, x_1089);
lean::dec(x_1089);
if (lean::obj_tag(x_1095) == 0)
{
obj* x_1102; obj* x_1104; obj* x_1105; 
lean::dec(x_1087);
lean::dec(x_1045);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1066);
x_1102 = lean::cnstr_get(x_1095, 0);
if (lean::is_exclusive(x_1095)) {
 x_1104 = x_1095;
} else {
 lean::inc(x_1102);
 lean::dec(x_1095);
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
obj* x_1106; obj* x_1109; obj* x_1111; obj* x_1113; obj* x_1114; obj* x_1115; obj* x_1116; 
x_1106 = lean::cnstr_get(x_1095, 0);
lean::inc(x_1106);
lean::dec(x_1095);
x_1109 = lean::cnstr_get(x_1106, 0);
x_1111 = lean::cnstr_get(x_1106, 1);
if (lean::is_exclusive(x_1106)) {
 x_1113 = x_1106;
} else {
 lean::inc(x_1109);
 lean::inc(x_1111);
 lean::dec(x_1106);
 x_1113 = lean::box(0);
}
x_1114 = l_lean_elaborator_mangle__ident(x_1045);
x_1115 = lean_expr_mk_let(x_1114, x_1066, x_1087, x_1109);
if (lean::is_scalar(x_1113)) {
 x_1116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1116 = x_1113;
}
lean::cnstr_set(x_1116, 0, x_1115);
lean::cnstr_set(x_1116, 1, x_1111);
x_14 = x_1116;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1120; obj* x_1121; 
lean::dec(x_1022);
lean::dec(x_1028);
lean::dec(x_1025);
x_1120 = l_lean_elaborator_to__pexpr___main___closed__36;
x_1121 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1120, x_1, x_2);
if (lean::obj_tag(x_1121) == 0)
{
obj* x_1124; obj* x_1126; obj* x_1127; 
lean::dec(x_7);
lean::dec(x_0);
x_1124 = lean::cnstr_get(x_1121, 0);
if (lean::is_exclusive(x_1121)) {
 x_1126 = x_1121;
} else {
 lean::inc(x_1124);
 lean::dec(x_1121);
 x_1126 = lean::box(0);
}
if (lean::is_scalar(x_1126)) {
 x_1127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1127 = x_1126;
}
lean::cnstr_set(x_1127, 0, x_1124);
return x_1127;
}
else
{
obj* x_1128; 
x_1128 = lean::cnstr_get(x_1121, 0);
lean::inc(x_1128);
lean::dec(x_1121);
x_14 = x_1128;
goto lbl_15;
}
}
}
else
{
obj* x_1133; obj* x_1134; 
lean::dec(x_1022);
lean::dec(x_1023);
x_1133 = l_lean_elaborator_to__pexpr___main___closed__36;
x_1134 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1133, x_1, x_2);
if (lean::obj_tag(x_1134) == 0)
{
obj* x_1137; obj* x_1139; obj* x_1140; 
lean::dec(x_7);
lean::dec(x_0);
x_1137 = lean::cnstr_get(x_1134, 0);
if (lean::is_exclusive(x_1134)) {
 x_1139 = x_1134;
} else {
 lean::inc(x_1137);
 lean::dec(x_1134);
 x_1139 = lean::box(0);
}
if (lean::is_scalar(x_1139)) {
 x_1140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1140 = x_1139;
}
lean::cnstr_set(x_1140, 0, x_1137);
return x_1140;
}
else
{
obj* x_1141; 
x_1141 = lean::cnstr_get(x_1134, 0);
lean::inc(x_1141);
lean::dec(x_1134);
x_14 = x_1141;
goto lbl_15;
}
}
}
}
else
{
obj* x_1145; obj* x_1146; obj* x_1150; obj* x_1151; obj* x_1153; 
lean::dec(x_9);
x_1145 = l_lean_parser_term_show_has__view;
x_1146 = lean::cnstr_get(x_1145, 0);
lean::inc(x_1146);
lean::dec(x_1145);
lean::inc(x_0);
x_1150 = lean::apply_1(x_1146, x_0);
x_1151 = lean::cnstr_get(x_1150, 1);
lean::inc(x_1151);
x_1153 = l_lean_elaborator_to__pexpr___main(x_1151, x_1, x_2);
if (lean::obj_tag(x_1153) == 0)
{
obj* x_1157; obj* x_1159; obj* x_1160; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1150);
x_1157 = lean::cnstr_get(x_1153, 0);
if (lean::is_exclusive(x_1153)) {
 x_1159 = x_1153;
} else {
 lean::inc(x_1157);
 lean::dec(x_1153);
 x_1159 = lean::box(0);
}
if (lean::is_scalar(x_1159)) {
 x_1160 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1160 = x_1159;
}
lean::cnstr_set(x_1160, 0, x_1157);
return x_1160;
}
else
{
obj* x_1161; obj* x_1164; obj* x_1166; obj* x_1169; obj* x_1172; obj* x_1175; 
x_1161 = lean::cnstr_get(x_1153, 0);
lean::inc(x_1161);
lean::dec(x_1153);
x_1164 = lean::cnstr_get(x_1161, 0);
lean::inc(x_1164);
x_1166 = lean::cnstr_get(x_1161, 1);
lean::inc(x_1166);
lean::dec(x_1161);
x_1169 = lean::cnstr_get(x_1150, 3);
lean::inc(x_1169);
lean::dec(x_1150);
x_1172 = lean::cnstr_get(x_1169, 1);
lean::inc(x_1172);
lean::dec(x_1169);
x_1175 = l_lean_elaborator_to__pexpr___main(x_1172, x_1, x_1166);
lean::dec(x_1166);
if (lean::obj_tag(x_1175) == 0)
{
obj* x_1180; obj* x_1182; obj* x_1183; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1164);
x_1180 = lean::cnstr_get(x_1175, 0);
if (lean::is_exclusive(x_1175)) {
 x_1182 = x_1175;
} else {
 lean::inc(x_1180);
 lean::dec(x_1175);
 x_1182 = lean::box(0);
}
if (lean::is_scalar(x_1182)) {
 x_1183 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1183 = x_1182;
}
lean::cnstr_set(x_1183, 0, x_1180);
return x_1183;
}
else
{
obj* x_1184; obj* x_1187; obj* x_1189; obj* x_1191; obj* x_1192; uint8 x_1193; obj* x_1194; obj* x_1195; obj* x_1196; obj* x_1197; obj* x_1198; obj* x_1199; 
x_1184 = lean::cnstr_get(x_1175, 0);
lean::inc(x_1184);
lean::dec(x_1175);
x_1187 = lean::cnstr_get(x_1184, 0);
x_1189 = lean::cnstr_get(x_1184, 1);
if (lean::is_exclusive(x_1184)) {
 x_1191 = x_1184;
} else {
 lean::inc(x_1187);
 lean::inc(x_1189);
 lean::dec(x_1184);
 x_1191 = lean::box(0);
}
x_1192 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1193 = 0;
x_1194 = l_lean_elaborator_to__pexpr___main___closed__38;
x_1195 = lean_expr_mk_lambda(x_1192, x_1193, x_1164, x_1194);
x_1196 = lean_expr_mk_app(x_1195, x_1187);
x_1197 = l_lean_elaborator_to__pexpr___main___closed__39;
x_1198 = l_lean_elaborator_expr_mk__annotation(x_1197, x_1196);
if (lean::is_scalar(x_1191)) {
 x_1199 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1199 = x_1191;
}
lean::cnstr_set(x_1199, 0, x_1198);
lean::cnstr_set(x_1199, 1, x_1189);
x_14 = x_1199;
goto lbl_15;
}
}
}
}
else
{
obj* x_1201; obj* x_1202; obj* x_1206; obj* x_1207; obj* x_1209; obj* x_1211; 
lean::dec(x_9);
x_1201 = l_lean_parser_term_have_has__view;
x_1202 = lean::cnstr_get(x_1201, 0);
lean::inc(x_1202);
lean::dec(x_1201);
lean::inc(x_0);
x_1206 = lean::apply_1(x_1202, x_0);
x_1209 = lean::cnstr_get(x_1206, 2);
lean::inc(x_1209);
x_1211 = l_lean_elaborator_to__pexpr___main(x_1209, x_1, x_2);
if (lean::obj_tag(x_1211) == 0)
{
obj* x_1215; obj* x_1217; obj* x_1218; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1206);
x_1215 = lean::cnstr_get(x_1211, 0);
if (lean::is_exclusive(x_1211)) {
 x_1217 = x_1211;
} else {
 lean::inc(x_1215);
 lean::dec(x_1211);
 x_1217 = lean::box(0);
}
if (lean::is_scalar(x_1217)) {
 x_1218 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1218 = x_1217;
}
lean::cnstr_set(x_1218, 0, x_1215);
return x_1218;
}
else
{
obj* x_1219; obj* x_1222; obj* x_1224; obj* x_1227; obj* x_1229; 
x_1219 = lean::cnstr_get(x_1211, 0);
lean::inc(x_1219);
lean::dec(x_1211);
x_1222 = lean::cnstr_get(x_1219, 0);
lean::inc(x_1222);
x_1224 = lean::cnstr_get(x_1219, 1);
lean::inc(x_1224);
lean::dec(x_1219);
x_1227 = lean::cnstr_get(x_1206, 5);
lean::inc(x_1227);
x_1229 = l_lean_elaborator_to__pexpr___main(x_1227, x_1, x_1224);
lean::dec(x_1224);
if (lean::obj_tag(x_1229) == 0)
{
obj* x_1235; obj* x_1237; obj* x_1238; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1206);
lean::dec(x_1222);
x_1235 = lean::cnstr_get(x_1229, 0);
if (lean::is_exclusive(x_1229)) {
 x_1237 = x_1229;
} else {
 lean::inc(x_1235);
 lean::dec(x_1229);
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
obj* x_1239; obj* x_1242; obj* x_1244; obj* x_1246; obj* x_1247; obj* x_1249; obj* x_1250; obj* x_1251; obj* x_1252; obj* x_1253; obj* x_1254; uint8 x_1256; obj* x_1257; obj* x_1258; 
x_1239 = lean::cnstr_get(x_1229, 0);
lean::inc(x_1239);
lean::dec(x_1229);
x_1242 = lean::cnstr_get(x_1239, 0);
x_1244 = lean::cnstr_get(x_1239, 1);
if (lean::is_exclusive(x_1239)) {
 x_1246 = x_1239;
} else {
 lean::inc(x_1242);
 lean::inc(x_1244);
 lean::dec(x_1239);
 x_1246 = lean::box(0);
}
x_1247 = lean::cnstr_get(x_1206, 1);
lean::inc(x_1247);
x_1249 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1250 = l_option_map___rarg(x_1249, x_1247);
x_1251 = l_lean_elaborator_to__pexpr___main___closed__28;
x_1252 = l_option_map___rarg(x_1251, x_1250);
x_1253 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1254 = l_option_get__or__else___main___rarg(x_1252, x_1253);
lean::dec(x_1252);
x_1256 = 0;
x_1257 = lean_expr_mk_lambda(x_1254, x_1256, x_1222, x_1242);
if (lean::is_scalar(x_1246)) {
 x_1258 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1258 = x_1246;
}
lean::cnstr_set(x_1258, 0, x_1257);
lean::cnstr_set(x_1258, 1, x_1244);
x_1207 = x_1258;
goto lbl_1208;
}
}
lbl_1208:
{
obj* x_1259; 
x_1259 = lean::cnstr_get(x_1206, 3);
lean::inc(x_1259);
lean::dec(x_1206);
if (lean::obj_tag(x_1259) == 0)
{
obj* x_1262; obj* x_1264; obj* x_1267; obj* x_1270; obj* x_1273; 
x_1262 = lean::cnstr_get(x_1207, 0);
lean::inc(x_1262);
x_1264 = lean::cnstr_get(x_1207, 1);
lean::inc(x_1264);
lean::dec(x_1207);
x_1267 = lean::cnstr_get(x_1259, 0);
lean::inc(x_1267);
lean::dec(x_1259);
x_1270 = lean::cnstr_get(x_1267, 1);
lean::inc(x_1270);
lean::dec(x_1267);
x_1273 = l_lean_elaborator_to__pexpr___main(x_1270, x_1, x_1264);
lean::dec(x_1264);
if (lean::obj_tag(x_1273) == 0)
{
obj* x_1278; obj* x_1280; obj* x_1281; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1262);
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
obj* x_1282; obj* x_1285; obj* x_1287; obj* x_1289; obj* x_1290; obj* x_1291; obj* x_1292; obj* x_1293; 
x_1282 = lean::cnstr_get(x_1273, 0);
lean::inc(x_1282);
lean::dec(x_1273);
x_1285 = lean::cnstr_get(x_1282, 0);
x_1287 = lean::cnstr_get(x_1282, 1);
if (lean::is_exclusive(x_1282)) {
 x_1289 = x_1282;
} else {
 lean::inc(x_1285);
 lean::inc(x_1287);
 lean::dec(x_1282);
 x_1289 = lean::box(0);
}
x_1290 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1291 = l_lean_elaborator_expr_mk__annotation(x_1290, x_1262);
x_1292 = lean_expr_mk_app(x_1291, x_1285);
if (lean::is_scalar(x_1289)) {
 x_1293 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1293 = x_1289;
}
lean::cnstr_set(x_1293, 0, x_1292);
lean::cnstr_set(x_1293, 1, x_1287);
x_14 = x_1293;
goto lbl_15;
}
}
else
{
obj* x_1294; obj* x_1296; obj* x_1299; obj* x_1302; obj* x_1305; obj* x_1308; 
x_1294 = lean::cnstr_get(x_1207, 0);
lean::inc(x_1294);
x_1296 = lean::cnstr_get(x_1207, 1);
lean::inc(x_1296);
lean::dec(x_1207);
x_1299 = lean::cnstr_get(x_1259, 0);
lean::inc(x_1299);
lean::dec(x_1259);
x_1302 = lean::cnstr_get(x_1299, 1);
lean::inc(x_1302);
lean::dec(x_1299);
x_1305 = lean::cnstr_get(x_1302, 1);
lean::inc(x_1305);
lean::dec(x_1302);
x_1308 = l_lean_elaborator_to__pexpr___main(x_1305, x_1, x_1296);
lean::dec(x_1296);
if (lean::obj_tag(x_1308) == 0)
{
obj* x_1313; obj* x_1315; obj* x_1316; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1294);
x_1313 = lean::cnstr_get(x_1308, 0);
if (lean::is_exclusive(x_1308)) {
 x_1315 = x_1308;
} else {
 lean::inc(x_1313);
 lean::dec(x_1308);
 x_1315 = lean::box(0);
}
if (lean::is_scalar(x_1315)) {
 x_1316 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1316 = x_1315;
}
lean::cnstr_set(x_1316, 0, x_1313);
return x_1316;
}
else
{
obj* x_1317; obj* x_1320; obj* x_1322; obj* x_1324; obj* x_1325; obj* x_1326; obj* x_1327; obj* x_1328; 
x_1317 = lean::cnstr_get(x_1308, 0);
lean::inc(x_1317);
lean::dec(x_1308);
x_1320 = lean::cnstr_get(x_1317, 0);
x_1322 = lean::cnstr_get(x_1317, 1);
if (lean::is_exclusive(x_1317)) {
 x_1324 = x_1317;
} else {
 lean::inc(x_1320);
 lean::inc(x_1322);
 lean::dec(x_1317);
 x_1324 = lean::box(0);
}
x_1325 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1326 = l_lean_elaborator_expr_mk__annotation(x_1325, x_1294);
x_1327 = lean_expr_mk_app(x_1326, x_1320);
if (lean::is_scalar(x_1324)) {
 x_1328 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1328 = x_1324;
}
lean::cnstr_set(x_1328, 0, x_1327);
lean::cnstr_set(x_1328, 1, x_1322);
x_14 = x_1328;
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
obj* x_1331; 
x_1331 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1331) == 0)
{
obj* x_1333; obj* x_1335; obj* x_1336; 
x_1333 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_2);
x_1335 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1335, 0, x_1333);
lean::cnstr_set(x_1335, 1, x_2);
x_1336 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1336, 0, x_1335);
return x_1336;
}
else
{
obj* x_1337; obj* x_1340; obj* x_1341; obj* x_1342; obj* x_1344; obj* x_1345; obj* x_1347; obj* x_1348; obj* x_1350; obj* x_1353; obj* x_1354; obj* x_1356; obj* x_1357; obj* x_1359; obj* x_1360; 
x_1337 = lean::cnstr_get(x_1331, 0);
lean::inc(x_1337);
lean::dec(x_1331);
x_1340 = lean::cnstr_get(x_1, 0);
x_1341 = lean::cnstr_get(x_1340, 2);
x_1342 = l_lean_file__map_to__position(x_1341, x_1337);
lean::dec(x_1337);
x_1344 = lean::box(0);
x_1345 = lean::cnstr_get(x_1342, 1);
lean::inc(x_1345);
x_1347 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1348 = l_lean_kvmap_set__nat(x_1344, x_1347, x_1345);
lean::dec(x_1345);
x_1350 = lean::cnstr_get(x_1342, 0);
lean::inc(x_1350);
lean::dec(x_1342);
x_1353 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1354 = l_lean_kvmap_set__nat(x_1348, x_1353, x_1350);
lean::dec(x_1350);
x_1356 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1357 = lean_expr_mk_mdata(x_1354, x_1356);
lean::inc(x_2);
x_1359 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1359, 0, x_1357);
lean::cnstr_set(x_1359, 1, x_2);
x_1360 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1360, 0, x_1359);
return x_1360;
}
}
else
{
obj* x_1362; obj* x_1364; obj* x_1365; 
lean::dec(x_0);
x_1362 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_2);
x_1364 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1364, 0, x_1362);
lean::cnstr_set(x_1364, 1, x_2);
x_1365 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1365, 0, x_1364);
return x_1365;
}
}
}
else
{
obj* x_1367; obj* x_1368; obj* x_1372; obj* x_1373; obj* x_1376; obj* x_1377; obj* x_1378; obj* x_1379; 
lean::dec(x_9);
x_1367 = l_lean_parser_term_anonymous__constructor_has__view;
x_1368 = lean::cnstr_get(x_1367, 0);
lean::inc(x_1368);
lean::dec(x_1367);
lean::inc(x_0);
x_1372 = lean::apply_1(x_1368, x_0);
x_1373 = lean::cnstr_get(x_1372, 1);
lean::inc(x_1373);
lean::dec(x_1372);
x_1376 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_1373);
x_1377 = l_lean_expander_get__opt__type___main___closed__1;
x_1378 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_1377, x_1376);
x_1379 = l_lean_elaborator_to__pexpr___main(x_1378, x_1, x_2);
if (lean::obj_tag(x_1379) == 0)
{
obj* x_1382; obj* x_1384; obj* x_1385; 
lean::dec(x_7);
lean::dec(x_0);
x_1382 = lean::cnstr_get(x_1379, 0);
if (lean::is_exclusive(x_1379)) {
 x_1384 = x_1379;
} else {
 lean::inc(x_1382);
 lean::dec(x_1379);
 x_1384 = lean::box(0);
}
if (lean::is_scalar(x_1384)) {
 x_1385 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1385 = x_1384;
}
lean::cnstr_set(x_1385, 0, x_1382);
return x_1385;
}
else
{
obj* x_1386; obj* x_1389; obj* x_1391; obj* x_1393; obj* x_1394; obj* x_1395; obj* x_1396; 
x_1386 = lean::cnstr_get(x_1379, 0);
lean::inc(x_1386);
lean::dec(x_1379);
x_1389 = lean::cnstr_get(x_1386, 0);
x_1391 = lean::cnstr_get(x_1386, 1);
if (lean::is_exclusive(x_1386)) {
 x_1393 = x_1386;
} else {
 lean::inc(x_1389);
 lean::inc(x_1391);
 lean::dec(x_1386);
 x_1393 = lean::box(0);
}
x_1394 = l_lean_elaborator_to__pexpr___main___closed__43;
x_1395 = l_lean_elaborator_expr_mk__annotation(x_1394, x_1389);
if (lean::is_scalar(x_1393)) {
 x_1396 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1396 = x_1393;
}
lean::cnstr_set(x_1396, 0, x_1395);
lean::cnstr_set(x_1396, 1, x_1391);
x_14 = x_1396;
goto lbl_15;
}
}
}
else
{
obj* x_1398; obj* x_1399; obj* x_1403; obj* x_1404; obj* x_1405; obj* x_1408; obj* x_1410; 
lean::dec(x_9);
x_1398 = l_lean_parser_term_sort__app_has__view;
x_1399 = lean::cnstr_get(x_1398, 0);
lean::inc(x_1399);
lean::dec(x_1398);
lean::inc(x_0);
x_1403 = lean::apply_1(x_1399, x_0);
x_1404 = l_lean_parser_term_sort_has__view;
x_1405 = lean::cnstr_get(x_1404, 0);
lean::inc(x_1405);
lean::dec(x_1404);
x_1408 = lean::cnstr_get(x_1403, 0);
lean::inc(x_1408);
x_1410 = lean::apply_1(x_1405, x_1408);
if (lean::obj_tag(x_1410) == 0)
{
obj* x_1412; obj* x_1415; 
lean::dec(x_1410);
x_1412 = lean::cnstr_get(x_1403, 1);
lean::inc(x_1412);
lean::dec(x_1403);
x_1415 = l_lean_elaborator_to__level___main(x_1412, x_1, x_2);
if (lean::obj_tag(x_1415) == 0)
{
obj* x_1418; obj* x_1420; obj* x_1421; 
lean::dec(x_7);
lean::dec(x_0);
x_1418 = lean::cnstr_get(x_1415, 0);
if (lean::is_exclusive(x_1415)) {
 x_1420 = x_1415;
} else {
 lean::inc(x_1418);
 lean::dec(x_1415);
 x_1420 = lean::box(0);
}
if (lean::is_scalar(x_1420)) {
 x_1421 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1421 = x_1420;
}
lean::cnstr_set(x_1421, 0, x_1418);
return x_1421;
}
else
{
obj* x_1422; obj* x_1425; obj* x_1427; obj* x_1429; obj* x_1430; obj* x_1431; 
x_1422 = lean::cnstr_get(x_1415, 0);
lean::inc(x_1422);
lean::dec(x_1415);
x_1425 = lean::cnstr_get(x_1422, 0);
x_1427 = lean::cnstr_get(x_1422, 1);
if (lean::is_exclusive(x_1422)) {
 x_1429 = x_1422;
} else {
 lean::inc(x_1425);
 lean::inc(x_1427);
 lean::dec(x_1422);
 x_1429 = lean::box(0);
}
x_1430 = lean_expr_mk_sort(x_1425);
if (lean::is_scalar(x_1429)) {
 x_1431 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1431 = x_1429;
}
lean::cnstr_set(x_1431, 0, x_1430);
lean::cnstr_set(x_1431, 1, x_1427);
x_14 = x_1431;
goto lbl_15;
}
}
else
{
obj* x_1433; obj* x_1436; 
lean::dec(x_1410);
x_1433 = lean::cnstr_get(x_1403, 1);
lean::inc(x_1433);
lean::dec(x_1403);
x_1436 = l_lean_elaborator_to__level___main(x_1433, x_1, x_2);
if (lean::obj_tag(x_1436) == 0)
{
obj* x_1439; obj* x_1441; obj* x_1442; 
lean::dec(x_7);
lean::dec(x_0);
x_1439 = lean::cnstr_get(x_1436, 0);
if (lean::is_exclusive(x_1436)) {
 x_1441 = x_1436;
} else {
 lean::inc(x_1439);
 lean::dec(x_1436);
 x_1441 = lean::box(0);
}
if (lean::is_scalar(x_1441)) {
 x_1442 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1442 = x_1441;
}
lean::cnstr_set(x_1442, 0, x_1439);
return x_1442;
}
else
{
obj* x_1443; obj* x_1446; obj* x_1448; obj* x_1450; obj* x_1451; obj* x_1452; obj* x_1453; 
x_1443 = lean::cnstr_get(x_1436, 0);
lean::inc(x_1443);
lean::dec(x_1436);
x_1446 = lean::cnstr_get(x_1443, 0);
x_1448 = lean::cnstr_get(x_1443, 1);
if (lean::is_exclusive(x_1443)) {
 x_1450 = x_1443;
} else {
 lean::inc(x_1446);
 lean::inc(x_1448);
 lean::dec(x_1443);
 x_1450 = lean::box(0);
}
x_1451 = level_mk_succ(x_1446);
x_1452 = lean_expr_mk_sort(x_1451);
if (lean::is_scalar(x_1450)) {
 x_1453 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1453 = x_1450;
}
lean::cnstr_set(x_1453, 0, x_1452);
lean::cnstr_set(x_1453, 1, x_1448);
x_14 = x_1453;
goto lbl_15;
}
}
}
}
else
{
obj* x_1456; obj* x_1457; obj* x_1461; 
lean::dec(x_9);
lean::dec(x_7);
x_1456 = l_lean_parser_term_sort_has__view;
x_1457 = lean::cnstr_get(x_1456, 0);
lean::inc(x_1457);
lean::dec(x_1456);
lean::inc(x_0);
x_1461 = lean::apply_1(x_1457, x_0);
if (lean::obj_tag(x_1461) == 0)
{
lean::dec(x_1461);
if (x_21 == 0)
{
obj* x_1463; 
x_1463 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1463) == 0)
{
obj* x_1465; obj* x_1467; obj* x_1468; 
x_1465 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_2);
x_1467 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1467, 0, x_1465);
lean::cnstr_set(x_1467, 1, x_2);
x_1468 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1468, 0, x_1467);
return x_1468;
}
else
{
obj* x_1469; obj* x_1472; obj* x_1473; obj* x_1474; obj* x_1476; obj* x_1477; obj* x_1479; obj* x_1480; obj* x_1482; obj* x_1485; obj* x_1486; obj* x_1488; obj* x_1489; obj* x_1491; obj* x_1492; 
x_1469 = lean::cnstr_get(x_1463, 0);
lean::inc(x_1469);
lean::dec(x_1463);
x_1472 = lean::cnstr_get(x_1, 0);
x_1473 = lean::cnstr_get(x_1472, 2);
x_1474 = l_lean_file__map_to__position(x_1473, x_1469);
lean::dec(x_1469);
x_1476 = lean::box(0);
x_1477 = lean::cnstr_get(x_1474, 1);
lean::inc(x_1477);
x_1479 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1480 = l_lean_kvmap_set__nat(x_1476, x_1479, x_1477);
lean::dec(x_1477);
x_1482 = lean::cnstr_get(x_1474, 0);
lean::inc(x_1482);
lean::dec(x_1474);
x_1485 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1486 = l_lean_kvmap_set__nat(x_1480, x_1485, x_1482);
lean::dec(x_1482);
x_1488 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
x_1489 = lean_expr_mk_mdata(x_1486, x_1488);
lean::inc(x_2);
x_1491 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1491, 0, x_1489);
lean::cnstr_set(x_1491, 1, x_2);
x_1492 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1492, 0, x_1491);
return x_1492;
}
}
else
{
obj* x_1494; obj* x_1496; obj* x_1497; 
lean::dec(x_0);
x_1494 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9___closed__1;
lean::inc(x_2);
x_1496 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1496, 0, x_1494);
lean::cnstr_set(x_1496, 1, x_2);
x_1497 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1497, 0, x_1496);
return x_1497;
}
}
else
{
lean::dec(x_1461);
if (x_21 == 0)
{
obj* x_1499; 
x_1499 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1499) == 0)
{
obj* x_1501; obj* x_1503; obj* x_1504; 
x_1501 = l_lean_elaborator_to__pexpr___main___closed__44;
lean::inc(x_2);
x_1503 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1503, 0, x_1501);
lean::cnstr_set(x_1503, 1, x_2);
x_1504 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1504, 0, x_1503);
return x_1504;
}
else
{
obj* x_1505; obj* x_1508; obj* x_1509; obj* x_1510; obj* x_1512; obj* x_1513; obj* x_1515; obj* x_1516; obj* x_1518; obj* x_1521; obj* x_1522; obj* x_1524; obj* x_1525; obj* x_1527; obj* x_1528; 
x_1505 = lean::cnstr_get(x_1499, 0);
lean::inc(x_1505);
lean::dec(x_1499);
x_1508 = lean::cnstr_get(x_1, 0);
x_1509 = lean::cnstr_get(x_1508, 2);
x_1510 = l_lean_file__map_to__position(x_1509, x_1505);
lean::dec(x_1505);
x_1512 = lean::box(0);
x_1513 = lean::cnstr_get(x_1510, 1);
lean::inc(x_1513);
x_1515 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1516 = l_lean_kvmap_set__nat(x_1512, x_1515, x_1513);
lean::dec(x_1513);
x_1518 = lean::cnstr_get(x_1510, 0);
lean::inc(x_1518);
lean::dec(x_1510);
x_1521 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1522 = l_lean_kvmap_set__nat(x_1516, x_1521, x_1518);
lean::dec(x_1518);
x_1524 = l_lean_elaborator_to__pexpr___main___closed__44;
x_1525 = lean_expr_mk_mdata(x_1522, x_1524);
lean::inc(x_2);
x_1527 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1527, 0, x_1525);
lean::cnstr_set(x_1527, 1, x_2);
x_1528 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1528, 0, x_1527);
return x_1528;
}
}
else
{
obj* x_1530; obj* x_1532; obj* x_1533; 
lean::dec(x_0);
x_1530 = l_lean_elaborator_to__pexpr___main___closed__44;
lean::inc(x_2);
x_1532 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1532, 0, x_1530);
lean::cnstr_set(x_1532, 1, x_2);
x_1533 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1533, 0, x_1532);
return x_1533;
}
}
}
}
else
{
obj* x_1535; obj* x_1536; obj* x_1540; obj* x_1541; 
lean::dec(x_9);
x_1535 = l_lean_parser_term_pi_has__view;
x_1536 = lean::cnstr_get(x_1535, 0);
lean::inc(x_1536);
lean::dec(x_1535);
lean::inc(x_0);
x_1540 = lean::apply_1(x_1536, x_0);
x_1541 = lean::cnstr_get(x_1540, 1);
lean::inc(x_1541);
if (lean::obj_tag(x_1541) == 0)
{
obj* x_1545; obj* x_1546; 
lean::dec(x_1541);
lean::dec(x_1540);
x_1545 = l_lean_elaborator_to__pexpr___main___closed__45;
x_1546 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1545, x_1, x_2);
if (lean::obj_tag(x_1546) == 0)
{
obj* x_1549; obj* x_1551; obj* x_1552; 
lean::dec(x_7);
lean::dec(x_0);
x_1549 = lean::cnstr_get(x_1546, 0);
if (lean::is_exclusive(x_1546)) {
 x_1551 = x_1546;
} else {
 lean::inc(x_1549);
 lean::dec(x_1546);
 x_1551 = lean::box(0);
}
if (lean::is_scalar(x_1551)) {
 x_1552 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1552 = x_1551;
}
lean::cnstr_set(x_1552, 0, x_1549);
return x_1552;
}
else
{
obj* x_1553; 
x_1553 = lean::cnstr_get(x_1546, 0);
lean::inc(x_1553);
lean::dec(x_1546);
x_14 = x_1553;
goto lbl_15;
}
}
else
{
obj* x_1556; obj* x_1559; obj* x_1561; obj* x_1563; obj* x_1566; obj* x_1568; obj* x_1571; 
x_1556 = lean::cnstr_get(x_1541, 0);
lean::inc(x_1556);
lean::dec(x_1541);
x_1559 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1556);
lean::dec(x_1556);
x_1561 = lean::cnstr_get(x_1559, 1);
lean::inc(x_1561);
x_1563 = lean::cnstr_get(x_1559, 0);
lean::inc(x_1563);
lean::dec(x_1559);
x_1566 = lean::cnstr_get(x_1561, 0);
lean::inc(x_1566);
x_1568 = lean::cnstr_get(x_1561, 1);
lean::inc(x_1568);
lean::dec(x_1561);
x_1571 = l_lean_elaborator_to__pexpr___main(x_1568, x_1, x_2);
if (lean::obj_tag(x_1571) == 0)
{
obj* x_1577; obj* x_1579; obj* x_1580; 
lean::dec(x_7);
lean::dec(x_1563);
lean::dec(x_0);
lean::dec(x_1540);
lean::dec(x_1566);
x_1577 = lean::cnstr_get(x_1571, 0);
if (lean::is_exclusive(x_1571)) {
 x_1579 = x_1571;
} else {
 lean::inc(x_1577);
 lean::dec(x_1571);
 x_1579 = lean::box(0);
}
if (lean::is_scalar(x_1579)) {
 x_1580 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1580 = x_1579;
}
lean::cnstr_set(x_1580, 0, x_1577);
return x_1580;
}
else
{
obj* x_1581; obj* x_1584; obj* x_1586; obj* x_1589; obj* x_1592; 
x_1581 = lean::cnstr_get(x_1571, 0);
lean::inc(x_1581);
lean::dec(x_1571);
x_1584 = lean::cnstr_get(x_1581, 0);
lean::inc(x_1584);
x_1586 = lean::cnstr_get(x_1581, 1);
lean::inc(x_1586);
lean::dec(x_1581);
x_1589 = lean::cnstr_get(x_1540, 3);
lean::inc(x_1589);
lean::dec(x_1540);
x_1592 = l_lean_elaborator_to__pexpr___main(x_1589, x_1, x_1586);
lean::dec(x_1586);
if (lean::obj_tag(x_1592) == 0)
{
obj* x_1599; obj* x_1601; obj* x_1602; 
lean::dec(x_1584);
lean::dec(x_7);
lean::dec(x_1563);
lean::dec(x_0);
lean::dec(x_1566);
x_1599 = lean::cnstr_get(x_1592, 0);
if (lean::is_exclusive(x_1592)) {
 x_1601 = x_1592;
} else {
 lean::inc(x_1599);
 lean::dec(x_1592);
 x_1601 = lean::box(0);
}
if (lean::is_scalar(x_1601)) {
 x_1602 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1602 = x_1601;
}
lean::cnstr_set(x_1602, 0, x_1599);
return x_1602;
}
else
{
obj* x_1603; obj* x_1606; obj* x_1608; obj* x_1610; obj* x_1611; uint8 x_1612; obj* x_1613; obj* x_1614; 
x_1603 = lean::cnstr_get(x_1592, 0);
lean::inc(x_1603);
lean::dec(x_1592);
x_1606 = lean::cnstr_get(x_1603, 0);
x_1608 = lean::cnstr_get(x_1603, 1);
if (lean::is_exclusive(x_1603)) {
 x_1610 = x_1603;
} else {
 lean::inc(x_1606);
 lean::inc(x_1608);
 lean::dec(x_1603);
 x_1610 = lean::box(0);
}
x_1611 = l_lean_elaborator_mangle__ident(x_1566);
x_1612 = lean::unbox(x_1563);
x_1613 = lean_expr_mk_pi(x_1611, x_1612, x_1584, x_1606);
if (lean::is_scalar(x_1610)) {
 x_1614 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1614 = x_1610;
}
lean::cnstr_set(x_1614, 0, x_1613);
lean::cnstr_set(x_1614, 1, x_1608);
x_14 = x_1614;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1616; obj* x_1617; obj* x_1621; obj* x_1622; 
lean::dec(x_9);
x_1616 = l_lean_parser_term_lambda_has__view;
x_1617 = lean::cnstr_get(x_1616, 0);
lean::inc(x_1617);
lean::dec(x_1616);
lean::inc(x_0);
x_1621 = lean::apply_1(x_1617, x_0);
x_1622 = lean::cnstr_get(x_1621, 1);
lean::inc(x_1622);
if (lean::obj_tag(x_1622) == 0)
{
obj* x_1626; obj* x_1627; 
lean::dec(x_1621);
lean::dec(x_1622);
x_1626 = l_lean_elaborator_to__pexpr___main___closed__46;
x_1627 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1626, x_1, x_2);
if (lean::obj_tag(x_1627) == 0)
{
obj* x_1630; obj* x_1632; obj* x_1633; 
lean::dec(x_7);
lean::dec(x_0);
x_1630 = lean::cnstr_get(x_1627, 0);
if (lean::is_exclusive(x_1627)) {
 x_1632 = x_1627;
} else {
 lean::inc(x_1630);
 lean::dec(x_1627);
 x_1632 = lean::box(0);
}
if (lean::is_scalar(x_1632)) {
 x_1633 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1633 = x_1632;
}
lean::cnstr_set(x_1633, 0, x_1630);
return x_1633;
}
else
{
obj* x_1634; 
x_1634 = lean::cnstr_get(x_1627, 0);
lean::inc(x_1634);
lean::dec(x_1627);
x_14 = x_1634;
goto lbl_15;
}
}
else
{
obj* x_1637; obj* x_1640; obj* x_1642; obj* x_1644; obj* x_1647; obj* x_1649; obj* x_1652; 
x_1637 = lean::cnstr_get(x_1622, 0);
lean::inc(x_1637);
lean::dec(x_1622);
x_1640 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1637);
lean::dec(x_1637);
x_1642 = lean::cnstr_get(x_1640, 1);
lean::inc(x_1642);
x_1644 = lean::cnstr_get(x_1640, 0);
lean::inc(x_1644);
lean::dec(x_1640);
x_1647 = lean::cnstr_get(x_1642, 0);
lean::inc(x_1647);
x_1649 = lean::cnstr_get(x_1642, 1);
lean::inc(x_1649);
lean::dec(x_1642);
x_1652 = l_lean_elaborator_to__pexpr___main(x_1649, x_1, x_2);
if (lean::obj_tag(x_1652) == 0)
{
obj* x_1658; obj* x_1660; obj* x_1661; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1644);
lean::dec(x_1647);
lean::dec(x_1621);
x_1658 = lean::cnstr_get(x_1652, 0);
if (lean::is_exclusive(x_1652)) {
 x_1660 = x_1652;
} else {
 lean::inc(x_1658);
 lean::dec(x_1652);
 x_1660 = lean::box(0);
}
if (lean::is_scalar(x_1660)) {
 x_1661 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1661 = x_1660;
}
lean::cnstr_set(x_1661, 0, x_1658);
return x_1661;
}
else
{
obj* x_1662; obj* x_1665; obj* x_1667; obj* x_1670; obj* x_1673; 
x_1662 = lean::cnstr_get(x_1652, 0);
lean::inc(x_1662);
lean::dec(x_1652);
x_1665 = lean::cnstr_get(x_1662, 0);
lean::inc(x_1665);
x_1667 = lean::cnstr_get(x_1662, 1);
lean::inc(x_1667);
lean::dec(x_1662);
x_1670 = lean::cnstr_get(x_1621, 3);
lean::inc(x_1670);
lean::dec(x_1621);
x_1673 = l_lean_elaborator_to__pexpr___main(x_1670, x_1, x_1667);
lean::dec(x_1667);
if (lean::obj_tag(x_1673) == 0)
{
obj* x_1680; obj* x_1682; obj* x_1683; 
lean::dec(x_1665);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1644);
lean::dec(x_1647);
x_1680 = lean::cnstr_get(x_1673, 0);
if (lean::is_exclusive(x_1673)) {
 x_1682 = x_1673;
} else {
 lean::inc(x_1680);
 lean::dec(x_1673);
 x_1682 = lean::box(0);
}
if (lean::is_scalar(x_1682)) {
 x_1683 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1683 = x_1682;
}
lean::cnstr_set(x_1683, 0, x_1680);
return x_1683;
}
else
{
obj* x_1684; obj* x_1687; obj* x_1689; obj* x_1691; obj* x_1692; uint8 x_1693; obj* x_1694; obj* x_1695; 
x_1684 = lean::cnstr_get(x_1673, 0);
lean::inc(x_1684);
lean::dec(x_1673);
x_1687 = lean::cnstr_get(x_1684, 0);
x_1689 = lean::cnstr_get(x_1684, 1);
if (lean::is_exclusive(x_1684)) {
 x_1691 = x_1684;
} else {
 lean::inc(x_1687);
 lean::inc(x_1689);
 lean::dec(x_1684);
 x_1691 = lean::box(0);
}
x_1692 = l_lean_elaborator_mangle__ident(x_1647);
x_1693 = lean::unbox(x_1644);
x_1694 = lean_expr_mk_lambda(x_1692, x_1693, x_1665, x_1687);
if (lean::is_scalar(x_1691)) {
 x_1695 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1695 = x_1691;
}
lean::cnstr_set(x_1695, 0, x_1694);
lean::cnstr_set(x_1695, 1, x_1689);
x_14 = x_1695;
goto lbl_15;
}
}
}
}
}
else
{
obj* x_1697; obj* x_1698; obj* x_1702; obj* x_1703; obj* x_1705; 
lean::dec(x_9);
x_1697 = l_lean_parser_term_app_has__view;
x_1698 = lean::cnstr_get(x_1697, 0);
lean::inc(x_1698);
lean::dec(x_1697);
lean::inc(x_0);
x_1702 = lean::apply_1(x_1698, x_0);
x_1703 = lean::cnstr_get(x_1702, 0);
lean::inc(x_1703);
x_1705 = l_lean_elaborator_to__pexpr___main(x_1703, x_1, x_2);
if (lean::obj_tag(x_1705) == 0)
{
obj* x_1709; obj* x_1711; obj* x_1712; 
lean::dec(x_1702);
lean::dec(x_7);
lean::dec(x_0);
x_1709 = lean::cnstr_get(x_1705, 0);
if (lean::is_exclusive(x_1705)) {
 x_1711 = x_1705;
} else {
 lean::inc(x_1709);
 lean::dec(x_1705);
 x_1711 = lean::box(0);
}
if (lean::is_scalar(x_1711)) {
 x_1712 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1712 = x_1711;
}
lean::cnstr_set(x_1712, 0, x_1709);
return x_1712;
}
else
{
obj* x_1713; obj* x_1716; obj* x_1718; obj* x_1721; obj* x_1724; 
x_1713 = lean::cnstr_get(x_1705, 0);
lean::inc(x_1713);
lean::dec(x_1705);
x_1716 = lean::cnstr_get(x_1713, 0);
lean::inc(x_1716);
x_1718 = lean::cnstr_get(x_1713, 1);
lean::inc(x_1718);
lean::dec(x_1713);
x_1721 = lean::cnstr_get(x_1702, 1);
lean::inc(x_1721);
lean::dec(x_1702);
x_1724 = l_lean_elaborator_to__pexpr___main(x_1721, x_1, x_1718);
lean::dec(x_1718);
if (lean::obj_tag(x_1724) == 0)
{
obj* x_1729; obj* x_1731; obj* x_1732; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1716);
x_1729 = lean::cnstr_get(x_1724, 0);
if (lean::is_exclusive(x_1724)) {
 x_1731 = x_1724;
} else {
 lean::inc(x_1729);
 lean::dec(x_1724);
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
obj* x_1733; obj* x_1736; obj* x_1738; obj* x_1740; obj* x_1741; obj* x_1742; 
x_1733 = lean::cnstr_get(x_1724, 0);
lean::inc(x_1733);
lean::dec(x_1724);
x_1736 = lean::cnstr_get(x_1733, 0);
x_1738 = lean::cnstr_get(x_1733, 1);
if (lean::is_exclusive(x_1733)) {
 x_1740 = x_1733;
} else {
 lean::inc(x_1736);
 lean::inc(x_1738);
 lean::dec(x_1733);
 x_1740 = lean::box(0);
}
x_1741 = lean_expr_mk_app(x_1716, x_1736);
if (lean::is_scalar(x_1740)) {
 x_1742 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1742 = x_1740;
}
lean::cnstr_set(x_1742, 0, x_1741);
lean::cnstr_set(x_1742, 1, x_1738);
x_14 = x_1742;
goto lbl_15;
}
}
}
}
else
{
obj* x_1744; obj* x_1745; obj* x_1749; obj* x_1750; 
lean::dec(x_9);
x_1744 = l_lean_parser_ident__univs_has__view;
x_1745 = lean::cnstr_get(x_1744, 0);
lean::inc(x_1745);
lean::dec(x_1744);
lean::inc(x_0);
x_1749 = lean::apply_1(x_1745, x_0);
x_1750 = lean::cnstr_get(x_1749, 1);
lean::inc(x_1750);
if (lean::obj_tag(x_1750) == 0)
{
obj* x_1752; obj* x_1756; obj* x_1757; obj* x_1758; obj* x_1759; obj* x_1762; obj* x_1763; obj* x_1764; obj* x_1765; obj* x_1766; obj* x_1767; uint8 x_1768; 
x_1752 = lean::cnstr_get(x_1749, 0);
lean::inc(x_1752);
lean::dec(x_1749);
lean::inc(x_1752);
x_1756 = l_lean_elaborator_mangle__ident(x_1752);
x_1757 = lean::box(0);
x_1758 = lean_expr_mk_const(x_1756, x_1757);
x_1759 = lean::cnstr_get(x_1752, 3);
lean::inc(x_1759);
lean::dec(x_1752);
x_1762 = lean::mk_nat_obj(0u);
x_1763 = l_list_enum__from___main___rarg(x_1762, x_1759);
x_1764 = l_lean_elaborator_to__pexpr___main___closed__47;
x_1765 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(x_1764, x_1763);
x_1766 = lean_expr_mk_mdata(x_1765, x_1758);
x_1767 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1768 = lean_name_dec_eq(x_7, x_1767);
lean::dec(x_7);
if (x_1768 == 0)
{
obj* x_1770; 
x_1770 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1770) == 0)
{
obj* x_1773; obj* x_1774; 
lean::inc(x_2);
x_1773 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1773, 0, x_1766);
lean::cnstr_set(x_1773, 1, x_2);
x_1774 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1774, 0, x_1773);
return x_1774;
}
else
{
obj* x_1775; obj* x_1778; obj* x_1779; obj* x_1780; obj* x_1782; obj* x_1784; obj* x_1785; obj* x_1787; obj* x_1790; obj* x_1791; obj* x_1793; obj* x_1795; obj* x_1796; 
x_1775 = lean::cnstr_get(x_1770, 0);
lean::inc(x_1775);
lean::dec(x_1770);
x_1778 = lean::cnstr_get(x_1, 0);
x_1779 = lean::cnstr_get(x_1778, 2);
x_1780 = l_lean_file__map_to__position(x_1779, x_1775);
lean::dec(x_1775);
x_1782 = lean::cnstr_get(x_1780, 1);
lean::inc(x_1782);
x_1784 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1785 = l_lean_kvmap_set__nat(x_1757, x_1784, x_1782);
lean::dec(x_1782);
x_1787 = lean::cnstr_get(x_1780, 0);
lean::inc(x_1787);
lean::dec(x_1780);
x_1790 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1791 = l_lean_kvmap_set__nat(x_1785, x_1790, x_1787);
lean::dec(x_1787);
x_1793 = lean_expr_mk_mdata(x_1791, x_1766);
lean::inc(x_2);
x_1795 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1795, 0, x_1793);
lean::cnstr_set(x_1795, 1, x_2);
x_1796 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1796, 0, x_1795);
return x_1796;
}
}
else
{
obj* x_1799; obj* x_1800; 
lean::dec(x_0);
lean::inc(x_2);
x_1799 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1799, 0, x_1766);
lean::cnstr_set(x_1799, 1, x_2);
x_1800 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1800, 0, x_1799);
return x_1800;
}
}
else
{
obj* x_1801; obj* x_1804; obj* x_1807; obj* x_1810; 
x_1801 = lean::cnstr_get(x_1749, 0);
lean::inc(x_1801);
lean::dec(x_1749);
x_1804 = lean::cnstr_get(x_1750, 0);
lean::inc(x_1804);
lean::dec(x_1750);
x_1807 = lean::cnstr_get(x_1804, 1);
lean::inc(x_1807);
lean::dec(x_1804);
x_1810 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_1807, x_1, x_2);
if (lean::obj_tag(x_1810) == 0)
{
obj* x_1814; obj* x_1816; obj* x_1817; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1801);
x_1814 = lean::cnstr_get(x_1810, 0);
if (lean::is_exclusive(x_1810)) {
 x_1816 = x_1810;
} else {
 lean::inc(x_1814);
 lean::dec(x_1810);
 x_1816 = lean::box(0);
}
if (lean::is_scalar(x_1816)) {
 x_1817 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1817 = x_1816;
}
lean::cnstr_set(x_1817, 0, x_1814);
return x_1817;
}
else
{
obj* x_1818; obj* x_1821; obj* x_1823; obj* x_1825; obj* x_1827; obj* x_1828; obj* x_1829; obj* x_1832; obj* x_1833; obj* x_1834; obj* x_1835; obj* x_1836; obj* x_1837; 
x_1818 = lean::cnstr_get(x_1810, 0);
lean::inc(x_1818);
lean::dec(x_1810);
x_1821 = lean::cnstr_get(x_1818, 0);
x_1823 = lean::cnstr_get(x_1818, 1);
if (lean::is_exclusive(x_1818)) {
 x_1825 = x_1818;
} else {
 lean::inc(x_1821);
 lean::inc(x_1823);
 lean::dec(x_1818);
 x_1825 = lean::box(0);
}
lean::inc(x_1801);
x_1827 = l_lean_elaborator_mangle__ident(x_1801);
x_1828 = lean_expr_mk_const(x_1827, x_1821);
x_1829 = lean::cnstr_get(x_1801, 3);
lean::inc(x_1829);
lean::dec(x_1801);
x_1832 = lean::mk_nat_obj(0u);
x_1833 = l_list_enum__from___main___rarg(x_1832, x_1829);
x_1834 = l_lean_elaborator_to__pexpr___main___closed__47;
x_1835 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(x_1834, x_1833);
x_1836 = lean_expr_mk_mdata(x_1835, x_1828);
if (lean::is_scalar(x_1825)) {
 x_1837 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1837 = x_1825;
}
lean::cnstr_set(x_1837, 0, x_1836);
lean::cnstr_set(x_1837, 1, x_1823);
x_14 = x_1837;
goto lbl_15;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_1840; obj* x_1842; obj* x_1843; 
lean::dec(x_7);
lean::dec(x_0);
x_1840 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_1842 = x_12;
} else {
 lean::inc(x_1840);
 lean::dec(x_12);
 x_1842 = lean::box(0);
}
if (lean::is_scalar(x_1842)) {
 x_1843 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1843 = x_1842;
}
lean::cnstr_set(x_1843, 0, x_1840);
return x_1843;
}
else
{
obj* x_1844; obj* x_1846; obj* x_1847; obj* x_1849; obj* x_1851; obj* x_1852; uint8 x_1853; 
x_1844 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 x_1846 = x_12;
} else {
 lean::inc(x_1844);
 lean::dec(x_12);
 x_1846 = lean::box(0);
}
x_1847 = lean::cnstr_get(x_1844, 0);
x_1849 = lean::cnstr_get(x_1844, 1);
if (lean::is_exclusive(x_1844)) {
 lean::cnstr_set(x_1844, 0, lean::box(0));
 lean::cnstr_set(x_1844, 1, lean::box(0));
 x_1851 = x_1844;
} else {
 lean::inc(x_1847);
 lean::inc(x_1849);
 lean::dec(x_1844);
 x_1851 = lean::box(0);
}
x_1852 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1853 = lean_name_dec_eq(x_7, x_1852);
lean::dec(x_7);
if (x_1853 == 0)
{
obj* x_1855; 
x_1855 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1855) == 0)
{
obj* x_1857; obj* x_1858; 
if (lean::is_scalar(x_1851)) {
 x_1857 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1857 = x_1851;
}
lean::cnstr_set(x_1857, 0, x_1847);
lean::cnstr_set(x_1857, 1, x_1849);
if (lean::is_scalar(x_1846)) {
 x_1858 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1858 = x_1846;
}
lean::cnstr_set(x_1858, 0, x_1857);
return x_1858;
}
else
{
obj* x_1859; obj* x_1862; obj* x_1863; obj* x_1864; obj* x_1866; obj* x_1867; obj* x_1869; obj* x_1870; obj* x_1872; obj* x_1875; obj* x_1876; obj* x_1878; obj* x_1879; obj* x_1880; 
x_1859 = lean::cnstr_get(x_1855, 0);
lean::inc(x_1859);
lean::dec(x_1855);
x_1862 = lean::cnstr_get(x_1, 0);
x_1863 = lean::cnstr_get(x_1862, 2);
x_1864 = l_lean_file__map_to__position(x_1863, x_1859);
lean::dec(x_1859);
x_1866 = lean::box(0);
x_1867 = lean::cnstr_get(x_1864, 1);
lean::inc(x_1867);
x_1869 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1870 = l_lean_kvmap_set__nat(x_1866, x_1869, x_1867);
lean::dec(x_1867);
x_1872 = lean::cnstr_get(x_1864, 0);
lean::inc(x_1872);
lean::dec(x_1864);
x_1875 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1876 = l_lean_kvmap_set__nat(x_1870, x_1875, x_1872);
lean::dec(x_1872);
x_1878 = lean_expr_mk_mdata(x_1876, x_1847);
if (lean::is_scalar(x_1851)) {
 x_1879 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1879 = x_1851;
}
lean::cnstr_set(x_1879, 0, x_1878);
lean::cnstr_set(x_1879, 1, x_1849);
if (lean::is_scalar(x_1846)) {
 x_1880 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1880 = x_1846;
}
lean::cnstr_set(x_1880, 0, x_1879);
return x_1880;
}
}
else
{
obj* x_1882; obj* x_1883; 
lean::dec(x_0);
if (lean::is_scalar(x_1851)) {
 x_1882 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1882 = x_1851;
}
lean::cnstr_set(x_1882, 0, x_1847);
lean::cnstr_set(x_1882, 1, x_1849);
if (lean::is_scalar(x_1846)) {
 x_1883 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1883 = x_1846;
}
lean::cnstr_set(x_1883, 0, x_1882);
return x_1883;
}
}
}
lbl_15:
{
obj* x_1884; obj* x_1886; obj* x_1888; obj* x_1889; uint8 x_1890; 
x_1884 = lean::cnstr_get(x_14, 0);
x_1886 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_set(x_14, 1, lean::box(0));
 x_1888 = x_14;
} else {
 lean::inc(x_1884);
 lean::inc(x_1886);
 lean::dec(x_14);
 x_1888 = lean::box(0);
}
x_1889 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1890 = lean_name_dec_eq(x_7, x_1889);
lean::dec(x_7);
if (x_1890 == 0)
{
obj* x_1892; 
x_1892 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1892) == 0)
{
obj* x_1894; obj* x_1895; 
if (lean::is_scalar(x_1888)) {
 x_1894 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1894 = x_1888;
}
lean::cnstr_set(x_1894, 0, x_1884);
lean::cnstr_set(x_1894, 1, x_1886);
x_1895 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1895, 0, x_1894);
return x_1895;
}
else
{
obj* x_1896; obj* x_1899; obj* x_1900; obj* x_1901; obj* x_1903; obj* x_1904; obj* x_1906; obj* x_1907; obj* x_1909; obj* x_1912; obj* x_1913; obj* x_1915; obj* x_1916; obj* x_1917; 
x_1896 = lean::cnstr_get(x_1892, 0);
lean::inc(x_1896);
lean::dec(x_1892);
x_1899 = lean::cnstr_get(x_1, 0);
x_1900 = lean::cnstr_get(x_1899, 2);
x_1901 = l_lean_file__map_to__position(x_1900, x_1896);
lean::dec(x_1896);
x_1903 = lean::box(0);
x_1904 = lean::cnstr_get(x_1901, 1);
lean::inc(x_1904);
x_1906 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1907 = l_lean_kvmap_set__nat(x_1903, x_1906, x_1904);
lean::dec(x_1904);
x_1909 = lean::cnstr_get(x_1901, 0);
lean::inc(x_1909);
lean::dec(x_1901);
x_1912 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1913 = l_lean_kvmap_set__nat(x_1907, x_1912, x_1909);
lean::dec(x_1909);
x_1915 = lean_expr_mk_mdata(x_1913, x_1884);
if (lean::is_scalar(x_1888)) {
 x_1916 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1916 = x_1888;
}
lean::cnstr_set(x_1916, 0, x_1915);
lean::cnstr_set(x_1916, 1, x_1886);
x_1917 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1917, 0, x_1916);
return x_1917;
}
}
else
{
obj* x_1919; obj* x_1920; 
lean::dec(x_0);
if (lean::is_scalar(x_1888)) {
 x_1919 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1919 = x_1888;
}
lean::cnstr_set(x_1919, 0, x_1884);
lean::cnstr_set(x_1919, 1, x_1886);
x_1920 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1920, 0, x_1919);
return x_1920;
}
}
lbl_17:
{
obj* x_1921; 
x_1921 = lean::cnstr_get(x_16, 0);
lean::inc(x_1921);
if (lean::obj_tag(x_1921) == 0)
{
obj* x_1924; obj* x_1927; obj* x_1928; 
lean::dec(x_9);
x_1924 = lean::cnstr_get(x_16, 1);
lean::inc(x_1924);
lean::dec(x_16);
x_1927 = l_lean_elaborator_to__pexpr___main___closed__5;
x_1928 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1927, x_1, x_1924);
lean::dec(x_1924);
if (lean::obj_tag(x_1928) == 0)
{
obj* x_1932; obj* x_1934; obj* x_1935; 
lean::dec(x_7);
lean::dec(x_0);
x_1932 = lean::cnstr_get(x_1928, 0);
if (lean::is_exclusive(x_1928)) {
 x_1934 = x_1928;
} else {
 lean::inc(x_1932);
 lean::dec(x_1928);
 x_1934 = lean::box(0);
}
if (lean::is_scalar(x_1934)) {
 x_1935 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1935 = x_1934;
}
lean::cnstr_set(x_1935, 0, x_1932);
return x_1935;
}
else
{
obj* x_1936; 
x_1936 = lean::cnstr_get(x_1928, 0);
lean::inc(x_1936);
lean::dec(x_1928);
x_14 = x_1936;
goto lbl_15;
}
}
else
{
obj* x_1939; obj* x_1941; obj* x_1942; obj* x_1944; obj* x_1947; obj* x_1948; obj* x_1949; obj* x_1951; obj* x_1952; obj* x_1954; obj* x_1955; obj* x_1957; obj* x_1958; 
x_1939 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_1941 = x_16;
} else {
 lean::inc(x_1939);
 lean::dec(x_16);
 x_1941 = lean::box(0);
}
x_1942 = lean::cnstr_get(x_1921, 0);
lean::inc(x_1942);
x_1944 = lean::cnstr_get(x_1921, 1);
lean::inc(x_1944);
lean::dec(x_1921);
x_1947 = lean::box(0);
x_1948 = lean::mk_nat_obj(0u);
x_1949 = l_list_length__aux___main___rarg(x_9, x_1948);
lean::dec(x_9);
x_1951 = l_lean_elaborator_to__pexpr___main___closed__6;
x_1952 = l_lean_kvmap_set__nat(x_1947, x_1951, x_1949);
lean::dec(x_1949);
x_1954 = l_list_reverse___rarg(x_1944);
x_1955 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_1942, x_1954);
lean::dec(x_1942);
x_1957 = lean_expr_mk_mdata(x_1952, x_1955);
if (lean::is_scalar(x_1941)) {
 x_1958 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1958 = x_1941;
}
lean::cnstr_set(x_1958, 0, x_1957);
lean::cnstr_set(x_1958, 1, x_1939);
x_14 = x_1958;
goto lbl_15;
}
}
}
default:
{
obj* x_1959; 
x_1959 = lean::box(0);
x_3 = x_1959;
goto lbl_4;
}
}
lbl_4:
{
obj* x_1962; obj* x_1963; obj* x_1964; obj* x_1966; obj* x_1967; obj* x_1969; 
lean::dec(x_3);
lean::inc(x_0);
x_1962 = l_lean_parser_syntax_to__format___main(x_0);
x_1963 = lean::mk_nat_obj(80u);
x_1964 = l_lean_format_pretty(x_1962, x_1963);
lean::dec(x_1962);
x_1966 = l_lean_elaborator_to__pexpr___main___closed__1;
x_1967 = lean::string_append(x_1966, x_1964);
lean::dec(x_1964);
x_1969 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1967, x_1, x_2);
lean::dec(x_1967);
lean::dec(x_0);
return x_1969;
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
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* l_lean_elaborator_to__pexpr___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_to__pexpr___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* l_lean_elaborator_to__pexpr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_to__pexpr(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_get__namespace___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::cnstr_get(x_0, 4);
x_2 = lean::cnstr_get(x_1, 4);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_0);
lean::inc(x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_lean_elaborator_get__namespace(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_get__namespace___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_elaborator_get__namespace___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_get__namespace___rarg(x_0);
lean::dec(x_0);
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
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
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
lean::inc(x_2);
lean::inc(x_11);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_2);
x_17 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(x_9, x_1, x_16);
lean::dec(x_16);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_11, x_19);
lean::dec(x_11);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_8);
lean::cnstr_set(x_22, 1, x_17);
lean::cnstr_set(x_22, 2, x_20);
return x_22;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(x_0, x_4, x_5);
x_0 = x_6;
x_1 = x_3;
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
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
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
lean::inc(x_2);
lean::inc(x_11);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_2);
x_17 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(x_9, x_1, x_16);
lean::dec(x_16);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_11, x_19);
lean::dec(x_11);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_8);
lean::cnstr_set(x_22, 1, x_17);
lean::cnstr_set(x_22, 2, x_20);
return x_22;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__9(x_0, x_4, x_5);
x_0 = x_6;
x_1 = x_3;
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
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(x_3);
x_5 = lean::box(0);
x_6 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(x_4, x_2, x_5);
return x_6;
}
}
}
obj* l_lean_elaborator_old__elab__command(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = l_lean_elaborator_get__namespace___rarg(x_3);
switch (lean::obj_tag(x_1)) {
case 10:
{
obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_35; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_4, 2);
lean::inc(x_15);
x_17 = l_lean_parser_syntax_get__pos(x_0);
x_18 = lean::mk_nat_obj(0u);
x_19 = l_option_get__or__else___main___rarg(x_17, x_18);
lean::dec(x_17);
x_21 = l_lean_file__map_to__position(x_15, x_19);
lean::dec(x_19);
lean::dec(x_15);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
x_26 = l_lean_elaborator_to__pexpr___main___closed__3;
x_27 = l_lean_kvmap_set__nat(x_10, x_26, x_24);
lean::dec(x_24);
x_29 = lean::cnstr_get(x_21, 0);
lean::inc(x_29);
lean::dec(x_21);
x_32 = l_lean_elaborator_to__pexpr___main___closed__4;
x_33 = l_lean_kvmap_set__nat(x_27, x_32, x_29);
lean::dec(x_29);
x_35 = lean_expr_mk_mdata(x_33, x_12);
x_8 = x_35;
goto lbl_9;
}
default:
{
x_8 = x_1;
goto lbl_9;
}
}
lbl_9:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_8);
x_39 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_41 = x_7;
} else {
 lean::inc(x_39);
 lean::dec(x_7);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_51; obj* x_54; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_65; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_74; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; 
x_43 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_45 = x_7;
} else {
 lean::inc(x_43);
 lean::dec(x_7);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_43, 1);
lean::inc(x_48);
lean::dec(x_43);
x_51 = lean::cnstr_get(x_4, 0);
lean::inc(x_51);
lean::dec(x_4);
x_54 = lean::cnstr_get(x_3, 8);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_3, 9);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_3, 4);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_58, 1);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_60, 0);
lean::inc(x_62);
lean::dec(x_60);
x_65 = l_list_reverse___rarg(x_62);
x_66 = lean::cnstr_get(x_58, 2);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_66, 0);
lean::inc(x_68);
lean::dec(x_66);
x_71 = l_list_reverse___rarg(x_68);
x_72 = lean::cnstr_get(x_58, 3);
lean::inc(x_72);
x_74 = l_rbtree_to__list___rarg(x_72);
lean::dec(x_72);
x_76 = lean::cnstr_get(x_58, 6);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_3, 10);
lean::inc(x_78);
x_80 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_80, 0, x_54);
lean::cnstr_set(x_80, 1, x_56);
lean::cnstr_set(x_80, 2, x_65);
lean::cnstr_set(x_80, 3, x_71);
lean::cnstr_set(x_80, 4, x_74);
lean::cnstr_set(x_80, 5, x_76);
lean::cnstr_set(x_80, 6, x_78);
lean::cnstr_set(x_80, 7, x_46);
x_81 = lean_elaborator_elaborate_command(x_51, x_8, x_80);
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
if (lean::obj_tag(x_82) == 0)
{
obj* x_86; obj* x_88; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_3);
lean::dec(x_58);
x_86 = lean::cnstr_get(x_81, 1);
if (lean::is_exclusive(x_81)) {
 lean::cnstr_release(x_81, 0);
 x_88 = x_81;
} else {
 lean::inc(x_86);
 lean::dec(x_81);
 x_88 = lean::box(0);
}
x_89 = lean::cnstr_get(x_48, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_48, 1);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_48, 2);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_48, 3);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_48, 4);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_48, 5);
lean::inc(x_99);
x_101 = l_list_append___rarg(x_86, x_99);
x_102 = lean::cnstr_get(x_48, 6);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_48, 7);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_48, 8);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_48, 9);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_48, 10);
lean::inc(x_110);
lean::dec(x_48);
x_113 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_113, 0, x_89);
lean::cnstr_set(x_113, 1, x_91);
lean::cnstr_set(x_113, 2, x_93);
lean::cnstr_set(x_113, 3, x_95);
lean::cnstr_set(x_113, 4, x_97);
lean::cnstr_set(x_113, 5, x_101);
lean::cnstr_set(x_113, 6, x_102);
lean::cnstr_set(x_113, 7, x_104);
lean::cnstr_set(x_113, 8, x_106);
lean::cnstr_set(x_113, 9, x_108);
lean::cnstr_set(x_113, 10, x_110);
x_114 = lean::box(0);
if (lean::is_scalar(x_88)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_88;
}
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_113);
if (lean::is_scalar(x_45)) {
 x_116 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_116 = x_45;
}
lean::cnstr_set(x_116, 0, x_115);
return x_116;
}
else
{
obj* x_118; obj* x_120; obj* x_121; obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_134; obj* x_136; obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_153; obj* x_155; obj* x_156; obj* x_158; obj* x_160; obj* x_163; obj* x_165; obj* x_167; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
lean::dec(x_48);
x_118 = lean::cnstr_get(x_81, 1);
if (lean::is_exclusive(x_81)) {
 lean::cnstr_release(x_81, 0);
 x_120 = x_81;
} else {
 lean::inc(x_118);
 lean::dec(x_81);
 x_120 = lean::box(0);
}
x_121 = lean::cnstr_get(x_82, 0);
lean::inc(x_121);
lean::dec(x_82);
x_124 = lean::cnstr_get(x_3, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_3, 1);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_3, 2);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_3, 3);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_58, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_121, 2);
lean::inc(x_134);
x_136 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
x_137 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(x_136, x_134);
lean::dec(x_134);
x_139 = lean::cnstr_get(x_121, 3);
lean::inc(x_139);
x_141 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1;
x_142 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(x_141, x_139);
lean::dec(x_139);
x_144 = lean::cnstr_get(x_121, 4);
lean::inc(x_144);
x_146 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(x_144);
lean::dec(x_144);
x_148 = lean::cnstr_get(x_58, 4);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_58, 5);
lean::inc(x_150);
lean::dec(x_58);
x_153 = lean::cnstr_get(x_121, 5);
lean::inc(x_153);
x_155 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_155, 0, x_132);
lean::cnstr_set(x_155, 1, x_137);
lean::cnstr_set(x_155, 2, x_142);
lean::cnstr_set(x_155, 3, x_146);
lean::cnstr_set(x_155, 4, x_148);
lean::cnstr_set(x_155, 5, x_150);
lean::cnstr_set(x_155, 6, x_153);
x_156 = lean::cnstr_get(x_3, 5);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_3, 6);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_3, 7);
lean::inc(x_160);
lean::dec(x_3);
x_163 = lean::cnstr_get(x_121, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_121, 1);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_121, 6);
lean::inc(x_167);
lean::dec(x_121);
x_170 = l_list_append___rarg(x_118, x_156);
x_171 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_171, 0, x_124);
lean::cnstr_set(x_171, 1, x_126);
lean::cnstr_set(x_171, 2, x_128);
lean::cnstr_set(x_171, 3, x_130);
lean::cnstr_set(x_171, 4, x_155);
lean::cnstr_set(x_171, 5, x_170);
lean::cnstr_set(x_171, 6, x_158);
lean::cnstr_set(x_171, 7, x_160);
lean::cnstr_set(x_171, 8, x_163);
lean::cnstr_set(x_171, 9, x_165);
lean::cnstr_set(x_171, 10, x_167);
x_172 = lean::box(0);
if (lean::is_scalar(x_120)) {
 x_173 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_173 = x_120;
}
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_171);
if (lean::is_scalar(x_45)) {
 x_174 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_174 = x_45;
}
lean::cnstr_set(x_174, 0, x_173);
return x_174;
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__10(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__9(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__16___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__16(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
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
x_12 = l_lean_elaborator_to__pexpr___main(x_7, x_1, x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_9);
lean::dec(x_11);
x_15 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_17 = x_12;
} else {
 lean::inc(x_15);
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
obj* x_19; obj* x_22; obj* x_24; obj* x_27; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_9, x_1, x_24);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_11);
lean::dec(x_22);
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
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_35 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_37 = x_27;
} else {
 lean::inc(x_35);
 lean::dec(x_27);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_35, 0);
x_40 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_42 = x_35;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_35);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_11;
}
lean::cnstr_set(x_43, 0, x_22);
lean::cnstr_set(x_43, 1, x_38);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_40);
if (lean::is_scalar(x_37)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_37;
}
lean::cnstr_set(x_45, 0, x_44);
return x_45;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_17; 
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
x_17 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_15, x_1, x_2);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_12);
lean::dec(x_9);
lean::dec(x_11);
x_21 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 x_23 = x_17;
} else {
 lean::inc(x_21);
 lean::dec(x_17);
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
obj* x_25; obj* x_28; obj* x_30; obj* x_33; 
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
lean::dec(x_17);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(x_9, x_1, x_30);
lean::dec(x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_12);
lean::dec(x_11);
lean::dec(x_28);
x_38 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_40 = x_33;
} else {
 lean::inc(x_38);
 lean::dec(x_33);
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
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_42 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_44 = x_33;
} else {
 lean::inc(x_42);
 lean::dec(x_33);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_42, 0);
x_47 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 x_49 = x_42;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_42);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_12, 0);
lean::inc(x_50);
lean::dec(x_12);
x_53 = lean::cnstr_get(x_50, 2);
lean::inc(x_53);
lean::dec(x_50);
x_56 = l_lean_expr_mk__capp(x_53, x_28);
if (lean::is_scalar(x_11)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_11;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_45);
if (lean::is_scalar(x_49)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_49;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_47);
if (lean::is_scalar(x_44)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_44;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
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
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_attrs__to__pexpr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_attrs__to__pexpr(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
lean::dec(x_3);
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
lean::dec(x_3);
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
lean::dec(x_44);
if (lean::obj_tag(x_6) == 0)
{
x_19 = x_48;
goto lbl_20;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_6, 0);
lean::inc(x_50);
lean::dec(x_6);
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; uint8 x_55; obj* x_56; 
lean::dec(x_50);
x_54 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
x_55 = 1;
x_56 = l_lean_kvmap_set__bool(x_48, x_54, x_55);
x_19 = x_56;
goto lbl_20;
}
else
{
obj* x_58; uint8 x_59; obj* x_60; 
lean::dec(x_50);
x_58 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
x_59 = 1;
x_60 = l_lean_kvmap_set__bool(x_48, x_58, x_59);
x_19 = x_60;
goto lbl_20;
}
}
}
}
lbl_20:
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_61 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
x_62 = l_lean_kvmap_set__bool(x_19, x_61, x_10);
x_63 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
x_64 = l_lean_kvmap_set__bool(x_62, x_63, x_14);
if (lean::obj_tag(x_16) == 0)
{
obj* x_65; 
x_65 = l_lean_elaborator_attrs__to__pexpr(x_3, x_1, x_2);
if (lean::obj_tag(x_65) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_64);
x_67 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_69 = x_65;
} else {
 lean::inc(x_67);
 lean::dec(x_65);
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
obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_71 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_73 = x_65;
} else {
 lean::inc(x_71);
 lean::dec(x_65);
 x_73 = lean::box(0);
}
x_74 = lean::cnstr_get(x_71, 0);
x_76 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 x_78 = x_71;
} else {
 lean::inc(x_74);
 lean::inc(x_76);
 lean::dec(x_71);
 x_78 = lean::box(0);
}
x_79 = lean_expr_mk_mdata(x_64, x_74);
if (lean::is_scalar(x_78)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_78;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_76);
if (lean::is_scalar(x_73)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_73;
}
lean::cnstr_set(x_81, 0, x_80);
return x_81;
}
}
else
{
obj* x_82; obj* x_85; obj* x_88; 
x_82 = lean::cnstr_get(x_16, 0);
lean::inc(x_82);
lean::dec(x_16);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
x_88 = l_lean_elaborator_attrs__to__pexpr(x_85, x_1, x_2);
if (lean::obj_tag(x_88) == 0)
{
obj* x_90; obj* x_92; obj* x_93; 
lean::dec(x_64);
x_90 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
 x_92 = x_88;
} else {
 lean::inc(x_90);
 lean::dec(x_88);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
return x_93;
}
else
{
obj* x_94; obj* x_96; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_94 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
 x_96 = x_88;
} else {
 lean::inc(x_94);
 lean::dec(x_88);
 x_96 = lean::box(0);
}
x_97 = lean::cnstr_get(x_94, 0);
x_99 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 x_101 = x_94;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_94);
 x_101 = lean::box(0);
}
x_102 = lean_expr_mk_mdata(x_64, x_97);
if (lean::is_scalar(x_101)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_101;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_99);
if (lean::is_scalar(x_96)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_96;
}
lean::cnstr_set(x_104, 0, x_103);
return x_104;
}
}
}
}
}
obj* l_lean_elaborator_decl__modifiers__to__pexpr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_decl__modifiers__to__pexpr(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_23; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::cnstr_get(x_1, 3);
x_6 = lean::cnstr_get(x_1, 5);
x_7 = lean::cnstr_get(x_1, 6);
x_8 = lean::cnstr_get(x_1, 7);
x_9 = lean::cnstr_get(x_1, 8);
x_10 = lean::cnstr_get(x_1, 9);
x_11 = lean::cnstr_get(x_1, 10);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_0);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_23 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_23, 0, x_2);
lean::cnstr_set(x_23, 1, x_3);
lean::cnstr_set(x_23, 2, x_4);
lean::cnstr_set(x_23, 3, x_5);
lean::cnstr_set(x_23, 4, x_0);
lean::cnstr_set(x_23, 5, x_6);
lean::cnstr_set(x_23, 6, x_7);
lean::cnstr_set(x_23, 7, x_8);
lean::cnstr_set(x_23, 8, x_9);
lean::cnstr_set(x_23, 9, x_10);
lean::cnstr_set(x_23, 10, x_11);
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
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg___lambda__2___boxed), 2, 1);
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
obj* l_lean_elaborator_locally___rarg___lambda__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_locally___rarg___lambda__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_21; obj* x_24; 
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
lean::dec(x_7);
x_14 = lean::cnstr_get(x_12, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
lean::dec(x_12);
x_19 = lean::cnstr_get(x_14, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 1);
lean::inc(x_21);
lean::dec(x_14);
x_24 = l_lean_elaborator_to__pexpr___main(x_21, x_1, x_2);
if (lean::obj_tag(x_24) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_16);
lean::dec(x_19);
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
obj* x_33; obj* x_36; obj* x_38; obj* x_41; 
x_33 = lean::cnstr_get(x_24, 0);
lean::inc(x_33);
lean::dec(x_24);
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
lean::dec(x_33);
x_41 = l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(x_9, x_1, x_38);
lean::dec(x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_11);
lean::dec(x_36);
lean::dec(x_16);
lean::dec(x_19);
x_47 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_49 = x_41;
} else {
 lean::inc(x_47);
 lean::dec(x_41);
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
x_51 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_53 = x_41;
} else {
 lean::inc(x_51);
 lean::dec(x_41);
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
x_59 = l_lean_elaborator_mangle__ident(x_19);
x_60 = lean::unbox(x_16);
lean::inc(x_59);
x_62 = lean_expr_local(x_59, x_59, x_36, x_60);
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
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_simple__binders__to__pexpr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_simple__binders__to__pexpr(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
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
x_12 = l_lean_elaborator_to__pexpr___main(x_7, x_1, x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_9);
lean::dec(x_11);
x_15 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_17 = x_12;
} else {
 lean::inc(x_15);
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
obj* x_19; obj* x_22; obj* x_24; obj* x_27; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_9, x_1, x_24);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_11);
lean::dec(x_22);
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
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_35 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_37 = x_27;
} else {
 lean::inc(x_35);
 lean::dec(x_27);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_35, 0);
x_40 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_42 = x_35;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_35);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_11;
}
lean::cnstr_set(x_43, 0, x_22);
lean::cnstr_set(x_43, 1, x_38);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_40);
if (lean::is_scalar(x_37)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_37;
}
lean::cnstr_set(x_45, 0, x_44);
return x_45;
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
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_5 = lean::box(0);
lean::inc(x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; 
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
x_16 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_14, x_2, x_3);
if (lean::obj_tag(x_16) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_9);
lean::dec(x_11);
x_21 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
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
obj* x_25; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_36; 
x_25 = lean::cnstr_get(x_16, 0);
lean::inc(x_25);
lean::dec(x_16);
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
x_33 = lean::cnstr_get(x_9, 3);
lean::inc(x_33);
lean::dec(x_9);
x_36 = l_lean_elaborator_to__pexpr___main(x_33, x_2, x_30);
lean::dec(x_30);
if (lean::obj_tag(x_36) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_32);
lean::dec(x_28);
x_43 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_45 = x_36;
} else {
 lean::inc(x_43);
 lean::dec(x_36);
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
obj* x_47; obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; 
x_47 = lean::cnstr_get(x_36, 0);
lean::inc(x_47);
lean::dec(x_36);
x_50 = lean::cnstr_get(x_0, 0);
lean::inc(x_50);
x_52 = l_lean_elaborator_mangle__ident(x_50);
x_53 = lean::cnstr_get(x_47, 0);
x_55 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_set(x_47, 0, lean::box(0));
 lean::cnstr_set(x_47, 1, lean::box(0));
 x_57 = x_47;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_47);
 x_57 = lean::box(0);
}
x_58 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_0, x_11, x_2, x_55);
lean::dec(x_55);
if (lean::obj_tag(x_58) == 0)
{
obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_13);
lean::dec(x_57);
lean::dec(x_32);
lean::dec(x_28);
lean::dec(x_52);
lean::dec(x_53);
x_66 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_68 = x_58;
} else {
 lean::inc(x_66);
 lean::dec(x_58);
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
obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_70 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_72 = x_58;
} else {
 lean::inc(x_70);
 lean::dec(x_58);
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
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_28);
lean::cnstr_set(x_78, 1, x_53);
if (lean::is_scalar(x_57)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_57;
}
lean::cnstr_set(x_79, 0, x_52);
lean::cnstr_set(x_79, 1, x_78);
if (lean::is_scalar(x_13)) {
 x_80 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_80 = x_13;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_73);
if (lean::is_scalar(x_32)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_32;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_75);
if (lean::is_scalar(x_72)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_72;
}
lean::cnstr_set(x_82, 0, x_81);
return x_82;
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
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
lean::inc(x_2);
lean::inc(x_11);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_2);
x_17 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(x_9, x_1, x_16);
lean::dec(x_16);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_11, x_19);
lean::dec(x_11);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_8);
lean::cnstr_set(x_22, 1, x_17);
lean::cnstr_set(x_22, 2, x_20);
return x_22;
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
lean::dec(x_8);
lean::dec(x_2);
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
lean::dec(x_5);
lean::dec(x_3);
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
obj* x_14; obj* x_15; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_2);
x_14 = l_lean_elaborator_elab__def__like___closed__1;
x_15 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_14, x_4, x_5);
lean::dec(x_4);
return x_15;
}
else
{
obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_27; obj* x_30; 
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
x_30 = l_lean_elaborator_decl__modifiers__to__pexpr(x_1, x_4, x_5);
if (lean::obj_tag(x_30) == 0)
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_17);
lean::dec(x_24);
lean::dec(x_27);
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_41 = lean::cnstr_get(x_30, 0);
lean::inc(x_41);
lean::dec(x_30);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
lean::dec(x_41);
x_49 = lean::box(0);
lean::inc(x_3);
x_51 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_51, 0, x_3);
x_52 = lean_expr_mk_lit(x_51);
if (lean::obj_tag(x_17) == 0)
{
obj* x_56; obj* x_58; 
x_56 = l_lean_expander_get__opt__type___main(x_24);
lean::dec(x_24);
x_58 = l_lean_elaborator_to__pexpr___main(x_56, x_4, x_46);
lean::dec(x_46);
if (lean::obj_tag(x_17) == 0)
{
if (lean::obj_tag(x_58) == 0)
{
obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_44);
lean::dec(x_27);
lean::dec(x_52);
x_66 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_68 = x_58;
} else {
 lean::inc(x_66);
 lean::dec(x_58);
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
obj* x_70; 
x_70 = lean::cnstr_get(x_58, 0);
lean::inc(x_70);
lean::dec(x_58);
x_53 = x_49;
x_54 = x_70;
goto lbl_55;
}
}
else
{
if (lean::obj_tag(x_58) == 0)
{
obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_44);
lean::dec(x_27);
lean::dec(x_52);
x_79 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_81 = x_58;
} else {
 lean::inc(x_79);
 lean::dec(x_58);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
return x_82;
}
else
{
obj* x_83; obj* x_86; obj* x_89; obj* x_92; 
x_83 = lean::cnstr_get(x_17, 0);
lean::inc(x_83);
lean::dec(x_17);
x_86 = lean::cnstr_get(x_58, 0);
lean::inc(x_86);
lean::dec(x_58);
x_89 = lean::cnstr_get(x_83, 1);
lean::inc(x_89);
lean::dec(x_83);
x_92 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(x_89);
x_53 = x_92;
x_54 = x_86;
goto lbl_55;
}
}
}
else
{
obj* x_93; obj* x_95; obj* x_97; obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_113; obj* x_114; obj* x_115; obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_126; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_137; obj* x_140; obj* x_141; obj* x_143; 
x_93 = lean::cnstr_get(x_17, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_46, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_46, 1);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_46, 2);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_46, 3);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_46, 4);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_103, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_103, 1);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_93, 1);
lean::inc(x_109);
lean::dec(x_93);
lean::inc(x_109);
x_113 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(x_109);
x_114 = l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(x_107, x_113);
x_115 = lean::cnstr_get(x_103, 2);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_103, 3);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_103, 4);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_103, 5);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_103, 6);
lean::inc(x_123);
lean::dec(x_103);
x_126 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_126, 0, x_105);
lean::cnstr_set(x_126, 1, x_114);
lean::cnstr_set(x_126, 2, x_115);
lean::cnstr_set(x_126, 3, x_117);
lean::cnstr_set(x_126, 4, x_119);
lean::cnstr_set(x_126, 5, x_121);
lean::cnstr_set(x_126, 6, x_123);
x_127 = lean::cnstr_get(x_46, 5);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_46, 6);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_46, 7);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_46, 8);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_46, 9);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_46, 10);
lean::inc(x_137);
lean::dec(x_46);
x_140 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_140, 0, x_95);
lean::cnstr_set(x_140, 1, x_97);
lean::cnstr_set(x_140, 2, x_99);
lean::cnstr_set(x_140, 3, x_101);
lean::cnstr_set(x_140, 4, x_126);
lean::cnstr_set(x_140, 5, x_127);
lean::cnstr_set(x_140, 6, x_129);
lean::cnstr_set(x_140, 7, x_131);
lean::cnstr_set(x_140, 8, x_133);
lean::cnstr_set(x_140, 9, x_135);
lean::cnstr_set(x_140, 10, x_137);
x_141 = l_lean_expander_get__opt__type___main(x_24);
lean::dec(x_24);
x_143 = l_lean_elaborator_to__pexpr___main(x_141, x_4, x_140);
lean::dec(x_140);
if (lean::obj_tag(x_17) == 0)
{
lean::dec(x_109);
if (lean::obj_tag(x_143) == 0)
{
obj* x_152; obj* x_154; obj* x_155; 
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_44);
lean::dec(x_27);
lean::dec(x_52);
x_152 = lean::cnstr_get(x_143, 0);
if (lean::is_exclusive(x_143)) {
 x_154 = x_143;
} else {
 lean::inc(x_152);
 lean::dec(x_143);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_152);
return x_155;
}
else
{
obj* x_156; 
x_156 = lean::cnstr_get(x_143, 0);
lean::inc(x_156);
lean::dec(x_143);
x_53 = x_49;
x_54 = x_156;
goto lbl_55;
}
}
else
{
lean::dec(x_17);
if (lean::obj_tag(x_143) == 0)
{
obj* x_167; obj* x_169; obj* x_170; 
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_44);
lean::dec(x_27);
lean::dec(x_52);
lean::dec(x_109);
x_167 = lean::cnstr_get(x_143, 0);
if (lean::is_exclusive(x_143)) {
 x_169 = x_143;
} else {
 lean::inc(x_167);
 lean::dec(x_143);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_167);
return x_170;
}
else
{
obj* x_171; obj* x_174; 
x_171 = lean::cnstr_get(x_143, 0);
lean::inc(x_171);
lean::dec(x_143);
x_174 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(x_109);
x_53 = x_174;
x_54 = x_171;
goto lbl_55;
}
}
}
lbl_55:
{
obj* x_175; obj* x_177; obj* x_179; obj* x_180; obj* x_181; obj* x_183; uint8 x_184; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_175 = lean::cnstr_get(x_54, 0);
x_177 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_set(x_54, 0, lean::box(0));
 lean::cnstr_set(x_54, 1, lean::box(0));
 x_179 = x_54;
} else {
 lean::inc(x_175);
 lean::inc(x_177);
 lean::dec(x_54);
 x_179 = lean::box(0);
}
x_180 = l_lean_elaborator_names__to__pexpr(x_53);
x_181 = lean::cnstr_get(x_19, 0);
lean::inc(x_181);
x_183 = l_lean_elaborator_mangle__ident(x_181);
x_184 = 4;
lean::inc(x_175);
lean::inc(x_183);
x_187 = lean_expr_local(x_183, x_183, x_175, x_184);
x_188 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set(x_188, 1, x_49);
x_189 = l_lean_elaborator_mk__eqns___closed__1;
x_190 = l_lean_expr_mk__capp(x_189, x_188);
switch (lean::obj_tag(x_21)) {
case 0:
{
obj* x_196; obj* x_199; obj* x_202; 
lean::dec(x_175);
lean::dec(x_179);
lean::dec(x_19);
x_196 = lean::cnstr_get(x_21, 0);
lean::inc(x_196);
lean::dec(x_21);
x_199 = lean::cnstr_get(x_196, 1);
lean::inc(x_199);
lean::dec(x_196);
x_202 = l_lean_elaborator_to__pexpr___main(x_199, x_4, x_177);
lean::dec(x_177);
if (lean::obj_tag(x_202) == 0)
{
obj* x_210; obj* x_212; obj* x_213; 
lean::dec(x_190);
lean::dec(x_180);
lean::dec(x_4);
lean::dec(x_44);
lean::dec(x_27);
lean::dec(x_52);
x_210 = lean::cnstr_get(x_202, 0);
if (lean::is_exclusive(x_202)) {
 x_212 = x_202;
} else {
 lean::inc(x_210);
 lean::dec(x_202);
 x_212 = lean::box(0);
}
if (lean::is_scalar(x_212)) {
 x_213 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_213 = x_212;
}
lean::cnstr_set(x_213, 0, x_210);
return x_213;
}
else
{
obj* x_214; 
x_214 = lean::cnstr_get(x_202, 0);
lean::inc(x_214);
lean::dec(x_202);
x_191 = x_214;
goto lbl_192;
}
}
case 1:
{
obj* x_219; obj* x_220; 
lean::dec(x_19);
lean::dec(x_21);
x_219 = l_lean_elaborator_mk__eqns(x_175, x_49);
if (lean::is_scalar(x_179)) {
 x_220 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_220 = x_179;
}
lean::cnstr_set(x_220, 0, x_219);
lean::cnstr_set(x_220, 1, x_177);
x_191 = x_220;
goto lbl_192;
}
default:
{
obj* x_222; obj* x_225; 
lean::dec(x_179);
x_222 = lean::cnstr_get(x_21, 0);
lean::inc(x_222);
lean::dec(x_21);
x_225 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_19, x_222, x_4, x_177);
lean::dec(x_177);
if (lean::obj_tag(x_225) == 0)
{
obj* x_234; obj* x_236; obj* x_237; 
lean::dec(x_175);
lean::dec(x_190);
lean::dec(x_180);
lean::dec(x_4);
lean::dec(x_44);
lean::dec(x_27);
lean::dec(x_52);
x_234 = lean::cnstr_get(x_225, 0);
if (lean::is_exclusive(x_225)) {
 x_236 = x_225;
} else {
 lean::inc(x_234);
 lean::dec(x_225);
 x_236 = lean::box(0);
}
if (lean::is_scalar(x_236)) {
 x_237 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_237 = x_236;
}
lean::cnstr_set(x_237, 0, x_234);
return x_237;
}
else
{
obj* x_238; obj* x_241; obj* x_243; obj* x_245; obj* x_246; obj* x_247; 
x_238 = lean::cnstr_get(x_225, 0);
lean::inc(x_238);
lean::dec(x_225);
x_241 = lean::cnstr_get(x_238, 0);
x_243 = lean::cnstr_get(x_238, 1);
if (lean::is_exclusive(x_238)) {
 x_245 = x_238;
} else {
 lean::inc(x_241);
 lean::inc(x_243);
 lean::dec(x_238);
 x_245 = lean::box(0);
}
x_246 = l_lean_elaborator_mk__eqns(x_175, x_241);
if (lean::is_scalar(x_245)) {
 x_247 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_247 = x_245;
}
lean::cnstr_set(x_247, 0, x_246);
lean::cnstr_set(x_247, 1, x_243);
x_191 = x_247;
goto lbl_192;
}
}
}
lbl_192:
{
obj* x_248; obj* x_250; obj* x_253; 
x_248 = lean::cnstr_get(x_191, 0);
lean::inc(x_248);
x_250 = lean::cnstr_get(x_191, 1);
lean::inc(x_250);
lean::dec(x_191);
x_253 = l_lean_elaborator_simple__binders__to__pexpr(x_27, x_4, x_250);
lean::dec(x_250);
if (lean::obj_tag(x_253) == 0)
{
obj* x_261; obj* x_263; obj* x_264; 
lean::dec(x_190);
lean::dec(x_180);
lean::dec(x_248);
lean::dec(x_4);
lean::dec(x_44);
lean::dec(x_52);
x_261 = lean::cnstr_get(x_253, 0);
if (lean::is_exclusive(x_253)) {
 x_263 = x_253;
} else {
 lean::inc(x_261);
 lean::dec(x_253);
 x_263 = lean::box(0);
}
if (lean::is_scalar(x_263)) {
 x_264 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_264 = x_263;
}
lean::cnstr_set(x_264, 0, x_261);
return x_264;
}
else
{
obj* x_265; obj* x_268; obj* x_270; obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_265 = lean::cnstr_get(x_253, 0);
lean::inc(x_265);
lean::dec(x_253);
x_268 = lean::cnstr_get(x_265, 0);
lean::inc(x_268);
x_270 = lean::cnstr_get(x_265, 1);
lean::inc(x_270);
lean::dec(x_265);
x_273 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_273, 0, x_248);
lean::cnstr_set(x_273, 1, x_49);
x_274 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_274, 0, x_268);
lean::cnstr_set(x_274, 1, x_273);
x_275 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_275, 0, x_190);
lean::cnstr_set(x_275, 1, x_274);
x_276 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_276, 0, x_180);
lean::cnstr_set(x_276, 1, x_275);
x_277 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_277, 0, x_52);
lean::cnstr_set(x_277, 1, x_276);
x_278 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_278, 0, x_44);
lean::cnstr_set(x_278, 1, x_277);
x_279 = l_lean_expr_mk__capp(x_189, x_278);
x_280 = l_lean_elaborator_elab__def__like___closed__2;
x_281 = lean_expr_mk_mdata(x_280, x_279);
x_282 = l_lean_elaborator_old__elab__command(x_0, x_281, x_4, x_270);
return x_282;
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_elab__def__like___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_elaborator_elab__def__like(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_3);
lean::dec(x_5);
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
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
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
obj* x_22; obj* x_23; 
lean::dec(x_8);
lean::dec(x_15);
lean::dec(x_17);
x_22 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_23 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_22, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_12);
lean::dec(x_10);
x_26 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
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
obj* x_30; 
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
x_13 = x_30;
goto lbl_14;
}
}
else
{
obj* x_33; 
x_33 = lean::cnstr_get(x_17, 0);
lean::inc(x_33);
lean::dec(x_17);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; 
x_36 = lean::cnstr_get(x_15, 1);
lean::inc(x_36);
lean::dec(x_15);
if (lean::obj_tag(x_36) == 0)
{
obj* x_40; obj* x_41; 
lean::dec(x_8);
x_40 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_41 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_40, x_2, x_3);
if (lean::obj_tag(x_41) == 0)
{
obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_12);
lean::dec(x_10);
x_44 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_46 = x_41;
} else {
 lean::inc(x_44);
 lean::dec(x_41);
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
obj* x_48; 
x_48 = lean::cnstr_get(x_41, 0);
lean::inc(x_48);
lean::dec(x_41);
x_13 = x_48;
goto lbl_14;
}
}
else
{
obj* x_51; obj* x_54; obj* x_57; 
x_51 = lean::cnstr_get(x_36, 0);
lean::inc(x_51);
lean::dec(x_36);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
lean::dec(x_51);
x_57 = l_lean_elaborator_to__pexpr___main(x_54, x_2, x_3);
if (lean::obj_tag(x_57) == 0)
{
obj* x_61; obj* x_63; obj* x_64; 
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_10);
x_61 = lean::cnstr_get(x_57, 0);
if (lean::is_exclusive(x_57)) {
 x_63 = x_57;
} else {
 lean::inc(x_61);
 lean::dec(x_57);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_61);
return x_64;
}
else
{
obj* x_65; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_76; uint8 x_77; obj* x_79; obj* x_80; 
x_65 = lean::cnstr_get(x_57, 0);
lean::inc(x_65);
lean::dec(x_57);
x_68 = lean::cnstr_get(x_65, 0);
x_70 = lean::cnstr_get(x_65, 1);
if (lean::is_exclusive(x_65)) {
 x_72 = x_65;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_65);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_8, 1);
lean::inc(x_73);
lean::dec(x_8);
x_76 = l_lean_elaborator_mangle__ident(x_73);
x_77 = 0;
lean::inc(x_76);
x_79 = lean_expr_local(x_76, x_76, x_68, x_77);
if (lean::is_scalar(x_72)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_72;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_70);
x_13 = x_80;
goto lbl_14;
}
}
}
else
{
obj* x_84; obj* x_85; 
lean::dec(x_8);
lean::dec(x_15);
lean::dec(x_33);
x_84 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_85 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_84, x_2, x_3);
if (lean::obj_tag(x_85) == 0)
{
obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_12);
lean::dec(x_10);
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
obj* x_92; 
x_92 = lean::cnstr_get(x_85, 0);
lean::inc(x_92);
lean::dec(x_85);
x_13 = x_92;
goto lbl_14;
}
}
}
lbl_14:
{
obj* x_95; obj* x_97; obj* x_100; 
x_95 = lean::cnstr_get(x_13, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_13, 1);
lean::inc(x_97);
lean::dec(x_13);
x_100 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_10, x_2, x_97);
lean::dec(x_97);
if (lean::obj_tag(x_100) == 0)
{
obj* x_104; obj* x_106; obj* x_107; 
lean::dec(x_12);
lean::dec(x_95);
x_104 = lean::cnstr_get(x_100, 0);
if (lean::is_exclusive(x_100)) {
 x_106 = x_100;
} else {
 lean::inc(x_104);
 lean::dec(x_100);
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
obj* x_108; obj* x_110; obj* x_111; obj* x_113; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_108 = lean::cnstr_get(x_100, 0);
if (lean::is_exclusive(x_100)) {
 x_110 = x_100;
} else {
 lean::inc(x_108);
 lean::dec(x_100);
 x_110 = lean::box(0);
}
x_111 = lean::cnstr_get(x_108, 0);
x_113 = lean::cnstr_get(x_108, 1);
if (lean::is_exclusive(x_108)) {
 x_115 = x_108;
} else {
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_108);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_116 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_116 = x_12;
}
lean::cnstr_set(x_116, 0, x_95);
lean::cnstr_set(x_116, 1, x_111);
if (lean::is_scalar(x_115)) {
 x_117 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_117 = x_115;
}
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_113);
if (lean::is_scalar(x_110)) {
 x_118 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_118 = x_110;
}
lean::cnstr_set(x_118, 0, x_117);
return x_118;
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
lean::dec(x_8);
lean::dec(x_2);
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
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
lean::dec(x_7);
x_15 = l_lean_elaborator_to__pexpr___main(x_12, x_1, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
x_18 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_20 = x_15;
} else {
 lean::inc(x_18);
 lean::dec(x_15);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_30; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
lean::dec(x_15);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_9, x_1, x_27);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_11);
lean::dec(x_25);
x_34 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_36 = x_30;
} else {
 lean::inc(x_34);
 lean::dec(x_30);
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
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_38 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_40 = x_30;
} else {
 lean::inc(x_38);
 lean::dec(x_30);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_38, 0);
x_43 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 x_45 = x_38;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::dec(x_38);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_11;
}
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_41);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_40)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_40;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
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
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
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
obj* x_22; obj* x_23; 
lean::dec(x_18);
x_22 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_23 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_22, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_12);
lean::dec(x_10);
x_26 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
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
obj* x_30; 
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
x_13 = x_30;
goto lbl_14;
}
}
else
{
obj* x_33; uint8 x_36; obj* x_37; obj* x_38; obj* x_40; 
x_33 = lean::cnstr_get(x_18, 0);
lean::inc(x_33);
lean::dec(x_18);
x_36 = 0;
x_37 = lean::box(x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_33);
lean::inc(x_3);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_3);
x_13 = x_40;
goto lbl_14;
}
}
case 1:
{
obj* x_41; obj* x_44; uint8 x_47; obj* x_48; obj* x_49; obj* x_51; 
x_41 = lean::cnstr_get(x_8, 0);
lean::inc(x_41);
lean::dec(x_8);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
x_47 = 1;
x_48 = lean::box(x_47);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_44);
lean::inc(x_3);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_3);
x_13 = x_51;
goto lbl_14;
}
case 2:
{
obj* x_52; obj* x_55; uint8 x_58; obj* x_59; obj* x_60; obj* x_62; 
x_52 = lean::cnstr_get(x_8, 0);
lean::inc(x_52);
lean::dec(x_8);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_58 = 2;
x_59 = lean::box(x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_55);
lean::inc(x_3);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_3);
x_13 = x_62;
goto lbl_14;
}
default:
{
obj* x_63; obj* x_66; uint8 x_69; obj* x_70; obj* x_71; obj* x_73; 
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
lean::inc(x_3);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set(x_73, 1, x_3);
x_13 = x_73;
goto lbl_14;
}
}
lbl_14:
{
obj* x_74; obj* x_76; obj* x_79; obj* x_81; obj* x_84; obj* x_86; obj* x_89; obj* x_91; 
x_74 = lean::cnstr_get(x_13, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_13, 1);
lean::inc(x_76);
lean::dec(x_13);
x_79 = lean::cnstr_get(x_74, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_74, 1);
lean::inc(x_81);
lean::dec(x_74);
x_84 = lean::cnstr_get(x_81, 2);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_84, 1);
lean::inc(x_86);
lean::dec(x_84);
x_89 = l_lean_expander_get__opt__type___main(x_86);
lean::dec(x_86);
x_91 = l_lean_elaborator_to__pexpr___main(x_89, x_2, x_76);
lean::dec(x_76);
if (lean::obj_tag(x_91) == 0)
{
obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_81);
lean::dec(x_79);
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
lean::dec(x_106);
if (lean::obj_tag(x_109) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_12);
lean::dec(x_81);
lean::dec(x_79);
lean::dec(x_104);
x_115 = lean::cnstr_get(x_109, 0);
if (lean::is_exclusive(x_109)) {
 x_117 = x_109;
} else {
 lean::inc(x_115);
 lean::dec(x_109);
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
obj* x_119; obj* x_121; obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; obj* x_130; obj* x_131; obj* x_133; obj* x_134; obj* x_135; obj* x_138; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_119 = lean::cnstr_get(x_109, 0);
if (lean::is_exclusive(x_109)) {
 x_121 = x_109;
} else {
 lean::inc(x_119);
 lean::dec(x_109);
 x_121 = lean::box(0);
}
x_122 = lean::cnstr_get(x_119, 0);
x_124 = lean::cnstr_get(x_119, 1);
if (lean::is_exclusive(x_119)) {
 x_126 = x_119;
} else {
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_119);
 x_126 = lean::box(0);
}
x_127 = l_lean_elaborator_mk__eqns___closed__1;
x_128 = l_lean_elaborator_dummy;
x_129 = lean::unbox(x_79);
x_130 = lean_expr_local(x_127, x_127, x_128, x_129);
x_131 = lean::cnstr_get(x_81, 0);
lean::inc(x_131);
x_133 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(x_131);
x_134 = l_lean_elaborator_names__to__pexpr(x_133);
x_135 = lean::cnstr_get(x_81, 1);
lean::inc(x_135);
lean::dec(x_81);
x_138 = l_lean_elaborator_infer__mod__to__pexpr(x_135);
lean::dec(x_135);
x_140 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_12;
}
lean::cnstr_set(x_141, 0, x_104);
lean::cnstr_set(x_141, 1, x_140);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_138);
lean::cnstr_set(x_142, 1, x_141);
x_143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_143, 0, x_134);
lean::cnstr_set(x_143, 1, x_142);
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_130);
lean::cnstr_set(x_144, 1, x_143);
x_145 = l_lean_expr_mk__capp(x_127, x_144);
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_122);
if (lean::is_scalar(x_126)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_126;
}
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_124);
if (lean::is_scalar(x_121)) {
 x_148 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_148 = x_121;
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
lean::dec(x_8);
lean::dec(x_2);
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
lean::dec(x_5);
lean::dec(x_3);
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
lean::dec(x_5);
lean::dec(x_3);
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
lean::dec(x_5);
lean::dec(x_3);
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_2, 4);
x_6 = l_lean_parser_command_declaration_has__view;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
lean::inc(x_0);
x_11 = lean::apply_1(x_7, x_0);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_20; obj* x_23; obj* x_24; 
lean::dec(x_17);
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
lean::dec(x_11);
x_23 = lean::mk_nat_obj(1u);
x_24 = l_lean_elaborator_elab__def__like(x_0, x_20, x_14, x_23, x_1, x_2);
lean::dec(x_0);
x_4 = x_24;
goto lbl_5;
}
case 1:
{
obj* x_27; obj* x_30; obj* x_31; 
lean::dec(x_17);
x_27 = lean::cnstr_get(x_11, 0);
lean::inc(x_27);
lean::dec(x_11);
x_30 = lean::mk_nat_obj(5u);
x_31 = l_lean_elaborator_elab__def__like(x_0, x_27, x_14, x_30, x_1, x_2);
lean::dec(x_0);
x_4 = x_31;
goto lbl_5;
}
default:
{
obj* x_34; obj* x_37; obj* x_38; 
lean::dec(x_17);
x_34 = lean::cnstr_get(x_11, 0);
lean::inc(x_34);
lean::dec(x_11);
x_37 = lean::mk_nat_obj(0u);
x_38 = l_lean_elaborator_elab__def__like(x_0, x_34, x_14, x_37, x_1, x_2);
lean::dec(x_0);
x_4 = x_38;
goto lbl_5;
}
}
}
case 1:
{
obj* x_40; obj* x_43; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_40 = lean::cnstr_get(x_12, 0);
lean::inc(x_40);
lean::dec(x_12);
x_43 = lean::cnstr_get(x_11, 0);
lean::inc(x_43);
lean::dec(x_11);
x_46 = lean::box(0);
x_47 = lean::cnstr_get(x_40, 1);
lean::inc(x_47);
x_49 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
x_50 = l_option_get__or__else___main___rarg(x_47, x_49);
lean::dec(x_47);
x_52 = lean::cnstr_get(x_40, 2);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_52, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_52, 1);
lean::inc(x_56);
lean::dec(x_52);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_56);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_54);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::cnstr_get(x_40, 3);
lean::inc(x_61);
lean::dec(x_40);
x_64 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
x_65 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_46);
lean::cnstr_set(x_65, 2, x_50);
lean::cnstr_set(x_65, 3, x_60);
lean::cnstr_set(x_65, 4, x_61);
x_66 = lean::mk_nat_obj(3u);
x_67 = l_lean_elaborator_elab__def__like(x_0, x_43, x_65, x_66, x_1, x_2);
lean::dec(x_0);
x_4 = x_67;
goto lbl_5;
}
case 2:
{
obj* x_69; obj* x_72; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_83; obj* x_84; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_69 = lean::cnstr_get(x_12, 0);
lean::inc(x_69);
lean::dec(x_12);
x_72 = lean::cnstr_get(x_11, 0);
lean::inc(x_72);
lean::dec(x_11);
x_75 = lean::box(0);
x_76 = lean::cnstr_get(x_69, 1);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_76, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_76, 1);
lean::inc(x_80);
lean::dec(x_76);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_80);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_78);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::cnstr_get(x_69, 2);
lean::inc(x_85);
lean::dec(x_69);
x_88 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__2;
x_89 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__1;
x_90 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_75);
lean::cnstr_set(x_90, 2, x_89);
lean::cnstr_set(x_90, 3, x_84);
lean::cnstr_set(x_90, 4, x_85);
x_91 = lean::mk_nat_obj(2u);
x_92 = l_lean_elaborator_elab__def__like(x_0, x_72, x_90, x_91, x_1, x_2);
lean::dec(x_0);
x_4 = x_92;
goto lbl_5;
}
case 3:
{
obj* x_94; obj* x_97; obj* x_99; 
x_94 = lean::cnstr_get(x_12, 0);
lean::inc(x_94);
lean::dec(x_12);
x_97 = lean::cnstr_get(x_94, 2);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_97, 0);
lean::inc(x_99);
if (lean::obj_tag(x_99) == 0)
{
obj* x_105; obj* x_106; 
lean::dec(x_11);
lean::dec(x_97);
lean::dec(x_99);
lean::dec(x_94);
x_105 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_106 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_105, x_1, x_2);
lean::dec(x_1);
lean::dec(x_0);
x_4 = x_106;
goto lbl_5;
}
else
{
obj* x_109; 
x_109 = lean::cnstr_get(x_99, 0);
lean::inc(x_109);
lean::dec(x_99);
if (lean::obj_tag(x_109) == 0)
{
obj* x_112; obj* x_115; obj* x_118; obj* x_121; 
x_112 = lean::cnstr_get(x_94, 1);
lean::inc(x_112);
lean::dec(x_94);
x_115 = lean::cnstr_get(x_97, 1);
lean::inc(x_115);
lean::dec(x_97);
x_118 = lean::cnstr_get(x_11, 0);
lean::inc(x_118);
lean::dec(x_11);
x_121 = l_lean_elaborator_decl__modifiers__to__pexpr(x_118, x_1, x_2);
if (lean::obj_tag(x_121) == 0)
{
obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_112);
lean::dec(x_115);
x_126 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 x_128 = x_121;
} else {
 lean::inc(x_126);
 lean::dec(x_121);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
x_4 = x_129;
goto lbl_5;
}
else
{
obj* x_130; obj* x_133; obj* x_135; obj* x_138; obj* x_141; 
x_130 = lean::cnstr_get(x_121, 0);
lean::inc(x_130);
lean::dec(x_121);
x_133 = lean::cnstr_get(x_130, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_130, 1);
lean::inc(x_135);
lean::dec(x_130);
x_138 = lean::cnstr_get(x_115, 1);
lean::inc(x_138);
lean::dec(x_115);
x_141 = l_lean_elaborator_to__pexpr___main(x_138, x_1, x_135);
lean::dec(x_135);
if (lean::obj_tag(x_141) == 0)
{
obj* x_147; obj* x_149; obj* x_150; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_133);
lean::dec(x_112);
x_147 = lean::cnstr_get(x_141, 0);
if (lean::is_exclusive(x_141)) {
 x_149 = x_141;
} else {
 lean::inc(x_147);
 lean::dec(x_141);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_147);
x_4 = x_150;
goto lbl_5;
}
else
{
obj* x_151; obj* x_154; obj* x_156; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_151 = lean::cnstr_get(x_141, 0);
lean::inc(x_151);
lean::dec(x_141);
x_154 = lean::cnstr_get(x_151, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_151, 1);
lean::inc(x_156);
lean::dec(x_151);
x_159 = lean::box(0);
x_160 = l_lean_elaborator_ident__univ__params__to__pexpr(x_112);
x_161 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_161, 0, x_154);
lean::cnstr_set(x_161, 1, x_159);
x_162 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_162, 0, x_160);
lean::cnstr_set(x_162, 1, x_161);
x_163 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_163, 0, x_133);
lean::cnstr_set(x_163, 1, x_162);
x_164 = l_lean_elaborator_mk__eqns___closed__1;
x_165 = l_lean_expr_mk__capp(x_164, x_163);
x_166 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3;
x_167 = lean_expr_mk_mdata(x_166, x_165);
x_168 = l_lean_elaborator_old__elab__command(x_0, x_167, x_1, x_156);
lean::dec(x_0);
x_4 = x_168;
goto lbl_5;
}
}
}
else
{
obj* x_174; obj* x_175; 
lean::dec(x_11);
lean::dec(x_97);
lean::dec(x_94);
lean::dec(x_109);
x_174 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_175 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_174, x_1, x_2);
lean::dec(x_1);
lean::dec(x_0);
x_4 = x_175;
goto lbl_5;
}
}
}
case 4:
{
obj* x_178; obj* x_181; 
x_178 = lean::cnstr_get(x_12, 0);
lean::inc(x_178);
lean::dec(x_12);
x_181 = lean::cnstr_get(x_178, 0);
lean::inc(x_181);
if (lean::obj_tag(x_181) == 0)
{
obj* x_183; obj* x_185; 
x_183 = lean::cnstr_get(x_178, 4);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_183, 0);
lean::inc(x_185);
if (lean::obj_tag(x_185) == 0)
{
obj* x_191; obj* x_192; 
lean::dec(x_185);
lean::dec(x_183);
lean::dec(x_178);
lean::dec(x_11);
x_191 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_192 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_191, x_1, x_2);
lean::dec(x_1);
lean::dec(x_0);
x_4 = x_192;
goto lbl_5;
}
else
{
obj* x_195; obj* x_197; obj* x_199; obj* x_202; obj* x_205; obj* x_208; obj* x_212; 
x_195 = lean::cnstr_get(x_178, 2);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_178, 3);
lean::inc(x_197);
x_199 = lean::cnstr_get(x_178, 6);
lean::inc(x_199);
lean::dec(x_178);
x_202 = lean::cnstr_get(x_183, 1);
lean::inc(x_202);
lean::dec(x_183);
x_205 = lean::cnstr_get(x_185, 0);
lean::inc(x_205);
lean::dec(x_185);
x_208 = lean::cnstr_get(x_11, 0);
lean::inc(x_208);
lean::dec(x_11);
lean::inc(x_208);
x_212 = l_lean_elaborator_decl__modifiers__to__pexpr(x_208, x_1, x_2);
if (lean::obj_tag(x_212) == 0)
{
obj* x_221; obj* x_223; obj* x_224; 
lean::dec(x_195);
lean::dec(x_199);
lean::dec(x_202);
lean::dec(x_197);
lean::dec(x_208);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
x_221 = lean::cnstr_get(x_212, 0);
if (lean::is_exclusive(x_212)) {
 x_223 = x_212;
} else {
 lean::inc(x_221);
 lean::dec(x_212);
 x_223 = lean::box(0);
}
if (lean::is_scalar(x_223)) {
 x_224 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_224 = x_223;
}
lean::cnstr_set(x_224, 0, x_221);
x_4 = x_224;
goto lbl_5;
}
else
{
obj* x_225; obj* x_228; obj* x_230; obj* x_233; obj* x_234; obj* x_236; 
x_225 = lean::cnstr_get(x_212, 0);
lean::inc(x_225);
lean::dec(x_212);
x_228 = lean::cnstr_get(x_225, 0);
lean::inc(x_228);
x_230 = lean::cnstr_get(x_225, 1);
lean::inc(x_230);
lean::dec(x_225);
x_233 = lean::box(0);
x_236 = lean::cnstr_get(x_208, 1);
lean::inc(x_236);
lean::dec(x_208);
if (lean::obj_tag(x_236) == 0)
{
x_234 = x_233;
goto lbl_235;
}
else
{
obj* x_239; obj* x_242; 
x_239 = lean::cnstr_get(x_236, 0);
lean::inc(x_239);
lean::dec(x_236);
x_242 = lean::cnstr_get(x_239, 1);
lean::inc(x_242);
lean::dec(x_239);
x_234 = x_242;
goto lbl_235;
}
lbl_235:
{
obj* x_245; 
x_245 = l_lean_elaborator_attrs__to__pexpr(x_234, x_1, x_230);
lean::dec(x_230);
if (lean::obj_tag(x_245) == 0)
{
obj* x_255; obj* x_257; obj* x_258; 
lean::dec(x_195);
lean::dec(x_199);
lean::dec(x_202);
lean::dec(x_228);
lean::dec(x_197);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
x_255 = lean::cnstr_get(x_245, 0);
if (lean::is_exclusive(x_245)) {
 x_257 = x_245;
} else {
 lean::inc(x_255);
 lean::dec(x_245);
 x_257 = lean::box(0);
}
if (lean::is_scalar(x_257)) {
 x_258 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_258 = x_257;
}
lean::cnstr_set(x_258, 0, x_255);
x_4 = x_258;
goto lbl_5;
}
else
{
obj* x_259; obj* x_262; obj* x_264; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_259 = lean::cnstr_get(x_245, 0);
lean::inc(x_259);
lean::dec(x_245);
x_262 = lean::cnstr_get(x_259, 0);
lean::inc(x_262);
x_264 = lean::cnstr_get(x_259, 1);
lean::inc(x_264);
lean::dec(x_259);
x_267 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_267, 0, x_262);
lean::cnstr_set(x_267, 1, x_233);
x_268 = l_lean_elaborator_mk__eqns___closed__1;
x_269 = l_lean_expr_mk__capp(x_268, x_267);
if (lean::obj_tag(x_195) == 0)
{
obj* x_273; obj* x_275; 
x_273 = l_lean_expander_get__opt__type___main(x_202);
lean::dec(x_202);
x_275 = l_lean_elaborator_to__pexpr___main(x_273, x_1, x_264);
lean::dec(x_264);
if (lean::obj_tag(x_195) == 0)
{
if (lean::obj_tag(x_275) == 0)
{
obj* x_284; obj* x_286; obj* x_287; 
lean::dec(x_199);
lean::dec(x_228);
lean::dec(x_197);
lean::dec(x_269);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
x_284 = lean::cnstr_get(x_275, 0);
if (lean::is_exclusive(x_275)) {
 x_286 = x_275;
} else {
 lean::inc(x_284);
 lean::dec(x_275);
 x_286 = lean::box(0);
}
if (lean::is_scalar(x_286)) {
 x_287 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_287 = x_286;
}
lean::cnstr_set(x_287, 0, x_284);
x_4 = x_287;
goto lbl_5;
}
else
{
obj* x_288; 
x_288 = lean::cnstr_get(x_275, 0);
lean::inc(x_288);
lean::dec(x_275);
x_270 = x_233;
x_271 = x_288;
goto lbl_272;
}
}
else
{
if (lean::obj_tag(x_275) == 0)
{
obj* x_298; obj* x_300; obj* x_301; 
lean::dec(x_199);
lean::dec(x_228);
lean::dec(x_197);
lean::dec(x_269);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
x_298 = lean::cnstr_get(x_275, 0);
if (lean::is_exclusive(x_275)) {
 x_300 = x_275;
} else {
 lean::inc(x_298);
 lean::dec(x_275);
 x_300 = lean::box(0);
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_298);
x_4 = x_301;
goto lbl_5;
}
else
{
obj* x_302; obj* x_305; obj* x_308; obj* x_311; 
x_302 = lean::cnstr_get(x_195, 0);
lean::inc(x_302);
lean::dec(x_195);
x_305 = lean::cnstr_get(x_275, 0);
lean::inc(x_305);
lean::dec(x_275);
x_308 = lean::cnstr_get(x_302, 1);
lean::inc(x_308);
lean::dec(x_302);
x_311 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_308);
x_270 = x_311;
x_271 = x_305;
goto lbl_272;
}
}
}
else
{
obj* x_312; obj* x_314; obj* x_316; obj* x_318; obj* x_320; obj* x_322; obj* x_324; obj* x_326; obj* x_328; obj* x_332; obj* x_333; obj* x_334; obj* x_336; obj* x_338; obj* x_340; obj* x_342; obj* x_345; obj* x_346; obj* x_348; obj* x_350; obj* x_352; obj* x_354; obj* x_356; obj* x_359; obj* x_360; obj* x_362; 
x_312 = lean::cnstr_get(x_195, 0);
lean::inc(x_312);
x_314 = lean::cnstr_get(x_264, 0);
lean::inc(x_314);
x_316 = lean::cnstr_get(x_264, 1);
lean::inc(x_316);
x_318 = lean::cnstr_get(x_264, 2);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_264, 3);
lean::inc(x_320);
x_322 = lean::cnstr_get(x_264, 4);
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
x_346 = lean::cnstr_get(x_264, 5);
lean::inc(x_346);
x_348 = lean::cnstr_get(x_264, 6);
lean::inc(x_348);
x_350 = lean::cnstr_get(x_264, 7);
lean::inc(x_350);
x_352 = lean::cnstr_get(x_264, 8);
lean::inc(x_352);
x_354 = lean::cnstr_get(x_264, 9);
lean::inc(x_354);
x_356 = lean::cnstr_get(x_264, 10);
lean::inc(x_356);
lean::dec(x_264);
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
x_360 = l_lean_expander_get__opt__type___main(x_202);
lean::dec(x_202);
x_362 = l_lean_elaborator_to__pexpr___main(x_360, x_1, x_359);
lean::dec(x_359);
if (lean::obj_tag(x_195) == 0)
{
lean::dec(x_328);
if (lean::obj_tag(x_362) == 0)
{
obj* x_372; obj* x_374; obj* x_375; 
lean::dec(x_199);
lean::dec(x_228);
lean::dec(x_197);
lean::dec(x_269);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
x_372 = lean::cnstr_get(x_362, 0);
if (lean::is_exclusive(x_362)) {
 x_374 = x_362;
} else {
 lean::inc(x_372);
 lean::dec(x_362);
 x_374 = lean::box(0);
}
if (lean::is_scalar(x_374)) {
 x_375 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_375 = x_374;
}
lean::cnstr_set(x_375, 0, x_372);
x_4 = x_375;
goto lbl_5;
}
else
{
obj* x_376; 
x_376 = lean::cnstr_get(x_362, 0);
lean::inc(x_376);
lean::dec(x_362);
x_270 = x_233;
x_271 = x_376;
goto lbl_272;
}
}
else
{
lean::dec(x_195);
if (lean::obj_tag(x_362) == 0)
{
obj* x_388; obj* x_390; obj* x_391; 
lean::dec(x_199);
lean::dec(x_228);
lean::dec(x_197);
lean::dec(x_269);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_205);
lean::dec(x_328);
x_388 = lean::cnstr_get(x_362, 0);
if (lean::is_exclusive(x_362)) {
 x_390 = x_362;
} else {
 lean::inc(x_388);
 lean::dec(x_362);
 x_390 = lean::box(0);
}
if (lean::is_scalar(x_390)) {
 x_391 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_391 = x_390;
}
lean::cnstr_set(x_391, 0, x_388);
x_4 = x_391;
goto lbl_5;
}
else
{
obj* x_392; obj* x_395; 
x_392 = lean::cnstr_get(x_362, 0);
lean::inc(x_392);
lean::dec(x_362);
x_395 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(x_328);
x_270 = x_395;
x_271 = x_392;
goto lbl_272;
}
}
}
lbl_272:
{
obj* x_396; obj* x_398; obj* x_401; 
x_396 = lean::cnstr_get(x_271, 0);
lean::inc(x_396);
x_398 = lean::cnstr_get(x_271, 1);
lean::inc(x_398);
lean::dec(x_271);
x_401 = l_lean_elaborator_simple__binders__to__pexpr(x_205, x_1, x_398);
lean::dec(x_398);
if (lean::obj_tag(x_401) == 0)
{
obj* x_411; obj* x_413; obj* x_414; 
lean::dec(x_199);
lean::dec(x_228);
lean::dec(x_197);
lean::dec(x_269);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_396);
lean::dec(x_270);
x_411 = lean::cnstr_get(x_401, 0);
if (lean::is_exclusive(x_401)) {
 x_413 = x_401;
} else {
 lean::inc(x_411);
 lean::dec(x_401);
 x_413 = lean::box(0);
}
if (lean::is_scalar(x_413)) {
 x_414 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_414 = x_413;
}
lean::cnstr_set(x_414, 0, x_411);
x_4 = x_414;
goto lbl_5;
}
else
{
obj* x_415; obj* x_418; obj* x_420; obj* x_424; 
x_415 = lean::cnstr_get(x_401, 0);
lean::inc(x_415);
lean::dec(x_401);
x_418 = lean::cnstr_get(x_415, 0);
lean::inc(x_418);
x_420 = lean::cnstr_get(x_415, 1);
lean::inc(x_420);
lean::dec(x_415);
lean::inc(x_199);
x_424 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_199, x_1, x_420);
lean::dec(x_420);
if (lean::obj_tag(x_424) == 0)
{
obj* x_435; obj* x_437; obj* x_438; 
lean::dec(x_199);
lean::dec(x_228);
lean::dec(x_197);
lean::dec(x_269);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_396);
lean::dec(x_270);
lean::dec(x_418);
x_435 = lean::cnstr_get(x_424, 0);
if (lean::is_exclusive(x_424)) {
 x_437 = x_424;
} else {
 lean::inc(x_435);
 lean::dec(x_424);
 x_437 = lean::box(0);
}
if (lean::is_scalar(x_437)) {
 x_438 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_438 = x_437;
}
lean::cnstr_set(x_438, 0, x_435);
x_4 = x_438;
goto lbl_5;
}
else
{
obj* x_439; obj* x_442; obj* x_444; obj* x_447; obj* x_448; obj* x_451; uint8 x_452; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; 
x_439 = lean::cnstr_get(x_424, 0);
lean::inc(x_439);
lean::dec(x_424);
x_442 = lean::cnstr_get(x_439, 0);
lean::inc(x_442);
x_444 = lean::cnstr_get(x_439, 1);
lean::inc(x_444);
lean::dec(x_439);
x_447 = l_lean_elaborator_names__to__pexpr(x_270);
x_448 = lean::cnstr_get(x_197, 0);
lean::inc(x_448);
lean::dec(x_197);
x_451 = l_lean_elaborator_mangle__ident(x_448);
x_452 = 0;
lean::inc(x_451);
x_454 = lean_expr_local(x_451, x_451, x_396, x_452);
x_455 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_455, 0, x_454);
lean::cnstr_set(x_455, 1, x_233);
x_456 = l_lean_expr_mk__capp(x_268, x_455);
x_457 = l_lean_expr_mk__capp(x_268, x_442);
x_458 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_458, 0, x_457);
lean::cnstr_set(x_458, 1, x_233);
x_459 = l_lean_expr_mk__capp(x_268, x_458);
x_460 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(x_199);
x_461 = l_lean_expr_mk__capp(x_268, x_460);
x_462 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_462, 0, x_461);
lean::cnstr_set(x_462, 1, x_233);
x_463 = l_lean_expr_mk__capp(x_268, x_462);
x_464 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_464, 0, x_463);
lean::cnstr_set(x_464, 1, x_233);
x_465 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_465, 0, x_459);
lean::cnstr_set(x_465, 1, x_464);
x_466 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_466, 0, x_418);
lean::cnstr_set(x_466, 1, x_465);
x_467 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_467, 0, x_456);
lean::cnstr_set(x_467, 1, x_466);
x_468 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_468, 0, x_447);
lean::cnstr_set(x_468, 1, x_467);
x_469 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_469, 0, x_269);
lean::cnstr_set(x_469, 1, x_468);
x_470 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_470, 0, x_228);
lean::cnstr_set(x_470, 1, x_469);
x_471 = l_lean_expr_mk__capp(x_268, x_470);
x_472 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
x_473 = lean_expr_mk_mdata(x_472, x_471);
x_474 = l_lean_elaborator_old__elab__command(x_0, x_473, x_1, x_444);
lean::dec(x_0);
x_4 = x_474;
goto lbl_5;
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
obj* x_479; obj* x_480; 
lean::dec(x_181);
lean::dec(x_178);
lean::dec(x_11);
x_479 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_480 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_479, x_1, x_2);
lean::dec(x_1);
lean::dec(x_0);
x_4 = x_480;
goto lbl_5;
}
}
default:
{
obj* x_483; obj* x_486; 
x_483 = lean::cnstr_get(x_12, 0);
lean::inc(x_483);
lean::dec(x_12);
x_486 = lean::cnstr_get(x_483, 0);
lean::inc(x_486);
if (lean::obj_tag(x_486) == 0)
{
obj* x_489; obj* x_491; 
lean::dec(x_486);
x_489 = lean::cnstr_get(x_483, 3);
lean::inc(x_489);
x_491 = lean::cnstr_get(x_489, 0);
lean::inc(x_491);
if (lean::obj_tag(x_491) == 0)
{
obj* x_497; obj* x_498; 
lean::dec(x_489);
lean::dec(x_11);
lean::dec(x_483);
lean::dec(x_491);
x_497 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_498 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_497, x_1, x_2);
lean::dec(x_1);
lean::dec(x_0);
x_4 = x_498;
goto lbl_5;
}
else
{
obj* x_501; obj* x_503; obj* x_505; obj* x_507; obj* x_509; obj* x_512; obj* x_515; obj* x_518; obj* x_521; 
x_501 = lean::cnstr_get(x_483, 1);
lean::inc(x_501);
x_503 = lean::cnstr_get(x_483, 2);
lean::inc(x_503);
x_505 = lean::cnstr_get(x_483, 4);
lean::inc(x_505);
x_507 = lean::cnstr_get(x_483, 6);
lean::inc(x_507);
x_509 = lean::cnstr_get(x_483, 7);
lean::inc(x_509);
lean::dec(x_483);
x_512 = lean::cnstr_get(x_489, 1);
lean::inc(x_512);
lean::dec(x_489);
x_515 = lean::cnstr_get(x_491, 0);
lean::inc(x_515);
lean::dec(x_491);
x_518 = lean::cnstr_get(x_11, 0);
lean::inc(x_518);
lean::dec(x_11);
x_521 = l_lean_elaborator_decl__modifiers__to__pexpr(x_518, x_1, x_2);
if (lean::obj_tag(x_521) == 0)
{
obj* x_531; obj* x_533; obj* x_534; 
lean::dec(x_512);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_515);
lean::dec(x_503);
lean::dec(x_507);
lean::dec(x_505);
lean::dec(x_509);
lean::dec(x_501);
x_531 = lean::cnstr_get(x_521, 0);
if (lean::is_exclusive(x_521)) {
 x_533 = x_521;
} else {
 lean::inc(x_531);
 lean::dec(x_521);
 x_533 = lean::box(0);
}
if (lean::is_scalar(x_533)) {
 x_534 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_534 = x_533;
}
lean::cnstr_set(x_534, 0, x_531);
x_4 = x_534;
goto lbl_5;
}
else
{
obj* x_535; obj* x_538; obj* x_540; obj* x_543; obj* x_544; obj* x_545; 
x_535 = lean::cnstr_get(x_521, 0);
lean::inc(x_535);
lean::dec(x_521);
x_538 = lean::cnstr_get(x_535, 0);
lean::inc(x_538);
x_540 = lean::cnstr_get(x_535, 1);
lean::inc(x_540);
lean::dec(x_535);
x_543 = lean::box(0);
if (lean::obj_tag(x_501) == 0)
{
obj* x_547; obj* x_549; 
x_547 = l_lean_expander_get__opt__type___main(x_512);
lean::dec(x_512);
x_549 = l_lean_elaborator_to__pexpr___main(x_547, x_1, x_540);
lean::dec(x_540);
if (lean::obj_tag(x_501) == 0)
{
if (lean::obj_tag(x_549) == 0)
{
obj* x_559; obj* x_561; obj* x_562; 
lean::dec(x_538);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_515);
lean::dec(x_503);
lean::dec(x_507);
lean::dec(x_505);
lean::dec(x_509);
x_559 = lean::cnstr_get(x_549, 0);
if (lean::is_exclusive(x_549)) {
 x_561 = x_549;
} else {
 lean::inc(x_559);
 lean::dec(x_549);
 x_561 = lean::box(0);
}
if (lean::is_scalar(x_561)) {
 x_562 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_562 = x_561;
}
lean::cnstr_set(x_562, 0, x_559);
x_4 = x_562;
goto lbl_5;
}
else
{
obj* x_563; 
x_563 = lean::cnstr_get(x_549, 0);
lean::inc(x_563);
lean::dec(x_549);
x_544 = x_543;
x_545 = x_563;
goto lbl_546;
}
}
else
{
if (lean::obj_tag(x_549) == 0)
{
obj* x_574; obj* x_576; obj* x_577; 
lean::dec(x_538);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_515);
lean::dec(x_503);
lean::dec(x_507);
lean::dec(x_505);
lean::dec(x_509);
x_574 = lean::cnstr_get(x_549, 0);
if (lean::is_exclusive(x_549)) {
 x_576 = x_549;
} else {
 lean::inc(x_574);
 lean::dec(x_549);
 x_576 = lean::box(0);
}
if (lean::is_scalar(x_576)) {
 x_577 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_577 = x_576;
}
lean::cnstr_set(x_577, 0, x_574);
x_4 = x_577;
goto lbl_5;
}
else
{
obj* x_578; obj* x_581; obj* x_584; obj* x_587; 
x_578 = lean::cnstr_get(x_501, 0);
lean::inc(x_578);
lean::dec(x_501);
x_581 = lean::cnstr_get(x_549, 0);
lean::inc(x_581);
lean::dec(x_549);
x_584 = lean::cnstr_get(x_578, 1);
lean::inc(x_584);
lean::dec(x_578);
x_587 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(x_584);
x_544 = x_587;
x_545 = x_581;
goto lbl_546;
}
}
}
else
{
obj* x_588; obj* x_590; obj* x_592; obj* x_594; obj* x_596; obj* x_598; obj* x_600; obj* x_602; obj* x_604; obj* x_608; obj* x_609; obj* x_610; obj* x_612; obj* x_614; obj* x_616; obj* x_618; obj* x_621; obj* x_622; obj* x_624; obj* x_626; obj* x_628; obj* x_630; obj* x_632; obj* x_635; obj* x_636; obj* x_638; 
x_588 = lean::cnstr_get(x_501, 0);
lean::inc(x_588);
x_590 = lean::cnstr_get(x_540, 0);
lean::inc(x_590);
x_592 = lean::cnstr_get(x_540, 1);
lean::inc(x_592);
x_594 = lean::cnstr_get(x_540, 2);
lean::inc(x_594);
x_596 = lean::cnstr_get(x_540, 3);
lean::inc(x_596);
x_598 = lean::cnstr_get(x_540, 4);
lean::inc(x_598);
x_600 = lean::cnstr_get(x_598, 0);
lean::inc(x_600);
x_602 = lean::cnstr_get(x_598, 1);
lean::inc(x_602);
x_604 = lean::cnstr_get(x_588, 1);
lean::inc(x_604);
lean::dec(x_588);
lean::inc(x_604);
x_608 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(x_604);
x_609 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(x_602, x_608);
x_610 = lean::cnstr_get(x_598, 2);
lean::inc(x_610);
x_612 = lean::cnstr_get(x_598, 3);
lean::inc(x_612);
x_614 = lean::cnstr_get(x_598, 4);
lean::inc(x_614);
x_616 = lean::cnstr_get(x_598, 5);
lean::inc(x_616);
x_618 = lean::cnstr_get(x_598, 6);
lean::inc(x_618);
lean::dec(x_598);
x_621 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_621, 0, x_600);
lean::cnstr_set(x_621, 1, x_609);
lean::cnstr_set(x_621, 2, x_610);
lean::cnstr_set(x_621, 3, x_612);
lean::cnstr_set(x_621, 4, x_614);
lean::cnstr_set(x_621, 5, x_616);
lean::cnstr_set(x_621, 6, x_618);
x_622 = lean::cnstr_get(x_540, 5);
lean::inc(x_622);
x_624 = lean::cnstr_get(x_540, 6);
lean::inc(x_624);
x_626 = lean::cnstr_get(x_540, 7);
lean::inc(x_626);
x_628 = lean::cnstr_get(x_540, 8);
lean::inc(x_628);
x_630 = lean::cnstr_get(x_540, 9);
lean::inc(x_630);
x_632 = lean::cnstr_get(x_540, 10);
lean::inc(x_632);
lean::dec(x_540);
x_635 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_635, 0, x_590);
lean::cnstr_set(x_635, 1, x_592);
lean::cnstr_set(x_635, 2, x_594);
lean::cnstr_set(x_635, 3, x_596);
lean::cnstr_set(x_635, 4, x_621);
lean::cnstr_set(x_635, 5, x_622);
lean::cnstr_set(x_635, 6, x_624);
lean::cnstr_set(x_635, 7, x_626);
lean::cnstr_set(x_635, 8, x_628);
lean::cnstr_set(x_635, 9, x_630);
lean::cnstr_set(x_635, 10, x_632);
x_636 = l_lean_expander_get__opt__type___main(x_512);
lean::dec(x_512);
x_638 = l_lean_elaborator_to__pexpr___main(x_636, x_1, x_635);
lean::dec(x_635);
if (lean::obj_tag(x_501) == 0)
{
lean::dec(x_604);
if (lean::obj_tag(x_638) == 0)
{
obj* x_649; obj* x_651; obj* x_652; 
lean::dec(x_538);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_515);
lean::dec(x_503);
lean::dec(x_507);
lean::dec(x_505);
lean::dec(x_509);
x_649 = lean::cnstr_get(x_638, 0);
if (lean::is_exclusive(x_638)) {
 x_651 = x_638;
} else {
 lean::inc(x_649);
 lean::dec(x_638);
 x_651 = lean::box(0);
}
if (lean::is_scalar(x_651)) {
 x_652 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_652 = x_651;
}
lean::cnstr_set(x_652, 0, x_649);
x_4 = x_652;
goto lbl_5;
}
else
{
obj* x_653; 
x_653 = lean::cnstr_get(x_638, 0);
lean::inc(x_653);
lean::dec(x_638);
x_544 = x_543;
x_545 = x_653;
goto lbl_546;
}
}
else
{
lean::dec(x_501);
if (lean::obj_tag(x_638) == 0)
{
obj* x_666; obj* x_668; obj* x_669; 
lean::dec(x_538);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_515);
lean::dec(x_503);
lean::dec(x_507);
lean::dec(x_505);
lean::dec(x_509);
lean::dec(x_604);
x_666 = lean::cnstr_get(x_638, 0);
if (lean::is_exclusive(x_638)) {
 x_668 = x_638;
} else {
 lean::inc(x_666);
 lean::dec(x_638);
 x_668 = lean::box(0);
}
if (lean::is_scalar(x_668)) {
 x_669 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_669 = x_668;
}
lean::cnstr_set(x_669, 0, x_666);
x_4 = x_669;
goto lbl_5;
}
else
{
obj* x_670; obj* x_673; 
x_670 = lean::cnstr_get(x_638, 0);
lean::inc(x_670);
lean::dec(x_638);
x_673 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(x_604);
x_544 = x_673;
x_545 = x_670;
goto lbl_546;
}
}
}
lbl_546:
{
obj* x_674; obj* x_676; obj* x_679; 
x_674 = lean::cnstr_get(x_545, 0);
lean::inc(x_674);
x_676 = lean::cnstr_get(x_545, 1);
lean::inc(x_676);
lean::dec(x_545);
x_679 = l_lean_elaborator_simple__binders__to__pexpr(x_515, x_1, x_676);
lean::dec(x_676);
if (lean::obj_tag(x_679) == 0)
{
obj* x_690; obj* x_692; obj* x_693; 
lean::dec(x_544);
lean::dec(x_538);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_503);
lean::dec(x_507);
lean::dec(x_505);
lean::dec(x_509);
lean::dec(x_674);
x_690 = lean::cnstr_get(x_679, 0);
if (lean::is_exclusive(x_679)) {
 x_692 = x_679;
} else {
 lean::inc(x_690);
 lean::dec(x_679);
 x_692 = lean::box(0);
}
if (lean::is_scalar(x_692)) {
 x_693 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_693 = x_692;
}
lean::cnstr_set(x_693, 0, x_690);
x_4 = x_693;
goto lbl_5;
}
else
{
obj* x_694; obj* x_697; obj* x_699; obj* x_702; obj* x_703; obj* x_706; obj* x_707; uint8 x_708; obj* x_710; obj* x_711; 
x_694 = lean::cnstr_get(x_679, 0);
lean::inc(x_694);
lean::dec(x_679);
x_697 = lean::cnstr_get(x_694, 0);
lean::inc(x_697);
x_699 = lean::cnstr_get(x_694, 1);
lean::inc(x_699);
lean::dec(x_694);
x_702 = l_lean_elaborator_names__to__pexpr(x_544);
x_703 = lean::cnstr_get(x_503, 0);
lean::inc(x_703);
lean::dec(x_503);
x_706 = l_lean_elaborator_mangle__ident(x_703);
x_707 = l_lean_elaborator_dummy;
x_708 = 0;
lean::inc(x_706);
x_710 = lean_expr_local(x_706, x_706, x_707, x_708);
if (lean::obj_tag(x_505) == 0)
{
x_711 = x_543;
goto lbl_712;
}
else
{
obj* x_713; obj* x_716; 
x_713 = lean::cnstr_get(x_505, 0);
lean::inc(x_713);
lean::dec(x_505);
x_716 = lean::cnstr_get(x_713, 1);
lean::inc(x_716);
lean::dec(x_713);
x_711 = x_716;
goto lbl_712;
}
lbl_712:
{
obj* x_719; 
x_719 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_711, x_1, x_699);
lean::dec(x_699);
if (lean::obj_tag(x_719) == 0)
{
obj* x_730; obj* x_732; obj* x_733; 
lean::dec(x_710);
lean::dec(x_538);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_507);
lean::dec(x_509);
lean::dec(x_674);
lean::dec(x_702);
lean::dec(x_697);
x_730 = lean::cnstr_get(x_719, 0);
if (lean::is_exclusive(x_719)) {
 x_732 = x_719;
} else {
 lean::inc(x_730);
 lean::dec(x_719);
 x_732 = lean::box(0);
}
if (lean::is_scalar(x_732)) {
 x_733 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_733 = x_732;
}
lean::cnstr_set(x_733, 0, x_730);
x_4 = x_733;
goto lbl_5;
}
else
{
obj* x_734; obj* x_737; obj* x_739; obj* x_742; obj* x_743; obj* x_744; obj* x_746; 
x_734 = lean::cnstr_get(x_719, 0);
lean::inc(x_734);
lean::dec(x_719);
x_737 = lean::cnstr_get(x_734, 0);
lean::inc(x_737);
x_739 = lean::cnstr_get(x_734, 1);
lean::inc(x_739);
lean::dec(x_734);
x_742 = l_lean_elaborator_mk__eqns___closed__1;
x_743 = l_lean_expr_mk__capp(x_742, x_737);
x_744 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_509, x_1, x_739);
lean::dec(x_739);
if (lean::obj_tag(x_507) == 0)
{
obj* x_748; 
x_748 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7;
x_746 = x_748;
goto lbl_747;
}
else
{
obj* x_749; obj* x_751; obj* x_754; 
x_749 = lean::cnstr_get(x_507, 0);
lean::inc(x_749);
x_751 = lean::cnstr_get(x_749, 0);
lean::inc(x_751);
lean::dec(x_749);
x_754 = l_lean_elaborator_mangle__ident(x_751);
x_746 = x_754;
goto lbl_747;
}
lbl_747:
{
obj* x_756; 
lean::inc(x_746);
x_756 = lean_expr_local(x_746, x_746, x_707, x_708);
if (lean::obj_tag(x_507) == 0)
{
if (lean::obj_tag(x_744) == 0)
{
obj* x_766; obj* x_768; obj* x_769; 
lean::dec(x_710);
lean::dec(x_743);
lean::dec(x_538);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_756);
lean::dec(x_674);
lean::dec(x_702);
lean::dec(x_697);
x_766 = lean::cnstr_get(x_744, 0);
if (lean::is_exclusive(x_744)) {
 x_768 = x_744;
} else {
 lean::inc(x_766);
 lean::dec(x_744);
 x_768 = lean::box(0);
}
if (lean::is_scalar(x_768)) {
 x_769 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_769 = x_768;
}
lean::cnstr_set(x_769, 0, x_766);
x_4 = x_769;
goto lbl_5;
}
else
{
obj* x_770; obj* x_773; obj* x_775; obj* x_778; obj* x_779; obj* x_780; obj* x_781; obj* x_782; obj* x_783; obj* x_784; obj* x_785; obj* x_786; obj* x_787; obj* x_788; obj* x_789; obj* x_790; obj* x_791; obj* x_792; 
x_770 = lean::cnstr_get(x_744, 0);
lean::inc(x_770);
lean::dec(x_744);
x_773 = lean::cnstr_get(x_770, 0);
lean::inc(x_773);
x_775 = lean::cnstr_get(x_770, 1);
lean::inc(x_775);
lean::dec(x_770);
x_778 = l_lean_expr_mk__capp(x_742, x_773);
x_779 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_779, 0, x_778);
lean::cnstr_set(x_779, 1, x_543);
x_780 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5;
x_781 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_781, 0, x_780);
lean::cnstr_set(x_781, 1, x_779);
x_782 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_782, 0, x_756);
lean::cnstr_set(x_782, 1, x_781);
x_783 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_783, 0, x_674);
lean::cnstr_set(x_783, 1, x_782);
x_784 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_784, 0, x_743);
lean::cnstr_set(x_784, 1, x_783);
x_785 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_785, 0, x_697);
lean::cnstr_set(x_785, 1, x_784);
x_786 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_786, 0, x_710);
lean::cnstr_set(x_786, 1, x_785);
x_787 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_787, 0, x_702);
lean::cnstr_set(x_787, 1, x_786);
x_788 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_788, 0, x_538);
lean::cnstr_set(x_788, 1, x_787);
x_789 = l_lean_expr_mk__capp(x_742, x_788);
x_790 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
x_791 = lean_expr_mk_mdata(x_790, x_789);
x_792 = l_lean_elaborator_old__elab__command(x_0, x_791, x_1, x_775);
lean::dec(x_0);
x_4 = x_792;
goto lbl_5;
}
}
else
{
if (lean::obj_tag(x_744) == 0)
{
obj* x_804; obj* x_806; obj* x_807; 
lean::dec(x_710);
lean::dec(x_743);
lean::dec(x_538);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_756);
lean::dec(x_507);
lean::dec(x_674);
lean::dec(x_702);
lean::dec(x_697);
x_804 = lean::cnstr_get(x_744, 0);
if (lean::is_exclusive(x_744)) {
 x_806 = x_744;
} else {
 lean::inc(x_804);
 lean::dec(x_744);
 x_806 = lean::box(0);
}
if (lean::is_scalar(x_806)) {
 x_807 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_807 = x_806;
}
lean::cnstr_set(x_807, 0, x_804);
x_4 = x_807;
goto lbl_5;
}
else
{
obj* x_808; obj* x_811; obj* x_814; obj* x_816; obj* x_819; obj* x_822; obj* x_824; obj* x_825; obj* x_826; obj* x_827; obj* x_828; obj* x_829; obj* x_830; obj* x_831; obj* x_832; obj* x_833; obj* x_834; obj* x_835; obj* x_836; obj* x_837; 
x_808 = lean::cnstr_get(x_744, 0);
lean::inc(x_808);
lean::dec(x_744);
x_811 = lean::cnstr_get(x_507, 0);
lean::inc(x_811);
lean::dec(x_507);
x_814 = lean::cnstr_get(x_808, 0);
lean::inc(x_814);
x_816 = lean::cnstr_get(x_808, 1);
lean::inc(x_816);
lean::dec(x_808);
x_819 = lean::cnstr_get(x_811, 1);
lean::inc(x_819);
lean::dec(x_811);
x_822 = l_lean_elaborator_infer__mod__to__pexpr(x_819);
lean::dec(x_819);
x_824 = l_lean_expr_mk__capp(x_742, x_814);
x_825 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_825, 0, x_824);
lean::cnstr_set(x_825, 1, x_543);
x_826 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_826, 0, x_822);
lean::cnstr_set(x_826, 1, x_825);
x_827 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_827, 0, x_756);
lean::cnstr_set(x_827, 1, x_826);
x_828 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_828, 0, x_674);
lean::cnstr_set(x_828, 1, x_827);
x_829 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_829, 0, x_743);
lean::cnstr_set(x_829, 1, x_828);
x_830 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_830, 0, x_697);
lean::cnstr_set(x_830, 1, x_829);
x_831 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_831, 0, x_710);
lean::cnstr_set(x_831, 1, x_830);
x_832 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_832, 0, x_702);
lean::cnstr_set(x_832, 1, x_831);
x_833 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_833, 0, x_538);
lean::cnstr_set(x_833, 1, x_832);
x_834 = l_lean_expr_mk__capp(x_742, x_833);
x_835 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
x_836 = lean_expr_mk_mdata(x_835, x_834);
x_837 = l_lean_elaborator_old__elab__command(x_0, x_836, x_1, x_816);
lean::dec(x_0);
x_4 = x_837;
goto lbl_5;
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
obj* x_842; obj* x_843; 
lean::dec(x_11);
lean::dec(x_486);
lean::dec(x_483);
x_842 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
x_843 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_842, x_1, x_2);
lean::dec(x_1);
lean::dec(x_0);
x_4 = x_843;
goto lbl_5;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_846; obj* x_848; obj* x_849; 
x_846 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_848 = x_4;
} else {
 lean::inc(x_846);
 lean::dec(x_4);
 x_848 = lean::box(0);
}
if (lean::is_scalar(x_848)) {
 x_849 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_849 = x_848;
}
lean::cnstr_set(x_849, 0, x_846);
return x_849;
}
else
{
obj* x_850; obj* x_852; obj* x_853; obj* x_855; obj* x_856; obj* x_858; obj* x_860; obj* x_862; obj* x_864; obj* x_866; obj* x_868; obj* x_870; obj* x_872; obj* x_874; obj* x_878; obj* x_879; obj* x_880; obj* x_881; 
x_850 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_852 = x_4;
} else {
 lean::inc(x_850);
 lean::dec(x_4);
 x_852 = lean::box(0);
}
x_853 = lean::cnstr_get(x_850, 1);
if (lean::is_exclusive(x_850)) {
 lean::cnstr_release(x_850, 0);
 x_855 = x_850;
} else {
 lean::inc(x_853);
 lean::dec(x_850);
 x_855 = lean::box(0);
}
x_856 = lean::cnstr_get(x_853, 0);
lean::inc(x_856);
x_858 = lean::cnstr_get(x_853, 1);
lean::inc(x_858);
x_860 = lean::cnstr_get(x_853, 2);
lean::inc(x_860);
x_862 = lean::cnstr_get(x_853, 3);
lean::inc(x_862);
x_864 = lean::cnstr_get(x_853, 5);
lean::inc(x_864);
x_866 = lean::cnstr_get(x_853, 6);
lean::inc(x_866);
x_868 = lean::cnstr_get(x_853, 7);
lean::inc(x_868);
x_870 = lean::cnstr_get(x_853, 8);
lean::inc(x_870);
x_872 = lean::cnstr_get(x_853, 9);
lean::inc(x_872);
x_874 = lean::cnstr_get(x_853, 10);
lean::inc(x_874);
lean::dec(x_853);
lean::inc(x_3);
x_878 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_878, 0, x_856);
lean::cnstr_set(x_878, 1, x_858);
lean::cnstr_set(x_878, 2, x_860);
lean::cnstr_set(x_878, 3, x_862);
lean::cnstr_set(x_878, 4, x_3);
lean::cnstr_set(x_878, 5, x_864);
lean::cnstr_set(x_878, 6, x_866);
lean::cnstr_set(x_878, 7, x_868);
lean::cnstr_set(x_878, 8, x_870);
lean::cnstr_set(x_878, 9, x_872);
lean::cnstr_set(x_878, 10, x_874);
x_879 = lean::box(0);
if (lean::is_scalar(x_855)) {
 x_880 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_880 = x_855;
}
lean::cnstr_set(x_880, 0, x_879);
lean::cnstr_set(x_880, 1, x_878);
if (lean::is_scalar(x_852)) {
 x_881 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_881 = x_852;
}
lean::cnstr_set(x_881, 0, x_880);
return x_881;
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
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_declaration_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_declaration_elaborate(x_0, x_1, x_2);
lean::dec(x_2);
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
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_2, x_1);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
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
lean::inc(x_2);
lean::inc(x_11);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_2);
x_17 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(x_9, x_1, x_16);
lean::dec(x_16);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_11, x_19);
lean::dec(x_11);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_8);
lean::cnstr_set(x_22, 1, x_17);
lean::cnstr_set(x_22, 2, x_20);
return x_22;
}
}
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; uint8 x_26; 
x_5 = lean::cnstr_get(x_0, 0);
x_7 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_9 = x_0;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_0);
 x_9 = lean::box(0);
}
x_12 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_5);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_13, 0);
x_20 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 lean::cnstr_set(x_13, 1, lean::box(0));
 x_22 = x_13;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
x_25 = l_lean_expander_binding__annotation__update;
x_26 = l_lean_parser_syntax_is__of__kind___main(x_25, x_20);
lean::dec(x_20);
if (x_26 == 0)
{
uint8 x_30; obj* x_31; obj* x_32; 
lean::dec(x_15);
lean::dec(x_18);
x_30 = 1;
x_31 = lean::box(x_30);
if (lean::is_scalar(x_22)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_22;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_2);
x_10 = x_32;
goto lbl_11;
}
else
{
obj* x_34; 
lean::dec(x_22);
x_34 = lean::box(0);
x_23 = x_34;
goto lbl_24;
}
lbl_11:
{
obj* x_35; obj* x_37; obj* x_40; 
x_35 = lean::cnstr_get(x_10, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_10, 1);
lean::inc(x_37);
lean::dec(x_10);
x_40 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_7, x_1, x_37);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_5);
lean::dec(x_9);
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
obj* x_48; obj* x_50; uint8 x_51; 
x_48 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_set(x_40, 0, lean::box(0));
 x_50 = x_40;
} else {
 lean::inc(x_48);
 lean::dec(x_40);
 x_50 = lean::box(0);
}
x_51 = lean::unbox(x_35);
if (x_51 == 0)
{
obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_5);
lean::dec(x_9);
x_54 = lean::cnstr_get(x_48, 0);
x_56 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 x_58 = x_48;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_48);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_54);
lean::cnstr_set(x_59, 1, x_56);
if (lean::is_scalar(x_50)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_50;
}
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
else
{
obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_61 = lean::cnstr_get(x_48, 0);
x_63 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 x_65 = x_48;
} else {
 lean::inc(x_61);
 lean::inc(x_63);
 lean::dec(x_48);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_9)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_9;
}
lean::cnstr_set(x_66, 0, x_5);
lean::cnstr_set(x_66, 1, x_61);
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_63);
if (lean::is_scalar(x_50)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_50;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
lbl_24:
{
obj* x_70; obj* x_71; obj* x_73; obj* x_75; 
lean::dec(x_23);
x_70 = l_lean_elaborator_mangle__ident(x_18);
x_71 = lean::cnstr_get(x_2, 4);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_71, 2);
lean::inc(x_73);
x_75 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_73, x_70);
if (lean::obj_tag(x_75) == 0)
{
obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_15);
lean::dec(x_73);
lean::dec(x_71);
x_79 = lean::box(0);
x_80 = l_lean_name_to__string___closed__1;
lean::inc(x_70);
x_82 = l_lean_name_to__string__with__sep___main(x_80, x_70);
x_83 = l_lean_parser_substring_of__string(x_82);
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_85, 0, x_79);
lean::cnstr_set(x_85, 1, x_83);
lean::cnstr_set(x_85, 2, x_70);
lean::cnstr_set(x_85, 3, x_84);
lean::cnstr_set(x_85, 4, x_84);
x_86 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_86, 0, x_85);
x_87 = l_string_join___closed__1;
x_88 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_86, x_87, x_1, x_2);
lean::dec(x_2);
lean::dec(x_86);
if (lean::obj_tag(x_88) == 0)
{
obj* x_94; obj* x_96; obj* x_97; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_7);
x_94 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
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
obj* x_98; obj* x_101; obj* x_103; uint8 x_104; obj* x_105; obj* x_106; 
x_98 = lean::cnstr_get(x_88, 0);
lean::inc(x_98);
lean::dec(x_88);
x_101 = lean::cnstr_get(x_98, 1);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_103 = x_98;
} else {
 lean::inc(x_101);
 lean::dec(x_98);
 x_103 = lean::box(0);
}
x_104 = 0;
x_105 = lean::box(x_104);
if (lean::is_scalar(x_103)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_103;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_101);
x_10 = x_106;
goto lbl_11;
}
}
else
{
obj* x_107; obj* x_110; obj* x_112; obj* x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_130; uint8 x_131; obj* x_132; obj* x_133; obj* x_136; obj* x_138; obj* x_140; obj* x_142; obj* x_145; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_159; uint8 x_160; obj* x_161; obj* x_162; 
x_107 = lean::cnstr_get(x_75, 0);
lean::inc(x_107);
lean::dec(x_75);
x_110 = lean::cnstr_get(x_107, 1);
if (lean::is_exclusive(x_107)) {
 lean::cnstr_release(x_107, 0);
 x_112 = x_107;
} else {
 lean::inc(x_110);
 lean::dec(x_107);
 x_112 = lean::box(0);
}
x_113 = lean::cnstr_get(x_2, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_2, 1);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_2, 2);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_2, 3);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_71, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_71, 1);
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
x_133 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(x_73, x_70, x_132);
lean::dec(x_132);
lean::dec(x_70);
x_136 = lean::cnstr_get(x_71, 3);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_71, 4);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_71, 5);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_71, 6);
lean::inc(x_142);
lean::dec(x_71);
x_145 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_145, 0, x_121);
lean::cnstr_set(x_145, 1, x_123);
lean::cnstr_set(x_145, 2, x_133);
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
lean::cnstr_set(x_159, 0, x_113);
lean::cnstr_set(x_159, 1, x_115);
lean::cnstr_set(x_159, 2, x_117);
lean::cnstr_set(x_159, 3, x_119);
lean::cnstr_set(x_159, 4, x_145);
lean::cnstr_set(x_159, 5, x_146);
lean::cnstr_set(x_159, 6, x_148);
lean::cnstr_set(x_159, 7, x_150);
lean::cnstr_set(x_159, 8, x_152);
lean::cnstr_set(x_159, 9, x_154);
lean::cnstr_set(x_159, 10, x_156);
x_160 = 0;
x_161 = lean::box(x_160);
if (lean::is_scalar(x_112)) {
 x_162 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_162 = x_112;
}
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_159);
x_10 = x_162;
goto lbl_11;
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
lean::dec(x_5);
lean::dec(x_3);
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
obj* x_13; obj* x_14; 
lean::dec(x_9);
x_13 = l_lean_elaborator_variables_elaborate___closed__1;
x_14 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_13, x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_0);
x_18 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_20 = x_14;
} else {
 lean::inc(x_18);
 lean::dec(x_14);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
lean::dec(x_14);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_lean_elaborator_simple__binders__to__pexpr(x_25, x_1, x_27);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_1);
lean::dec(x_0);
x_34 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_36 = x_30;
} else {
 lean::inc(x_34);
 lean::dec(x_30);
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
obj* x_38; obj* x_41; obj* x_43; obj* x_46; obj* x_47; obj* x_48; 
x_38 = lean::cnstr_get(x_30, 0);
lean::inc(x_38);
lean::dec(x_30);
x_41 = lean::cnstr_get(x_38, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 1);
lean::inc(x_43);
lean::dec(x_38);
x_46 = l_lean_elaborator_variables_elaborate___closed__2;
x_47 = lean_expr_mk_mdata(x_46, x_41);
x_48 = l_lean_elaborator_old__elab__command(x_0, x_47, x_1, x_43);
lean::dec(x_0);
return x_48;
}
}
}
else
{
obj* x_50; obj* x_53; 
x_50 = lean::cnstr_get(x_9, 0);
lean::inc(x_50);
lean::dec(x_9);
x_53 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_50, x_1, x_2);
if (lean::obj_tag(x_53) == 0)
{
obj* x_56; obj* x_58; obj* x_59; 
lean::dec(x_1);
lean::dec(x_0);
x_56 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_58 = x_53;
} else {
 lean::inc(x_56);
 lean::dec(x_53);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_56);
return x_59;
}
else
{
obj* x_60; obj* x_63; obj* x_65; obj* x_68; 
x_60 = lean::cnstr_get(x_53, 0);
lean::inc(x_60);
lean::dec(x_53);
x_63 = lean::cnstr_get(x_60, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_60, 1);
lean::inc(x_65);
lean::dec(x_60);
x_68 = l_lean_elaborator_simple__binders__to__pexpr(x_63, x_1, x_65);
lean::dec(x_65);
if (lean::obj_tag(x_68) == 0)
{
obj* x_72; obj* x_74; obj* x_75; 
lean::dec(x_1);
lean::dec(x_0);
x_72 = lean::cnstr_get(x_68, 0);
if (lean::is_exclusive(x_68)) {
 x_74 = x_68;
} else {
 lean::inc(x_72);
 lean::dec(x_68);
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
obj* x_76; obj* x_79; obj* x_81; obj* x_84; obj* x_85; obj* x_86; 
x_76 = lean::cnstr_get(x_68, 0);
lean::inc(x_76);
lean::dec(x_68);
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_76, 1);
lean::inc(x_81);
lean::dec(x_76);
x_84 = l_lean_elaborator_variables_elaborate___closed__2;
x_85 = lean_expr_mk_mdata(x_84, x_79);
x_86 = l_lean_elaborator_old__elab__command(x_0, x_85, x_1, x_81);
lean::dec(x_0);
return x_86;
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
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
lean::dec(x_7);
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
obj* l_rbmap_insert___main___at_lean_elaborator_include_elaborate___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_elaborator_include_elaborate___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
lean::dec(x_0);
return x_13;
}
else
{
obj* x_16; 
lean::dec(x_9);
x_16 = lean::cnstr_get(x_8, 1);
lean::inc(x_16);
lean::dec(x_8);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_0);
x_20 = lean::box(0);
lean::inc(x_2);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_16);
x_25 = l_lean_elaborator_module_header_elaborate___closed__1;
x_26 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_25, x_1, x_2);
lean::dec(x_0);
return x_26;
}
}
}
}
obj* l_lean_elaborator_module_header_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_module_header_elaborate(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* x_14; obj* x_17; obj* x_20; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; 
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
lean::dec(x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_25);
lean::cnstr_set(x_40, 1, x_38);
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
obj* x_2; obj* x_3; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
}
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg___boxed), 1, 0);
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
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
obj* x_101; obj* x_103; obj* x_104; obj* x_106; obj* x_107; 
x_101 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_103 = x_50;
} else {
 lean::inc(x_101);
 lean::dec(x_50);
 x_103 = lean::box(0);
}
x_104 = l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(x_101);
lean::dec(x_101);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_9);
lean::cnstr_set(x_106, 1, x_104);
if (lean::is_scalar(x_103)) {
 x_107 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_107 = x_103;
}
lean::cnstr_set(x_107, 0, x_106);
x_7 = x_107;
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
obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_71; obj* x_73; obj* x_75; obj* x_78; obj* x_79; 
x_61 = lean::cnstr_get(x_2, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_2, 1);
lean::inc(x_63);
x_65 = lean::box(0);
x_66 = lean_name_mk_string(x_65, x_21);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1___boxed), 7, 2);
lean::closure_set(x_67, 0, x_0);
lean::closure_set(x_67, 1, x_54);
x_68 = l_lean_parser_token__map_insert___rarg(x_63, x_66, x_67);
lean::dec(x_67);
lean::dec(x_66);
x_71 = lean::cnstr_get(x_2, 2);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_2, 3);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_2, 4);
lean::inc(x_75);
lean::dec(x_2);
x_78 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_78, 0, x_61);
lean::cnstr_set(x_78, 1, x_68);
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
obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_96; obj* x_98; obj* x_101; obj* x_102; 
lean::dec(x_58);
x_81 = lean::cnstr_get(x_2, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_2, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_2, 2);
lean::inc(x_85);
x_87 = lean::box(0);
x_88 = lean_name_mk_string(x_87, x_21);
x_89 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(x_54);
x_90 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3___boxed), 8, 2);
lean::closure_set(x_92, 0, x_0);
lean::closure_set(x_92, 1, x_91);
x_93 = l_lean_parser_token__map_insert___rarg(x_85, x_88, x_92);
lean::dec(x_92);
lean::dec(x_88);
x_96 = lean::cnstr_get(x_2, 3);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_2, 4);
lean::inc(x_98);
lean::dec(x_2);
x_101 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_101, 0, x_81);
lean::cnstr_set(x_101, 1, x_83);
lean::cnstr_set(x_101, 2, x_93);
lean::cnstr_set(x_101, 3, x_96);
lean::cnstr_set(x_101, 4, x_98);
if (lean::is_scalar(x_20)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_20;
}
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
else
{
obj* x_104; 
lean::dec(x_55);
x_104 = lean::cnstr_get(x_3, 0);
lean::inc(x_104);
lean::dec(x_3);
if (lean::obj_tag(x_104) == 0)
{
obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_121; obj* x_124; obj* x_125; 
x_107 = lean::cnstr_get(x_2, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_2, 1);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_2, 2);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_2, 3);
lean::inc(x_113);
x_115 = lean::box(0);
x_116 = lean_name_mk_string(x_115, x_21);
x_117 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1___boxed), 7, 2);
lean::closure_set(x_117, 0, x_0);
lean::closure_set(x_117, 1, x_54);
x_118 = l_lean_parser_token__map_insert___rarg(x_113, x_116, x_117);
lean::dec(x_117);
lean::dec(x_116);
x_121 = lean::cnstr_get(x_2, 4);
lean::inc(x_121);
lean::dec(x_2);
x_124 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_124, 0, x_107);
lean::cnstr_set(x_124, 1, x_109);
lean::cnstr_set(x_124, 2, x_111);
lean::cnstr_set(x_124, 3, x_118);
lean::cnstr_set(x_124, 4, x_121);
if (lean::is_scalar(x_20)) {
 x_125 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_125 = x_20;
}
lean::cnstr_set(x_125, 0, x_124);
return x_125;
}
else
{
obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_147; obj* x_148; 
lean::dec(x_104);
x_127 = lean::cnstr_get(x_2, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_2, 1);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_2, 2);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_2, 3);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_2, 4);
lean::inc(x_135);
lean::dec(x_2);
x_138 = lean::box(0);
x_139 = lean_name_mk_string(x_138, x_21);
x_140 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(x_54);
x_141 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_140);
x_143 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3___boxed), 8, 2);
lean::closure_set(x_143, 0, x_0);
lean::closure_set(x_143, 1, x_142);
x_144 = l_lean_parser_token__map_insert___rarg(x_135, x_139, x_143);
lean::dec(x_143);
lean::dec(x_139);
x_147 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_147, 0, x_127);
lean::cnstr_set(x_147, 1, x_129);
lean::cnstr_set(x_147, 2, x_131);
lean::cnstr_set(x_147, 3, x_133);
lean::cnstr_set(x_147, 4, x_144);
if (lean::is_scalar(x_20)) {
 x_148 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_148 = x_20;
}
lean::cnstr_set(x_148, 0, x_147);
return x_148;
}
}
}
}
}
}
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_13; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
x_13 = l_lean_elaborator_command__parser__config_register__notation__tokens(x_11, x_0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_17; obj* x_18; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
lean::dec(x_13);
x_17 = l_lean_parser_command_reserve__notation_has__view;
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
lean::dec(x_17);
x_21 = lean::apply_1(x_18, x_6);
x_22 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_21, x_14, x_2, x_3);
lean::dec(x_3);
lean::dec(x_14);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_8);
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
obj* x_31; obj* x_34; obj* x_36; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
lean::dec(x_22);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::dec(x_31);
x_0 = x_34;
x_1 = x_8;
x_3 = x_36;
goto _start;
}
}
else
{
obj* x_41; 
lean::dec(x_6);
x_41 = lean::cnstr_get(x_13, 0);
lean::inc(x_41);
lean::dec(x_13);
x_0 = x_41;
x_1 = x_8;
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
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_15; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 2);
lean::inc(x_13);
x_15 = l_lean_elaborator_command__parser__config_register__notation__tokens(x_13, x_0);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_20; obj* x_21; obj* x_24; obj* x_25; 
lean::dec(x_6);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
lean::dec(x_15);
x_20 = l_lean_parser_command_notation_has__view;
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
x_24 = lean::apply_1(x_21, x_11);
x_25 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_24, x_17, x_2, x_3);
lean::dec(x_3);
lean::dec(x_17);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_8);
x_30 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_32 = x_25;
} else {
 lean::inc(x_30);
 lean::dec(x_25);
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
x_34 = lean::cnstr_get(x_25, 0);
lean::inc(x_34);
lean::dec(x_25);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_0 = x_37;
x_1 = x_8;
x_3 = x_39;
goto _start;
}
}
else
{
obj* x_43; obj* x_46; obj* x_50; 
x_43 = lean::cnstr_get(x_15, 0);
lean::inc(x_43);
lean::dec(x_15);
x_46 = lean::cnstr_get(x_6, 0);
lean::inc(x_46);
lean::dec(x_6);
lean::inc(x_11);
x_50 = l_lean_elaborator_command__parser__config_register__notation__parser(x_46, x_11, x_43);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_54; obj* x_55; obj* x_58; obj* x_59; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
lean::dec(x_50);
x_54 = l_lean_parser_command_notation_has__view;
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
lean::dec(x_54);
x_58 = lean::apply_1(x_55, x_11);
x_59 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_58, x_51, x_2, x_3);
lean::dec(x_3);
lean::dec(x_51);
lean::dec(x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_8);
x_64 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 x_66 = x_59;
} else {
 lean::inc(x_64);
 lean::dec(x_59);
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
obj* x_68; obj* x_71; obj* x_73; 
x_68 = lean::cnstr_get(x_59, 0);
lean::inc(x_68);
lean::dec(x_59);
x_71 = lean::cnstr_get(x_68, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
lean::dec(x_68);
x_0 = x_71;
x_1 = x_8;
x_3 = x_73;
goto _start;
}
}
else
{
obj* x_78; 
lean::dec(x_11);
x_78 = lean::cnstr_get(x_50, 0);
lean::inc(x_78);
lean::dec(x_50);
x_0 = x_78;
x_1 = x_8;
goto _start;
}
}
}
}
}
obj* l_lean_elaborator_update__parser__config(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::inc(x_1);
lean::inc(x_6);
x_10 = l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(x_4, x_6, x_0, x_1);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_17 = x_10;
} else {
 lean::inc(x_15);
 lean::dec(x_10);
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
obj* x_19; obj* x_22; obj* x_24; obj* x_27; obj* x_29; obj* x_31; obj* x_34; obj* x_35; 
x_19 = lean::cnstr_get(x_10, 0);
lean::inc(x_19);
lean::dec(x_10);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::cnstr_get(x_1, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_1, 4);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_29, 0);
lean::inc(x_31);
lean::inc(x_27);
x_34 = l_list_append___rarg(x_27, x_31);
x_35 = l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(x_22, x_34, x_0, x_24);
lean::dec(x_0);
if (lean::obj_tag(x_35) == 0)
{
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_29);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_27);
x_42 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_44 = x_35;
} else {
 lean::inc(x_42);
 lean::dec(x_35);
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
x_46 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_48 = x_35;
} else {
 lean::inc(x_46);
 lean::dec(x_35);
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
lean::cnstr_set(x_71, 1, x_27);
lean::cnstr_set(x_71, 2, x_52);
lean::cnstr_set(x_71, 3, x_54);
lean::cnstr_set(x_71, 4, x_29);
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
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_2 = x_1;
} else {
 lean::dec(x_1);
 x_2 = lean::box(0);
}
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_6 = lean::cnstr_get(x_0, 3);
x_7 = lean::cnstr_get(x_0, 4);
x_8 = lean::cnstr_get(x_0, 6);
x_9 = lean::cnstr_get(x_0, 7);
x_10 = lean::cnstr_get(x_0, 8);
x_11 = lean::cnstr_get(x_0, 9);
x_12 = lean::cnstr_get(x_0, 10);
x_13 = l_lean_message__log_empty;
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_24 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_24, 0, x_3);
lean::cnstr_set(x_24, 1, x_4);
lean::cnstr_set(x_24, 2, x_5);
lean::cnstr_set(x_24, 3, x_6);
lean::cnstr_set(x_24, 4, x_7);
lean::cnstr_set(x_24, 5, x_13);
lean::cnstr_set(x_24, 6, x_8);
lean::cnstr_set(x_24, 7, x_9);
lean::cnstr_set(x_24, 8, x_10);
lean::cnstr_set(x_24, 9, x_11);
lean::cnstr_set(x_24, 10, x_12);
x_25 = lean::box(0);
if (lean::is_scalar(x_2)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_2;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_24);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_28, 0, x_27);
return x_28;
}
}
obj* _init_l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_pure___rarg___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg___lambda__1___boxed), 1, 0);
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__3___boxed), 2, 1);
lean::closure_set(x_7, 0, x_1);
x_8 = l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_10, 0, x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___rarg___lambda__1___boxed), 2, 1);
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_0);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_0);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_lean_elaborator_yield__to__outside___rarg___closed__1;
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_lean_elaborator_yield__to__outside(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_yield__to__outside___rarg___lambda__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_elaborator_yield__to__outside___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_yield__to__outside___rarg(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_40; obj* x_41; 
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
x_21 = lean::cnstr_get(x_2, 2);
x_22 = lean::cnstr_get(x_2, 3);
x_23 = lean::cnstr_get(x_2, 4);
x_24 = lean::cnstr_get(x_2, 5);
x_25 = lean::cnstr_get(x_2, 6);
x_26 = lean::cnstr_get(x_2, 7);
x_27 = lean::cnstr_get(x_2, 8);
x_28 = lean::cnstr_get(x_2, 9);
x_29 = lean::cnstr_get(x_2, 10);
lean::inc(x_29);
lean::inc(x_28);
lean::inc(x_27);
lean::inc(x_26);
lean::inc(x_25);
lean::inc(x_24);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
x_40 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_40, 0, x_19);
lean::cnstr_set(x_40, 1, x_20);
lean::cnstr_set(x_40, 2, x_21);
lean::cnstr_set(x_40, 3, x_22);
lean::cnstr_set(x_40, 4, x_23);
lean::cnstr_set(x_40, 5, x_24);
lean::cnstr_set(x_40, 6, x_25);
lean::cnstr_set(x_40, 7, x_26);
lean::cnstr_set(x_40, 8, x_27);
lean::cnstr_set(x_40, 9, x_28);
lean::cnstr_set(x_40, 10, x_29);
x_41 = l_lean_elaborator_update__parser__config(x_1, x_40);
return x_41;
}
}
obj* l_lean_elaborator_reserve__notation_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_reserve__notation_elaborate(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg___lambda__1___boxed), 2, 0);
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
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 2);
lean::inc(x_12);
x_14 = l_lean_elaborator_postprocess__notation__spec(x_12);
x_15 = lean::cnstr_get(x_0, 3);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 4);
lean::inc(x_17);
lean::dec(x_0);
x_20 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_10);
lean::cnstr_set(x_20, 2, x_14);
lean::cnstr_set(x_20, 3, x_15);
lean::cnstr_set(x_20, 4, x_17);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_2);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
else
{
obj* x_23; 
x_23 = lean::cnstr_get(x_7, 1);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_25; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_25 = lean::cnstr_get(x_7, 0);
lean::inc(x_25);
lean::dec(x_7);
x_28 = lean::cnstr_get(x_0, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 3);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 4);
lean::inc(x_34);
lean::dec(x_0);
x_37 = l_lean_elaborator_postprocess__notation__spec(x_25);
x_38 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set(x_38, 1, x_30);
lean::cnstr_set(x_38, 2, x_37);
lean::cnstr_set(x_38, 3, x_32);
lean::cnstr_set(x_38, 4, x_34);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_2);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
else
{
obj* x_43; obj* x_44; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_7);
lean::dec(x_23);
x_43 = l_lean_parser_command_notation_has__view;
x_44 = lean::cnstr_get(x_43, 1);
lean::inc(x_44);
lean::dec(x_43);
x_47 = lean::apply_1(x_44, x_0);
x_48 = l_lean_elaborator_notation_elaborate__aux___closed__1;
x_49 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_47, x_48, x_1, x_2);
lean::dec(x_2);
lean::dec(x_47);
if (lean::obj_tag(x_49) == 0)
{
obj* x_52; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_49, 0);
if (lean::is_exclusive(x_49)) {
 x_54 = x_49;
} else {
 lean::inc(x_52);
 lean::dec(x_49);
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
x_56 = lean::cnstr_get(x_49, 0);
if (lean::is_exclusive(x_49)) {
 x_58 = x_49;
} else {
 lean::inc(x_56);
 lean::dec(x_49);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_56, 0);
x_61 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
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
obj* l_lean_elaborator_notation_elaborate__aux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_notation_elaborate__aux(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_53; obj* x_54; obj* x_55; 
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
lean::inc(x_0);
lean::inc(x_11);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_11);
lean::cnstr_set(x_18, 1, x_0);
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mk__notation__transformer___boxed), 3, 1);
lean::closure_set(x_20, 0, x_18);
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_13, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_13, 2);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 3);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_13, 4);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_13, 5);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_13, 6);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_13, 7);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_35, 1);
lean::inc(x_39);
lean::dec(x_35);
x_42 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_39, x_11, x_20);
lean::dec(x_20);
lean::dec(x_11);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_37);
lean::cnstr_set(x_45, 1, x_42);
x_46 = lean::cnstr_get(x_13, 8);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_13, 9);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_13, 10);
lean::inc(x_50);
lean::dec(x_13);
x_53 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_53, 0, x_21);
lean::cnstr_set(x_53, 1, x_23);
lean::cnstr_set(x_53, 2, x_25);
lean::cnstr_set(x_53, 3, x_27);
lean::cnstr_set(x_53, 4, x_29);
lean::cnstr_set(x_53, 5, x_31);
lean::cnstr_set(x_53, 6, x_33);
lean::cnstr_set(x_53, 7, x_45);
lean::cnstr_set(x_53, 8, x_46);
lean::cnstr_set(x_53, 9, x_48);
lean::cnstr_set(x_53, 10, x_50);
if (lean::is_scalar(x_15)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_15;
}
lean::cnstr_set(x_54, 0, x_18);
lean::cnstr_set(x_54, 1, x_53);
if (lean::is_scalar(x_10)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_10;
}
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_register__notation__macro___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_register__notation__macro(x_0, x_1, x_2);
lean::dec(x_0);
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
obj* x_61; 
lean::dec(x_8);
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
obj* x_67; obj* x_70; obj* x_72; obj* x_75; 
x_67 = lean::cnstr_get(x_61, 0);
lean::inc(x_67);
lean::dec(x_61);
x_70 = lean::cnstr_get(x_67, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_67, 1);
lean::inc(x_72);
lean::dec(x_67);
x_75 = l_lean_elaborator_register__notation__macro(x_70, x_1, x_72);
if (lean::obj_tag(x_75) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_1);
lean::dec(x_70);
x_78 = lean::cnstr_get(x_75, 0);
if (lean::is_exclusive(x_75)) {
 x_80 = x_75;
} else {
 lean::inc(x_78);
 lean::dec(x_75);
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
obj* x_82; obj* x_85; 
x_82 = lean::cnstr_get(x_75, 0);
lean::inc(x_82);
lean::dec(x_75);
x_85 = lean::cnstr_get(x_70, 0);
lean::inc(x_85);
lean::dec(x_70);
if (lean::obj_tag(x_85) == 0)
{
obj* x_88; obj* x_90; obj* x_93; obj* x_95; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_117; obj* x_118; 
x_88 = lean::cnstr_get(x_82, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_82, 1);
lean::inc(x_90);
lean::dec(x_82);
x_93 = lean::cnstr_get(x_90, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_90, 1);
lean::inc(x_95);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_88);
lean::cnstr_set(x_97, 1, x_95);
x_98 = lean::cnstr_get(x_90, 2);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_90, 3);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_90, 4);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_90, 5);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_90, 6);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_90, 7);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_90, 8);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_90, 9);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_90, 10);
lean::inc(x_114);
lean::dec(x_90);
x_117 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_117, 0, x_93);
lean::cnstr_set(x_117, 1, x_97);
lean::cnstr_set(x_117, 2, x_98);
lean::cnstr_set(x_117, 3, x_100);
lean::cnstr_set(x_117, 4, x_102);
lean::cnstr_set(x_117, 5, x_104);
lean::cnstr_set(x_117, 6, x_106);
lean::cnstr_set(x_117, 7, x_108);
lean::cnstr_set(x_117, 8, x_110);
lean::cnstr_set(x_117, 9, x_112);
lean::cnstr_set(x_117, 10, x_114);
x_118 = l_lean_elaborator_update__parser__config(x_1, x_117);
return x_118;
}
else
{
obj* x_120; obj* x_122; obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_140; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_151; obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_160; obj* x_162; obj* x_165; obj* x_166; 
lean::dec(x_85);
x_120 = lean::cnstr_get(x_82, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_82, 1);
lean::inc(x_122);
lean::dec(x_82);
x_125 = lean::cnstr_get(x_122, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_122, 1);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_122, 2);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_122, 3);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_122, 4);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_133, 0);
lean::inc(x_135);
x_137 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_137, 0, x_120);
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
x_152 = lean::cnstr_get(x_122, 5);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_122, 6);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_122, 7);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_122, 8);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_122, 9);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_122, 10);
lean::inc(x_162);
lean::dec(x_122);
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
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
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
x_17 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_15, x_12);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_0);
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_2, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 3);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 0);
lean::inc(x_27);
lean::inc(x_12);
x_30 = level_mk_param(x_12);
x_31 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_15, x_12, x_30);
lean::dec(x_30);
lean::dec(x_12);
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
lean::cnstr_set(x_45, 0, x_27);
lean::cnstr_set(x_45, 1, x_31);
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
lean::cnstr_set(x_59, 0, x_19);
lean::cnstr_set(x_59, 1, x_21);
lean::cnstr_set(x_59, 2, x_23);
lean::cnstr_set(x_59, 3, x_25);
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
lean::dec(x_17);
x_66 = l_lean_name_to__string___closed__1;
x_67 = l_lean_name_to__string__with__sep___main(x_66, x_12);
x_68 = l_lean_elaborator_universe_elaborate___closed__1;
x_69 = lean::string_append(x_68, x_67);
lean::dec(x_67);
x_71 = l_lean_elaborator_universe_elaborate___closed__2;
x_72 = lean::string_append(x_69, x_71);
x_73 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_72, x_1, x_2);
lean::dec(x_2);
lean::dec(x_72);
lean::dec(x_0);
return x_73;
}
}
}
obj* l_lean_elaborator_universe_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_universe_elaborate(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
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
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
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
x_26 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_15, x_25, x_1, x_2);
lean::dec(x_25);
lean::dec(x_15);
if (lean::obj_tag(x_26) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_11);
lean::dec(x_13);
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
obj* x_35; obj* x_38; obj* x_40; obj* x_43; 
x_35 = lean::cnstr_get(x_26, 0);
lean::inc(x_35);
lean::dec(x_26);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
x_43 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_11, x_1, x_40);
lean::dec(x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_13);
lean::dec(x_38);
x_47 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_49 = x_43;
} else {
 lean::inc(x_47);
 lean::dec(x_43);
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
obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_51 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_53 = x_43;
} else {
 lean::inc(x_51);
 lean::dec(x_43);
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
if (lean::is_scalar(x_13)) {
 x_59 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_59 = x_13;
}
lean::cnstr_set(x_59, 0, x_38);
lean::cnstr_set(x_59, 1, x_54);
if (lean::is_scalar(x_58)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_58;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_56);
if (lean::is_scalar(x_53)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_53;
}
lean::cnstr_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
obj* x_62; 
x_62 = lean::cnstr_get(x_9, 1);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
obj* x_65; obj* x_68; obj* x_70; obj* x_71; 
lean::dec(x_7);
x_65 = lean::cnstr_get(x_0, 1);
lean::inc(x_65);
lean::dec(x_0);
x_68 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_release(x_9, 1);
 x_70 = x_9;
} else {
 lean::inc(x_68);
 lean::dec(x_9);
 x_70 = lean::box(0);
}
x_71 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_65, x_1, x_2);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_68);
lean::dec(x_70);
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
obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_78 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 x_80 = x_71;
} else {
 lean::inc(x_78);
 lean::dec(x_71);
 x_80 = lean::box(0);
}
x_81 = lean::cnstr_get(x_78, 0);
x_83 = lean::cnstr_get(x_78, 1);
if (lean::is_exclusive(x_78)) {
 x_85 = x_78;
} else {
 lean::inc(x_81);
 lean::inc(x_83);
 lean::dec(x_78);
 x_85 = lean::box(0);
}
x_86 = lean::box(0);
x_87 = lean_expr_mk_const(x_68, x_86);
if (lean::is_scalar(x_70)) {
 x_88 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_88 = x_70;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_81);
if (lean::is_scalar(x_85)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_85;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_83);
if (lean::is_scalar(x_80)) {
 x_90 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_90 = x_80;
}
lean::cnstr_set(x_90, 0, x_89);
return x_90;
}
}
else
{
obj* x_92; obj* x_93; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_9);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_92 = x_62;
} else {
 lean::dec(x_62);
 x_92 = lean::box(0);
}
x_93 = lean::cnstr_get(x_0, 1);
lean::inc(x_93);
lean::dec(x_0);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_7);
x_97 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
x_98 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_96, x_97, x_1, x_2);
lean::dec(x_96);
if (lean::obj_tag(x_98) == 0)
{
obj* x_102; obj* x_104; obj* x_105; 
lean::dec(x_93);
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
x_114 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_93, x_1, x_111);
lean::dec(x_111);
if (lean::obj_tag(x_114) == 0)
{
obj* x_118; obj* x_120; obj* x_121; 
lean::dec(x_109);
lean::dec(x_92);
x_118 = lean::cnstr_get(x_114, 0);
if (lean::is_exclusive(x_114)) {
 x_120 = x_114;
} else {
 lean::inc(x_118);
 lean::dec(x_114);
 x_120 = lean::box(0);
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_118);
return x_121;
}
else
{
obj* x_122; obj* x_124; obj* x_125; obj* x_127; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_122 = lean::cnstr_get(x_114, 0);
if (lean::is_exclusive(x_114)) {
 x_124 = x_114;
} else {
 lean::inc(x_122);
 lean::dec(x_114);
 x_124 = lean::box(0);
}
x_125 = lean::cnstr_get(x_122, 0);
x_127 = lean::cnstr_get(x_122, 1);
if (lean::is_exclusive(x_122)) {
 x_129 = x_122;
} else {
 lean::inc(x_125);
 lean::inc(x_127);
 lean::dec(x_122);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_130 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_130 = x_92;
}
lean::cnstr_set(x_130, 0, x_109);
lean::cnstr_set(x_130, 1, x_125);
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_127);
if (lean::is_scalar(x_124)) {
 x_132 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_132 = x_124;
}
lean::cnstr_set(x_132, 0, x_131);
return x_132;
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
lean::dec(x_5);
lean::dec(x_3);
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
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_11; 
x_3 = l_lean_parser_command_attribute_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
lean::inc(x_0);
x_8 = lean::apply_1(x_4, x_0);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
x_11 = l_lean_elaborator_attrs__to__pexpr(x_9, x_1, x_2);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_17 = x_11;
} else {
 lean::inc(x_15);
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
obj* x_19; obj* x_22; obj* x_24; obj* x_27; obj* x_29; 
x_19 = lean::cnstr_get(x_11, 0);
lean::inc(x_19);
lean::dec(x_11);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::cnstr_get(x_8, 5);
lean::inc(x_27);
x_29 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_27, x_1, x_24);
lean::dec(x_24);
if (lean::obj_tag(x_29) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_22);
x_35 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_37 = x_29;
} else {
 lean::inc(x_35);
 lean::dec(x_29);
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
obj* x_39; obj* x_42; obj* x_44; obj* x_47; uint8 x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_39 = lean::cnstr_get(x_29, 0);
lean::inc(x_39);
lean::dec(x_29);
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
lean::dec(x_39);
x_47 = lean::cnstr_get(x_8, 0);
lean::inc(x_47);
lean::dec(x_8);
x_50 = l_option_is__some___main___rarg(x_47);
lean::dec(x_47);
x_52 = l_lean_elaborator_attribute_elaborate___closed__1;
x_53 = l_lean_elaborator_attribute_elaborate___closed__2;
x_54 = l_lean_kvmap_set__bool(x_52, x_53, x_50);
x_55 = l_lean_elaborator_mk__eqns___closed__1;
x_56 = l_lean_expr_mk__capp(x_55, x_42);
x_57 = lean_expr_mk_app(x_22, x_56);
x_58 = lean_expr_mk_mdata(x_54, x_57);
x_59 = l_lean_elaborator_old__elab__command(x_0, x_58, x_1, x_44);
lean::dec(x_0);
return x_59;
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_attribute_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_attribute_elaborate(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
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
lean::dec(x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_lean_elaborator_check_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_12; 
x_3 = l_lean_parser_command_check_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
lean::inc(x_0);
x_8 = lean::apply_1(x_4, x_0);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = l_lean_elaborator_to__pexpr___main(x_9, x_1, x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_1);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_17 = x_12;
} else {
 lean::inc(x_15);
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
obj* x_19; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_29; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
lean::dec(x_19);
x_27 = l_lean_elaborator_check_elaborate___closed__1;
x_28 = lean_expr_mk_mdata(x_27, x_22);
x_29 = l_lean_elaborator_old__elab__command(x_0, x_28, x_1, x_24);
lean::dec(x_0);
return x_29;
}
}
}
obj* l_lean_elaborator_check_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_check_elaborate(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
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
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
lean::inc(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_3);
x_10 = l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
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
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
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
lean::dec(x_12);
x_35 = l_list_append___rarg(x_28, x_33);
x_36 = lean::cnstr_get(x_14, 4);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_14, 5);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_14, 6);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_14, 7);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_14, 8);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_14, 9);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_14, 10);
lean::inc(x_48);
lean::dec(x_14);
x_51 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_51, 0, x_22);
lean::cnstr_set(x_51, 1, x_24);
lean::cnstr_set(x_51, 2, x_26);
lean::cnstr_set(x_51, 3, x_35);
lean::cnstr_set(x_51, 4, x_36);
lean::cnstr_set(x_51, 5, x_38);
lean::cnstr_set(x_51, 6, x_40);
lean::cnstr_set(x_51, 7, x_42);
lean::cnstr_set(x_51, 8, x_44);
lean::cnstr_set(x_51, 9, x_46);
lean::cnstr_set(x_51, 10, x_48);
x_52 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_16;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_51);
if (lean::is_scalar(x_11)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_11;
}
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
}
obj* l_list_map___main___at_lean_elaborator_export_elaborate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_elaborator_export_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_export_elaborate(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_lean_elaborator_init__quot_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("command");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("init_quot");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_lean_kvmap_set__name(x_0, x_3, x_5);
lean::dec(x_5);
lean::dec(x_3);
x_9 = l_lean_elaborator_dummy;
x_10 = lean_expr_mk_mdata(x_6, x_9);
return x_10;
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
obj* x_14; obj* x_17; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_55; uint8 x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
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
lean::dec(x_17);
x_61 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_61, 0, x_32);
lean::cnstr_set(x_61, 1, x_34);
lean::cnstr_set(x_61, 2, x_36);
lean::cnstr_set(x_61, 3, x_38);
lean::cnstr_set(x_61, 4, x_40);
lean::cnstr_set(x_61, 5, x_42);
lean::cnstr_set(x_61, 6, x_59);
x_62 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_62, 0, x_24);
lean::cnstr_set(x_62, 1, x_26);
lean::cnstr_set(x_62, 2, x_28);
lean::cnstr_set(x_62, 3, x_30);
lean::cnstr_set(x_62, 4, x_61);
lean::cnstr_set(x_62, 5, x_45);
lean::cnstr_set(x_62, 6, x_47);
lean::cnstr_set(x_62, 7, x_49);
lean::cnstr_set(x_62, 8, x_51);
lean::cnstr_set(x_62, 9, x_53);
lean::cnstr_set(x_62, 10, x_55);
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
obj* x_67; obj* x_70; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; uint8 x_111; obj* x_112; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_10);
x_67 = lean::cnstr_get(x_7, 1);
lean::inc(x_67);
lean::dec(x_7);
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
lean::dec(x_70);
x_114 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_114, 0, x_85);
lean::cnstr_set(x_114, 1, x_87);
lean::cnstr_set(x_114, 2, x_89);
lean::cnstr_set(x_114, 3, x_91);
lean::cnstr_set(x_114, 4, x_93);
lean::cnstr_set(x_114, 5, x_95);
lean::cnstr_set(x_114, 6, x_112);
x_115 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_115, 0, x_77);
lean::cnstr_set(x_115, 1, x_79);
lean::cnstr_set(x_115, 2, x_81);
lean::cnstr_set(x_115, 3, x_83);
lean::cnstr_set(x_115, 4, x_114);
lean::cnstr_set(x_115, 5, x_98);
lean::cnstr_set(x_115, 6, x_100);
lean::cnstr_set(x_115, 7, x_102);
lean::cnstr_set(x_115, 8, x_104);
lean::cnstr_set(x_115, 9, x_106);
lean::cnstr_set(x_115, 10, x_108);
x_116 = lean::box(0);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_115);
x_118 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_118, 0, x_117);
return x_118;
}
}
case 1:
{
obj* x_119; obj* x_122; obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_147; obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_160; obj* x_163; obj* x_166; 
x_119 = lean::cnstr_get(x_7, 1);
lean::inc(x_119);
lean::dec(x_7);
x_122 = lean::cnstr_get(x_119, 2);
lean::inc(x_122);
lean::dec(x_119);
x_125 = lean::cnstr_get(x_2, 4);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_125, 6);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_2, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_2, 1);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_2, 2);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_2, 3);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_125, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_125, 1);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_125, 2);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_125, 3);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_125, 4);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_125, 5);
lean::inc(x_147);
lean::dec(x_125);
x_150 = lean::cnstr_get(x_2, 5);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_2, 6);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_2, 7);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_2, 8);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_2, 9);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_2, 10);
lean::inc(x_160);
lean::dec(x_2);
x_163 = lean::cnstr_get(x_8, 0);
lean::inc(x_163);
lean::dec(x_8);
x_166 = l_lean_parser_string__lit_view_value(x_163);
if (lean::obj_tag(x_166) == 0)
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
lean::dec(x_122);
x_168 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_168, 0, x_137);
lean::cnstr_set(x_168, 1, x_139);
lean::cnstr_set(x_168, 2, x_141);
lean::cnstr_set(x_168, 3, x_143);
lean::cnstr_set(x_168, 4, x_145);
lean::cnstr_set(x_168, 5, x_147);
lean::cnstr_set(x_168, 6, x_127);
x_169 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_169, 0, x_129);
lean::cnstr_set(x_169, 1, x_131);
lean::cnstr_set(x_169, 2, x_133);
lean::cnstr_set(x_169, 3, x_135);
lean::cnstr_set(x_169, 4, x_168);
lean::cnstr_set(x_169, 5, x_150);
lean::cnstr_set(x_169, 6, x_152);
lean::cnstr_set(x_169, 7, x_154);
lean::cnstr_set(x_169, 8, x_156);
lean::cnstr_set(x_169, 9, x_158);
lean::cnstr_set(x_169, 10, x_160);
x_170 = lean::box(0);
x_171 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_171, 0, x_170);
lean::cnstr_set(x_171, 1, x_169);
x_172 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_172, 0, x_171);
return x_172;
}
else
{
obj* x_173; obj* x_176; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; 
x_173 = lean::cnstr_get(x_166, 0);
lean::inc(x_173);
lean::dec(x_166);
x_176 = l_lean_kvmap_set__string(x_127, x_122, x_173);
lean::dec(x_173);
lean::dec(x_122);
x_179 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_179, 0, x_137);
lean::cnstr_set(x_179, 1, x_139);
lean::cnstr_set(x_179, 2, x_141);
lean::cnstr_set(x_179, 3, x_143);
lean::cnstr_set(x_179, 4, x_145);
lean::cnstr_set(x_179, 5, x_147);
lean::cnstr_set(x_179, 6, x_176);
x_180 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_180, 0, x_129);
lean::cnstr_set(x_180, 1, x_131);
lean::cnstr_set(x_180, 2, x_133);
lean::cnstr_set(x_180, 3, x_135);
lean::cnstr_set(x_180, 4, x_179);
lean::cnstr_set(x_180, 5, x_150);
lean::cnstr_set(x_180, 6, x_152);
lean::cnstr_set(x_180, 7, x_154);
lean::cnstr_set(x_180, 8, x_156);
lean::cnstr_set(x_180, 9, x_158);
lean::cnstr_set(x_180, 10, x_160);
x_181 = lean::box(0);
x_182 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_180);
x_183 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_183, 0, x_182);
return x_183;
}
}
default:
{
obj* x_184; obj* x_187; obj* x_190; obj* x_192; obj* x_194; obj* x_196; obj* x_198; obj* x_200; obj* x_202; obj* x_204; obj* x_206; obj* x_208; obj* x_210; obj* x_212; obj* x_215; obj* x_217; obj* x_219; obj* x_221; obj* x_223; obj* x_225; obj* x_228; obj* x_231; obj* x_232; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
x_184 = lean::cnstr_get(x_7, 1);
lean::inc(x_184);
lean::dec(x_7);
x_187 = lean::cnstr_get(x_184, 2);
lean::inc(x_187);
lean::dec(x_184);
x_190 = lean::cnstr_get(x_2, 4);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_190, 6);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_2, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_2, 1);
lean::inc(x_196);
x_198 = lean::cnstr_get(x_2, 2);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_2, 3);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_190, 0);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_190, 1);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_190, 2);
lean::inc(x_206);
x_208 = lean::cnstr_get(x_190, 3);
lean::inc(x_208);
x_210 = lean::cnstr_get(x_190, 4);
lean::inc(x_210);
x_212 = lean::cnstr_get(x_190, 5);
lean::inc(x_212);
lean::dec(x_190);
x_215 = lean::cnstr_get(x_2, 5);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_2, 6);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_2, 7);
lean::inc(x_219);
x_221 = lean::cnstr_get(x_2, 8);
lean::inc(x_221);
x_223 = lean::cnstr_get(x_2, 9);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_2, 10);
lean::inc(x_225);
lean::dec(x_2);
x_228 = lean::cnstr_get(x_8, 0);
lean::inc(x_228);
lean::dec(x_8);
x_231 = l_lean_parser_number_view_to__nat___main(x_228);
x_232 = l_lean_kvmap_set__nat(x_192, x_187, x_231);
lean::dec(x_231);
lean::dec(x_187);
x_235 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_235, 0, x_202);
lean::cnstr_set(x_235, 1, x_204);
lean::cnstr_set(x_235, 2, x_206);
lean::cnstr_set(x_235, 3, x_208);
lean::cnstr_set(x_235, 4, x_210);
lean::cnstr_set(x_235, 5, x_212);
lean::cnstr_set(x_235, 6, x_232);
x_236 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_236, 0, x_194);
lean::cnstr_set(x_236, 1, x_196);
lean::cnstr_set(x_236, 2, x_198);
lean::cnstr_set(x_236, 3, x_200);
lean::cnstr_set(x_236, 4, x_235);
lean::cnstr_set(x_236, 5, x_215);
lean::cnstr_set(x_236, 6, x_217);
lean::cnstr_set(x_236, 7, x_219);
lean::cnstr_set(x_236, 8, x_221);
lean::cnstr_set(x_236, 9, x_223);
lean::cnstr_set(x_236, 10, x_225);
x_237 = lean::box(0);
x_238 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_238, 0, x_237);
lean::cnstr_set(x_238, 1, x_236);
x_239 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_239, 0, x_238);
return x_239;
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
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_23; uint8 x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
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
lean::dec(x_16);
x_20 = l_lean_file__map_to__position(x_13, x_18);
lean::dec(x_18);
lean::dec(x_13);
x_23 = lean::box(0);
x_24 = 2;
x_25 = l_string_join___closed__1;
lean::inc(x_1);
x_27 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_27, 0, x_11);
lean::cnstr_set(x_27, 1, x_20);
lean::cnstr_set(x_27, 2, x_23);
lean::cnstr_set(x_27, 3, x_25);
lean::cnstr_set(x_27, 4, x_1);
lean::cnstr_set_scalar(x_27, sizeof(void*)*5, x_24);
x_28 = x_27;
x_29 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_30, 0, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_current__command___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_31, 0, x_5);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_32, 0, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_33, 0, x_30);
lean::closure_set(x_33, 1, x_32);
return x_33;
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::inc(x_4);
lean::inc(x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_11);
return x_12;
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed), 5, 0);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_command_elaborate___boxed), 3, 0);
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
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
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
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
return x_10;
}
else
{
obj* x_15; obj* x_18; obj* x_21; obj* x_24; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_3, 1);
lean::inc(x_15);
lean::dec(x_3);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(x_21, x_1, x_2, x_15);
return x_24;
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
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
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
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
obj* l_lean_elaborator_commands_elaborate___main___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
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
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_4, 1);
x_6 = l_lean_elaborator_yield__to__outside___rarg(x_5);
x_7 = lean::box(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__2___boxed), 5, 4);
lean::closure_set(x_8, 0, x_7);
lean::closure_set(x_8, 1, x_1);
lean::closure_set(x_8, 2, x_2);
lean::closure_set(x_8, 3, x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_6);
lean::closure_set(x_10, 1, x_9);
return x_10;
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
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_5);
lean::dec(x_9);
x_16 = lean::box(0);
lean::inc(x_1);
x_18 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_16, x_0, x_1, x_7);
lean::dec(x_7);
x_20 = lean::box(x_2);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 5, 4);
lean::closure_set(x_21, 0, x_20);
lean::closure_set(x_21, 1, x_3);
lean::closure_set(x_21, 2, x_0);
lean::closure_set(x_21, 3, x_1);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_23, 0, x_18);
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
obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_5);
lean::dec(x_9);
x_34 = lean::box(0);
lean::inc(x_1);
x_36 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_34, x_0, x_1, x_7);
lean::dec(x_7);
x_38 = lean::box(x_2);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 5, 4);
lean::closure_set(x_39, 0, x_38);
lean::closure_set(x_39, 1, x_3);
lean::closure_set(x_39, 2, x_0);
lean::closure_set(x_39, 3, x_1);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_40, 0, x_39);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_41, 0, x_36);
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
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_49, 0, x_48);
return x_49;
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_9);
x_51 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4;
x_52 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_5, x_51, x_0, x_1, x_7);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
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
obj* x_59; obj* x_60; 
lean::dec(x_9);
x_59 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5;
x_60 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_5, x_59, x_0, x_1, x_7);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_0);
return x_60;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_67 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_9;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_7);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_70, 0, x_69);
return x_70;
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
lean::dec(x_5);
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
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
x_9 = l_lean_elaborator_current__command___rarg(x_4);
x_10 = lean::box(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__4___boxed), 5, 4);
lean::closure_set(x_11, 0, x_2);
lean::closure_set(x_11, 1, x_3);
lean::closure_set(x_11, 2, x_10);
lean::closure_set(x_11, 3, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = l_lean_elaborator_current__command___rarg(x_4);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__5___boxed), 3, 2);
lean::closure_set(x_15, 0, x_2);
lean::closure_set(x_15, 1, x_3);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_17, 0, x_14);
lean::closure_set(x_17, 1, x_16);
return x_17;
}
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
obj* l_lean_elaborator_commands_elaborate___main___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate___main___lambda__2(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate___main___lambda__3(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_4);
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
obj* l_lean_elaborator_commands_elaborate___main___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_commands_elaborate___main___lambda__5(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_elaborator_commands_elaborate___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate___main(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_1);
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
lean::dec(x_1);
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
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
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
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_5);
x_17 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_9;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_7);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_20, 0, x_19);
return x_20;
}
else
{
obj* x_22; 
lean::dec(x_9);
x_22 = lean::box(0);
x_10 = x_22;
goto lbl_11;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_25; 
lean::dec(x_15);
lean::dec(x_9);
x_25 = lean::box(0);
x_10 = x_25;
goto lbl_11;
}
else
{
obj* x_26; obj* x_29; uint8 x_30; 
x_26 = lean::cnstr_get(x_15, 0);
lean::inc(x_26);
lean::dec(x_15);
x_29 = lean::cnstr_get(x_1, 0);
x_30 = lean_name_dec_eq(x_26, x_29);
lean::dec(x_26);
if (x_30 == 0)
{
obj* x_33; 
lean::dec(x_9);
x_33 = lean::box(0);
x_10 = x_33;
goto lbl_11;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_5);
x_35 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_9;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_7);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_38, 0, x_37);
return x_38;
}
}
}
lbl_11:
{
obj* x_40; obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_10);
x_40 = l_lean_parser_command_end_has__view;
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
lean::dec(x_40);
x_44 = lean::apply_1(x_41, x_5);
x_45 = l_lean_elaborator_end__scope___lambda__2___closed__1;
x_46 = lean::string_append(x_45, x_0);
x_47 = l_lean_elaborator_end__scope___lambda__2___closed__2;
x_48 = lean::string_append(x_46, x_47);
x_49 = lean::box(0);
x_50 = l_option_get__or__else___main___rarg(x_1, x_49);
x_51 = l_lean_name_to__string___closed__1;
x_52 = l_lean_name_to__string__with__sep___main(x_51, x_50);
x_53 = lean::string_append(x_48, x_52);
lean::dec(x_52);
x_55 = l_char_has__repr___closed__1;
x_56 = lean::string_append(x_53, x_55);
x_57 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_44, x_56, x_2, x_3, x_7);
lean::dec(x_7);
return x_57;
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
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end__scope___lambda__2___boxed), 5, 4);
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
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
obj* l_lean_elaborator_end__scope___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_elaborator_end__scope___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 1;
x_5 = lean::mk_nat_obj(1000u);
x_6 = l_lean_elaborator_commands_elaborate___main(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
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
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
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
lean::inc(x_0);
x_27 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_27, 0, x_5);
lean::cnstr_set(x_27, 1, x_7);
lean::cnstr_set(x_27, 2, x_9);
lean::cnstr_set(x_27, 3, x_11);
lean::cnstr_set(x_27, 4, x_0);
lean::cnstr_set(x_27, 5, x_13);
lean::cnstr_set(x_27, 6, x_15);
lean::cnstr_set(x_27, 7, x_17);
lean::cnstr_set(x_27, 8, x_19);
lean::cnstr_set(x_27, 9, x_21);
lean::cnstr_set(x_27, 10, x_23);
x_28 = lean::box(0);
if (lean::is_scalar(x_4)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_4;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_31, 0, x_30);
return x_31;
}
}
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside___boxed), 2, 0);
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
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___boxed), 2, 1);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::inc(x_2);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2;
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4), 4, 3);
lean::closure_set(x_11, 0, x_10);
lean::closure_set(x_11, 1, x_0);
lean::closure_set(x_11, 2, x_1);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_12);
return x_13;
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
obj* x_3; obj* x_5; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_10 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2(x_0, x_1, x_5);
lean::dec(x_5);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_section_elaborate___lambda__1), 4, 3);
lean::closure_set(x_12, 0, x_3);
lean::closure_set(x_12, 1, x_0);
lean::closure_set(x_12, 2, x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_10);
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
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
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
lean::dec(x_4);
x_35 = lean::cnstr_get(x_17, 4);
lean::inc(x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set(x_37, 1, x_35);
x_38 = lean::cnstr_get(x_17, 5);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_17, 6);
lean::inc(x_40);
lean::dec(x_17);
x_43 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_43, 0, x_19);
lean::cnstr_set(x_43, 1, x_21);
lean::cnstr_set(x_43, 2, x_23);
lean::cnstr_set(x_43, 3, x_25);
lean::cnstr_set(x_43, 4, x_37);
lean::cnstr_set(x_43, 5, x_38);
lean::cnstr_set(x_43, 6, x_40);
x_44 = lean::cnstr_get(x_6, 5);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_6, 6);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_6, 7);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_6, 8);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_6, 9);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_6, 10);
lean::inc(x_54);
lean::dec(x_6);
x_57 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_57, 0, x_9);
lean::cnstr_set(x_57, 1, x_11);
lean::cnstr_set(x_57, 2, x_13);
lean::cnstr_set(x_57, 3, x_15);
lean::cnstr_set(x_57, 4, x_43);
lean::cnstr_set(x_57, 5, x_44);
lean::cnstr_set(x_57, 6, x_46);
lean::cnstr_set(x_57, 7, x_48);
lean::cnstr_set(x_57, 8, x_50);
lean::cnstr_set(x_57, 9, x_52);
lean::cnstr_set(x_57, 10, x_54);
x_58 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_8;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_57);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_61, 0, x_60);
x_62 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__1), 3, 2);
lean::closure_set(x_62, 0, x_1);
lean::closure_set(x_62, 1, x_2);
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_63, 0, x_62);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_64, 0, x_61);
lean::closure_set(x_64, 1, x_63);
return x_64;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = l_lean_elaborator_get__namespace___rarg(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2), 4, 3);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_2);
lean::closure_set(x_7, 2, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
return x_9;
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
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__3___boxed), 2, 1);
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
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__3___boxed), 5, 1);
lean::closure_set(x_4, 0, x_0);
lean::inc(x_3);
lean::inc(x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_10);
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
obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 1);
x_8 = lean::cnstr_get(x_7, 2);
lean::inc(x_8);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_8);
x_11 = l_lean_elaborator_namespace_elaborate___lambda__1___closed__1;
x_12 = l_lean_elaborator_end__scope(x_11, x_10, x_1, x_2, x_4);
return x_12;
}
}
obj* l_lean_elaborator_namespace_elaborate___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_3);
x_11 = l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1(x_3, x_0, x_1, x_5);
lean::dec(x_5);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_namespace_elaborate___lambda__1___boxed), 4, 3);
lean::closure_set(x_13, 0, x_3);
lean::closure_set(x_13, 1, x_0);
lean::closure_set(x_13, 2, x_1);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_15, 0, x_11);
lean::closure_set(x_15, 1, x_14);
return x_15;
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
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__3(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_elaborator_namespace_elaborate___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_namespace_elaborate___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(x_0, x_4, x_5);
x_0 = x_6;
x_1 = x_3;
goto _start;
}
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_module_header_elaborate(x_2, x_0, x_4);
lean::dec(x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_9, 0, x_7);
return x_9;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__3), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
obj* x_2; obj* x_4; obj* x_7; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_reserve__notation_elaborate(x_2, x_0, x_4);
lean::dec(x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_9, 0, x_7);
return x_9;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__5), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__7___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__9), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__11___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
obj* x_2; obj* x_4; obj* x_7; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14(x_2, x_0, x_4);
lean::dec(x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_9, 0, x_7);
return x_9;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__13), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
obj* x_2; obj* x_4; obj* x_7; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_attribute_elaborate(x_2, x_0, x_4);
lean::dec(x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_9, 0, x_7);
return x_9;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__15), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__17___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
obj* x_2; obj* x_4; obj* x_7; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_export_elaborate(x_2, x_0, x_4);
lean::dec(x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_9, 0, x_7);
return x_9;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__19___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
obj* x_2; obj* x_4; obj* x_7; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_elaborator_check_elaborate(x_2, x_0, x_4);
lean::dec(x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_9, 0, x_7);
return x_9;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__21), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_10, 0, x_8);
return x_10;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__23), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_elaborator_current__command___rarg(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__25___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
lean::dec(x_64);
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
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldl___main___at_lean_elaborator_elaborators___spec__5(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__1(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__7(x_0, x_1);
lean::dec(x_0);
return x_2;
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
lean::dec(x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_13; 
x_9 = lean::cnstr_get(x_3, 4);
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_13 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(x_0, x_2, x_9);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_18; uint8 x_21; obj* x_23; obj* x_24; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_36; 
x_14 = l_lean_elaborator_resolve__context___main___closed__1;
x_15 = lean::box(0);
lean::inc(x_0);
x_17 = l_lean_name_replace__prefix___main(x_0, x_14, x_15);
x_18 = lean::cnstr_get(x_2, 8);
lean::inc(x_18);
lean::inc(x_17);
x_21 = lean_environment_contains(x_18, x_17);
lean::inc(x_0);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_match__open__spec), 2, 1);
lean::closure_set(x_23, 0, x_0);
x_24 = lean::cnstr_get(x_3, 5);
lean::inc(x_24);
lean::dec(x_3);
x_27 = l_list_filter__map___main___rarg(x_23, x_24);
lean::inc(x_2);
x_29 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(x_2, x_27);
x_30 = lean::cnstr_get(x_2, 3);
lean::inc(x_30);
x_32 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(x_2, x_30);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_resolve__context___main___lambda__1), 2, 1);
lean::closure_set(x_33, 0, x_0);
x_34 = l_list_filter__map___main___rarg(x_33, x_32);
lean::inc(x_2);
x_36 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(x_2, x_34);
if (x_21 == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_17);
x_38 = l_list_append___rarg(x_13, x_29);
x_39 = l_list_append___rarg(x_38, x_36);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_2);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
return x_41;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_17);
lean::cnstr_set(x_42, 1, x_13);
x_43 = l_list_append___rarg(x_42, x_29);
x_44 = l_list_append___rarg(x_43, x_36);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_2);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
return x_46;
}
}
else
{
obj* x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_3);
x_48 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 1);
 x_50 = x_13;
} else {
 lean::inc(x_48);
 lean::dec(x_13);
 x_50 = lean::box(0);
}
x_51 = l_lean_name_append___main(x_48, x_0);
lean::dec(x_48);
x_53 = lean::box(0);
if (lean::is_scalar(x_50)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_50;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_2);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
}
else
{
obj* x_59; obj* x_62; obj* x_64; obj* x_65; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_3);
lean::dec(x_0);
x_59 = lean::cnstr_get(x_7, 0);
lean::inc(x_59);
lean::dec(x_7);
x_62 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 x_64 = x_59;
} else {
 lean::inc(x_62);
 lean::dec(x_59);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_62, 0);
lean::inc(x_65);
lean::dec(x_62);
x_68 = lean::box(0);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set(x_69, 1, x_68);
if (lean::is_scalar(x_64)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_64;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_2);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
return x_71;
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
lean::inc(x_3);
lean::inc(x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::cnstr_get(x_2, 3);
x_7 = lean::cnstr_get(x_2, 4);
x_8 = lean::cnstr_get(x_2, 5);
x_9 = l_lean_elaborator_run___lambda__1___closed__1;
lean::inc(x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_8);
x_12 = lean::cnstr_get(x_2, 6);
x_13 = lean::cnstr_get(x_2, 7);
x_14 = lean::cnstr_get(x_2, 8);
x_15 = lean::cnstr_get(x_2, 9);
x_16 = lean::cnstr_get(x_2, 10);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_27 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_27, 0, x_3);
lean::cnstr_set(x_27, 1, x_4);
lean::cnstr_set(x_27, 2, x_5);
lean::cnstr_set(x_27, 3, x_6);
lean::cnstr_set(x_27, 4, x_7);
lean::cnstr_set(x_27, 5, x_11);
lean::cnstr_set(x_27, 6, x_12);
lean::cnstr_set(x_27, 7, x_13);
lean::cnstr_set(x_27, 8, x_14);
lean::cnstr_set(x_27, 9, x_15);
lean::cnstr_set(x_27, 10, x_16);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_31, 0, x_30);
return x_31;
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
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
return x_15;
}
else
{
obj* x_21; obj* x_24; obj* x_27; 
lean::dec(x_1);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_4, 1);
lean::inc(x_21);
lean::dec(x_4);
x_24 = lean::cnstr_get(x_5, 0);
lean::inc(x_24);
lean::dec(x_5);
x_27 = lean::apply_3(x_24, x_2, x_3, x_21);
return x_27;
}
}
}
obj* l_lean_elaborator_run___lambda__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_2 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_7 = lean::cnstr_get(x_0, 2);
x_8 = lean::cnstr_get(x_0, 3);
x_9 = lean::cnstr_get(x_0, 4);
x_10 = lean::cnstr_get(x_0, 5);
lean::inc(x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::cnstr_get(x_0, 6);
x_14 = lean::cnstr_get(x_0, 7);
x_15 = lean::cnstr_get(x_0, 8);
x_16 = lean::cnstr_get(x_0, 9);
x_17 = lean::cnstr_get(x_0, 10);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
x_28 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_6);
lean::cnstr_set(x_28, 2, x_7);
lean::cnstr_set(x_28, 3, x_8);
lean::cnstr_set(x_28, 4, x_9);
lean::cnstr_set(x_28, 5, x_12);
lean::cnstr_set(x_28, 6, x_13);
lean::cnstr_set(x_28, 7, x_14);
lean::cnstr_set(x_28, 8, x_15);
lean::cnstr_set(x_28, 9, x_16);
lean::cnstr_set(x_28, 10, x_17);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
if (lean::is_scalar(x_4)) {
 x_31 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_31 = x_4;
 lean::cnstr_set_tag(x_4, 1);
}
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_32, 0, x_31);
return x_32;
}
else
{
obj* x_33; 
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_33, 0, x_1);
return x_33;
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
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; 
lean::inc(x_0);
x_6 = l_lean_parser_syntax_to__format___main(x_0);
x_7 = lean::mk_nat_obj(80u);
x_8 = l_lean_format_pretty(x_6, x_7);
lean::dec(x_6);
x_10 = l_lean_elaborator_run___lambda__4___closed__1;
x_11 = lean::string_append(x_10, x_8);
lean::dec(x_8);
x_13 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_0, x_11, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_13;
}
else
{
obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
lean::dec(x_1);
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_lean_elaborator_elaborators;
x_24 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_23, x_20);
lean::inc(x_4);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_4);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__2), 5, 4);
lean::closure_set(x_29, 0, x_20);
lean::closure_set(x_29, 1, x_0);
lean::closure_set(x_29, 2, x_2);
lean::closure_set(x_29, 3, x_3);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_30, 0, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_31, 0, x_28);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__3___boxed), 2, 1);
lean::closure_set(x_32, 0, x_4);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_32);
return x_33;
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
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_pure___at_lean_elaborator_run___spec__3___rarg___boxed), 4, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__4), 5, 1);
lean::closure_set(x_12, 0, x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_with__current__command___rarg___boxed), 6, 5);
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
obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = l_lean_elaborator_preresolve___main(x_3, x_0, x_5);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__5), 4, 3);
lean::closure_set(x_11, 0, x_3);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_lean_elaborator_run___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = l_lean_elaborator_current__command___rarg(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__6), 3, 2);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
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
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
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
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_16, 0, x_13);
return x_16;
}
}
}
obj* _init_l_lean_elaborator_run___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
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
lean::dec(x_6);
x_11 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1;
x_12 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2;
x_13 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_12);
lean::cnstr_set(x_13, 3, x_1);
lean::cnstr_set(x_13, 4, x_0);
lean::cnstr_set(x_13, 5, x_0);
lean::cnstr_set(x_13, 6, x_9);
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
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
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
lean::dec(x_0);
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
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_elaborator_run___lambda__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_run___lambda__3(x_0, x_1);
lean::dec(x_0);
return x_2;
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
