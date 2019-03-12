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
obj* l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6___boxed(obj*, obj*);
obj* l_lean_parser_token__map_insert___rarg(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2(obj*, obj*);
obj* l_lean_elaborator_eoi_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(obj*, obj*);
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(obj*);
obj* l_lean_elaborator_section_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_modify__current__scope___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__4(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(obj*, obj*);
obj* l_lean_elaborator_modify__current__scope(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_command_variables;
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3___rarg(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_pi(obj*, uint8, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11___boxed(obj*);
obj* l_lean_elaborator_module_header_elaborate___closed__1;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__m_monad__state;
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_current__scope(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_level__get__app__args___main___closed__1;
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_process__command___spec__3(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5___boxed(obj*, obj*);
obj* l_lean_elaborator_level__get__app__args___main(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3___closed__1;
obj* l_lean_elaborator_elab__def__like(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___boxed(obj*, obj*, obj*);
obj* l_id___boxed(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3(obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_sort(obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1(obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_attrs__to__pexpr(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___rarg(obj*, obj*, obj*);
extern obj* l_lean_parser_command_attribute_has__view;
obj* l_lean_elaborator_namespace_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2(obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(obj*);
obj* l_lean_elaborator_match__spec___closed__1;
obj* l_lean_elaborator_resolve__context___main___closed__1;
obj* l_lean_elaborator_init__quot_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_open_elaborate___lambda__1(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___rarg(obj*, obj*);
extern obj* l_lean_parser_level_leading_has__view;
extern obj* l_lean_parser_command_reserve__notation_has__view;
obj* l_lean_elaborator_notation_elaborate___closed__1;
obj* l_list_foldl___main___at_lean_expr_mk__app___spec__1(obj*, obj*);
obj* l_lean_elaborator_current__scope___closed__1;
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19___boxed(obj*);
obj* l_lean_elaborator_resolve__context___main___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_set__option_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_command_declaration;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
obj* l_lean_elaborator_to__level(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_get__namespace(obj*, obj*, obj*);
obj* l_lean_elaborator_no__kind_elaborate___closed__1;
obj* l_lean_elaborator_level__add(obj*, obj*);
extern obj* l_string_iterator_extract___main___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__7;
extern obj* l_lean_parser_command_export_has__view;
obj* l_lean_elaborator_to__pexpr___main___closed__33;
obj* l_lean_elaborator_to__pexpr___main___closed__1;
obj* l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__config__coe__frontend__config___boxed(obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___closed__1;
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_include_elaborate(obj*, obj*, obj*, obj*);
uint8 l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___rarg(obj*, obj*, obj*);
obj* l_list_filter__map___main___rarg(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_match_has__view;
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___boxed(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_level__get__app__args(obj*, obj*, obj*, obj*);
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__5(obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__9(obj*);
extern obj* l_lean_parser_command_open;
obj* l_lean_elaborator_declaration_elaborate___closed__4;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__config__coe__frontend__config(obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__26;
obj* l_lean_elaborator_declaration_elaborate___lambda__5___closed__1;
obj* l_lean_kvmap_set__string(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_elab__def__like___lambda__1(obj*, obj*);
obj* l_lean_parser_term_get__leading___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3(obj*, obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3___boxed(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__7(obj*, obj*);
extern obj* l_lean_expander_error___rarg___lambda__1___closed__1;
obj* l_lean_elaborator_notation_elaborate__aux___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__eqns___closed__2;
obj* l_reader__t_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate__aux___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1(obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___boxed(obj*, obj*, obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___boxed(obj*, obj*);
obj* l_lean_elaborator_mk__state___closed__5;
obj* l_lean_elaborator_universe_elaborate___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__31;
obj* l_lean_elaborator_module_header_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_register__notation__macro(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_process__command___lambda__2___closed__2;
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(obj*);
obj* l_lean_elaborator_preresolve___main___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_include_elaborate___spec__1(obj*, obj*);
obj* l_list_enum__from___main___rarg(obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_mk__state___closed__6;
obj* l_lean_elaborator_variables_elaborate___closed__2;
uint8 l_lean_elaborator_match__precedence___main(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__39;
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___boxed(obj*);
obj* l_lean_parser_number_view_to__nat___main(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_sort_has__view_x_27___lambda__1___closed__4;
obj* l_lean_elaborator_end_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_open_has__view;
obj* l_lean_elaborator_mk__notation__kind___rarg(obj*);
obj* l_lean_elaborator_resolve__context___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12___boxed(obj*, obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__13(obj*, obj*);
extern "C" obj* lean_expr_local(obj*, obj*, obj*, uint8);
obj* l_lean_parser_term_simple__binder_view_to__binder__info___main(obj*);
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___rarg(obj*, obj*);
extern obj* l_lean_parser_command_set__option;
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2(obj*, obj*);
obj* l_lean_elaborator_max__recursion;
obj* l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1___boxed(obj*, obj*);
obj* l_lean_elaborator_section_elaborate___closed__1;
obj* l_lean_elaborator_elab__def__like___closed__1;
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(obj*);
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_expr_mk__annotation___closed__1;
obj* l_list_zip___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_rec__t_run___at_lean_elaborator_process__command___spec__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__6;
obj* l_lean_elaborator_process__command___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_check_elaborate(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___rarg___boxed(obj*, obj*);
obj* l_lean_elaborator_elaborator__m_monad;
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_elaborator_declaration_elaborate___closed__2;
obj* l_lean_elaborator_eoi_elaborate___closed__1;
obj* l_lean_elaborator_declaration_elaborate___closed__5;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_old__elab__command___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___boxed(obj*, obj*, obj*, obj*);
uint8 l_coe__decidable__eq(uint8);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_notation;
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__2;
obj* l_lean_kvmap_set__name(obj*, obj*, obj*);
uint8 l_lean_elaborator_is__open__namespace(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborators;
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___boxed(obj*);
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__9(obj*);
extern obj* l_lean_parser_string__lit_has__view;
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__8___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_pi_has__view;
obj* l_lean_elaborator_export_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2___boxed(obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_find___rarg(obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
uint8 l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_resolve__context___main___lambda__1(obj*, obj*);
extern obj* l_lean_parser_command_universe_has__view;
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
obj* l_state__t_monad__state___rarg(obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__7___boxed(obj*, obj*);
extern "C" obj* lean_expr_mk_lambda(obj*, uint8, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___boxed(obj*, obj*);
obj* l_lean_kvmap_set__nat(obj*, obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__11(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main___closed__4;
obj* l_lean_elaborator_check_elaborate___closed__1;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___boxed(obj*, obj*);
extern obj* l_lean_parser_command_include;
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___rarg(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__8(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_set__option_elaborate___lambda__1(obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__6(obj*, obj*);
obj* l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_environment_contains___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_lean_elaborator_notation_elaborate___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
extern "C" obj* lean_expr_mk_const(obj*, obj*);
extern obj* l_lean_parser_command_reserve__notation;
obj* l_except__t_monad__except___rarg(obj*);
obj* l_lean_elaborator_mk__state___closed__4;
extern obj* l_lean_parser_term_have_has__view;
obj* l_lean_elaborator_init__quot_elaborate(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_variables_has__view;
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1(obj*, obj*);
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__32;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_lean_parser_trie_insert___rarg(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_preresolve___main(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___boxed(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___boxed(obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind___rarg___closed__1;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__5;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1___boxed(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18___boxed(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__3;
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(obj*, obj*);
obj* l_lean_elaborator_expr_mk__annotation(obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7(obj*, obj*, obj*);
obj* l_lean_elaborator_get__namespace___boxed(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_name_replace__prefix___main(obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate__aux___lambda__1(obj*, obj*);
obj* l_lean_elaborator_open_elaborate(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_section_has__view;
obj* l_lean_elaborator_mk__notation__kind___boxed(obj*, obj*);
obj* l_list_join___main___rarg(obj*);
obj* l_lean_elaborator_mangle__ident(obj*);
obj* l_lean_elaborator_universe_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list(obj*, obj*, obj*);
obj* l_lean_elaborator_process__command___lambda__1___closed__1;
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___rarg(obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_name__set_insert___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view;
obj* l_lean_elaborator_to__pexpr___main___closed__4;
obj* l_lean_parser_syntax_get__pos(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___boxed(obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4(obj*, obj*);
extern "C" obj* level_mk_imax(obj*, obj*);
obj* l_lean_environment_mk__empty___boxed(obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__15___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___boxed(obj*, obj*);
obj* l_lean_elaborator_attribute_elaborate___closed__2;
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5;
obj* l_list_zip__with___main___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_reserve__notation_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_simple__binders__to__pexpr(obj*, obj*, obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(obj*, obj*, obj*);
obj* l_lean_elaborator_is__open__namespace___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(obj*);
obj* l_lean_elaborator_namespace_elaborate___closed__1;
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___boxed(obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__parser(obj*, obj*, obj*);
obj* l_lean_elaborator_match__open__spec(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__11;
obj* l_lean_elaborator_level__add___main___boxed(obj*, obj*);
obj* l_lean_elaborator_end_elaborate___closed__4;
obj* l_lean_elaborator_ordered__rbmap_empty(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10___boxed(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__16;
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___rarg(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___rarg(obj*, obj*, obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4___boxed(obj*, obj*);
obj* l_lean_elaborator_attrs__to__pexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__17;
extern obj* l_lean_parser_module_header;
obj* l_lean_elaborator_level__get__app__args___main___boxed(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_names__to__pexpr___spec__1(obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__36;
obj* l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5(obj*, obj*);
obj* l_lean_elaborator_update__parser__config(obj*, obj*, obj*);
extern obj* l_lean_parser_no__kind;
obj* l_lean_elaborator_level__add___boxed(obj*, obj*);
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__46;
extern obj* l_lean_parser_module_eoi;
obj* l_lean_elaborator_elaborator__m_monad__except;
obj* l_lean_elaborator_command__parser__config_register__notation__tokens(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__10;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__4(obj*, obj*, obj*);
obj* l_lean_elaborator_process__command___lambda__2___closed__1;
obj* l_lean_elaborator_end_elaborate___closed__2;
uint8 l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___rarg(obj*, obj*, obj*);
obj* l_except__t_monad___rarg___lambda__8___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1___boxed(obj*);
obj* l_lean_elaborator_namespace_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_match__precedence___boxed(obj*, obj*);
extern obj* l_lean_message__log_empty;
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_register__notation__macro___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___boxed(obj*, obj*);
obj* l_lean_elaborator_export_elaborate(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(obj*);
obj* l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__38;
obj* l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5___boxed(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8(obj*);
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(obj*);
uint8 l_lean_elaborator_is__open__namespace___main(obj*, obj*);
obj* l_lean_elaborator_notation_elaborate___lambda__1(obj*, obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_elaborator_elaborator__m_monad__reader;
extern "C" obj* lean_environment_mk_empty(obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_mangle__ident___spec__1(obj*, obj*);
obj* l_lean_elaborator_include_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_universe_elaborate___lambda__1(obj*, obj*);
extern obj* l_lean_expander_binding__annotation__update;
extern obj* l_lean_parser_command_attribute;
extern obj* l_lean_parser_term_let_has__view;
obj* l_lean_elaborator_ordered__rbmap_find___boxed(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___rarg___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3;
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___rarg(obj*, obj*, obj*);
extern "C" obj* level_mk_succ(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__45;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__14;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___boxed(obj*, obj*);
obj* l_lean_elaborator_universe_elaborate___closed__2;
obj* l_lean_elaborator_is__open__namespace___main___boxed(obj*, obj*);
extern obj* l_lean_parser_term_projection_has__view;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_end_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__5___closed__2;
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_variables_elaborate___closed__1;
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___boxed(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__12;
obj* l_lean_parser_syntax_to__format___main(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(obj*, obj*);
obj* l_lean_name_append___main(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1___boxed(obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__35;
obj* l_lean_elaborator_to__pexpr___main___closed__25;
obj* l_lean_elaborator_names__to__pexpr(obj*);
obj* l_lean_elaborator_modify__current__scope___closed__1;
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___rarg(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_check_has__view;
obj* l_lean_elaborator_set__option_elaborate(obj*, obj*, obj*, obj*);
obj* l_reader__t_read___rarg(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2___boxed(obj*, obj*);
obj* l_lean_elaborator_no__kind_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_resolve__context___main(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_max__prec;
obj* l_lean_elaborator_notation_elaborate__aux(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___rarg(obj*, obj*);
obj* l_lean_elaborator_elaborator__m_lean_parser_monad__rec;
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___rarg(obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___boxed(obj*, obj*);
obj* l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_universe_elaborate___closed__1;
obj* l_monad__state__trans___rarg(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__20;
extern obj* l_lean_parser_command_end;
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__10___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_lean_expander_get__opt__type___main(obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2(obj*, obj*);
extern obj* l_lean_parser_term_struct__inst_has__view;
extern obj* l_lean_parser_term_lambda_has__view;
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___boxed(obj*, obj*);
obj* l_lean_elaborator_mk__eqns___closed__1;
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___rarg___boxed(obj*, obj*);
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19(obj*);
obj* l_lean_elaborator_resolve__context(obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg(obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__5(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_let(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_process__command___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_app_has__view;
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2___boxed(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
obj* l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6___boxed(obj*, obj*);
obj* l_lean_elaborator_to__level___main(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_ident__univs_has__view;
obj* l_lean_elaborator_to__pexpr___main___closed__9;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(obj*);
obj* l_state__t_monad__except___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
obj* l_reader__t_monad__except___rarg(obj*);
extern obj* l_lean_parser_term_sort__app_has__view;
extern obj* l_lean_parser_term_explicit_has__view;
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__20(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
obj* l_lean_elaborator_mk__state___closed__2;
obj* l_lean_elaborator_prec__to__nat(obj*);
obj* l_lean_elaborator_process__command___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
obj* l_id_monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__24;
obj* l_lean_elaborator_ordered__rbmap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_reserve__notation_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_term_parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate(obj*, obj*, obj*, obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__13;
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(obj*, obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__3;
obj* l_lean_elaborator_to__level___main___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__27;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1;
obj* l_lean_elaborator_end_elaborate___closed__3;
obj* l_lean_format_pretty(obj*, obj*);
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___boxed(obj*, obj*);
extern obj* l_lean_parser_command_namespace_has__view;
obj* l_lean_elaborator_preresolve___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___boxed(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__15;
obj* l_lean_elaborator_notation_elaborate___closed__2;
obj* l_lean_elaborator_to__pexpr___main___closed__18;
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___boxed(obj*, obj*);
extern obj* l_lean_parser_term_inaccessible_has__view;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5___boxed(obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__2;
obj* l_lean_elaborator_dummy;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_module_header_elaborate(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_parser_syntax_kind___main(obj*);
obj* l_lean_elaborator_eoi_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__2;
obj* l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6(obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___boxed(obj*);
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___lambda__1(obj*, uint8, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1;
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_section_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_preresolve(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__2(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
extern obj* l_lean_parser_module_header_has__view;
uint8 l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__1;
extern obj* l_lean_parser_command_section;
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__21;
uint8 l_lean_name_quick__lt(obj*, obj*);
obj* l_lean_elaborator_end_elaborate___closed__1;
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_struct__inst__item_has__view;
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___rarg(obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_match__precedence___main___boxed(obj*, obj*);
extern obj* l_lean_parser_term_borrowed_has__view;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_term_binders_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_current__scope___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_find(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__1;
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(obj*, obj*);
extern obj* l_lean_parser_command_universe;
obj* l_lean_elaborator_to__pexpr___main___closed__19;
obj* l_list_map___main___at_lean_elaborator_ident__univ__params__to__pexpr___spec__1(obj*);
extern obj* l_lean_parser_term_show_has__view;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(obj*);
obj* l_lean_level_of__nat___main(obj*);
extern obj* l_lean_parser_syntax_reprint__lst___main___closed__1;
obj* l_lean_elaborator_declaration_elaborate___lambda__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__22;
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___rarg(obj*, obj*);
obj* l_reader__t_lift___rarg___boxed(obj*, obj*);
obj* l_lean_parser_term_binder__ident_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__8;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___boxed(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__43;
obj* l_lean_elaborator_attribute_elaborate___closed__1;
uint8 l_lean_elaborator_match__precedence(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__12(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__23;
obj* l_lean_elaborator_elab__def__like___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_string_trim(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__34;
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___boxed(obj*, obj*);
obj* l_lean_elaborator_process__command___lambda__1(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_sort_has__view;
obj* l_lean_elaborator_level__get__app__args___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_check_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main___closed__2;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
obj* l_lean_elaborator_open_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__7(obj*);
obj* l_lean_elaborator_match__spec(obj*, obj*);
obj* l_lean_expander_mk__notation__transformer(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__30;
obj* l_lean_expr_local___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__eqns(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__14(obj*);
obj* l_lean_elaborator_level__add___main(obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborate__command___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_simple__binders__to__pexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_expr_mk__capp(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* level_mk_mvar(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__20___boxed(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(obj*, obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_declaration_has__view;
obj* l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
extern obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
obj* l_lean_elaborator_include_elaborate___lambda__1(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___boxed(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11___rarg(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_mk__state(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2___rarg(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_kvmap_insert__core___main(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__28;
obj* l_lean_elaborator_to__level___main___closed__3;
extern obj* l_lean_parser_command_end_has__view;
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___boxed(obj*);
obj* l_id_bind___boxed(obj*, obj*);
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__8;
obj* l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__17(obj*);
obj* l_lean_elaborator_process__command(obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(obj*);
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_anonymous__constructor_has__view;
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2;
obj* l_lean_elaborator_to__pexpr___main___closed__37;
obj* l_lean_elaborator_attribute_elaborate(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__2(obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__6(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_init__quot;
obj* l_lean_elaborator_variables_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__41;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__1;
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19___rarg(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(obj*);
obj* l_lean_elaborator_ident__univ__params__to__pexpr(obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__10(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbtree_to__list___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___boxed(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_update__parser__config___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_process__command___spec__3___boxed(obj*, obj*);
obj* l_lean_elaborator_to__pexpr(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_postprocess__notation__spec(obj*);
obj* l_lean_elaborator_elab__def__like___closed__2;
extern obj* l_lean_parser_command_include_has__view;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__5(obj*);
extern obj* l_lean_parser_command_namespace;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3___boxed(obj*);
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(obj*);
obj* l_lean_elaborator_old__elab__command(obj*, obj*, obj*, obj*, obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___boxed(obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1(obj*);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
extern "C" obj* level_mk_param(obj*);
obj* l_lean_elaborator_declaration_elaborate___closed__3;
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1(obj*);
extern "C" obj* lean_elaborator_elaborate_command(obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___rarg(obj*, obj*, obj*);
extern obj* l_lean_expander_get__opt__type___main___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_level_trailing_has__view;
obj* l_lean_elaborator_process__command___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6(obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___rarg___boxed(obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
obj* l_lean_elaborator_attribute_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__29;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
extern obj* l_lean_expander_no__expansion___closed__1;
extern "C" obj* lean_expr_mk_bvar(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__40;
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__15(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18(obj*, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(obj*);
extern "C" obj* lean_expr_mk_mvar(obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_id_monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11(obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(obj*);
obj* l_lean_elaborator_command_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_prec__to__nat___main(obj*);
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__6(obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_view_value(obj*);
obj* l_lean_elaborator_mk__state___closed__3;
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_process__command___spec__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2___boxed(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__42;
extern "C" uint8 lean_environment_contains(obj*, obj*);
extern obj* l_lean_parser_command_notation_has__view;
obj* l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2___boxed(obj*, obj*);
extern obj* l_lean_parser_command_check;
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_id_monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__10(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10___rarg(obj*, obj*, obj*);
extern obj* l_lean_parser_command_export;
obj* l_lean_elaborator_old__elab__command___lambda__1(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__44;
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2(obj*, obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_variables_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
obj* l_lean_elaborator_init__quot_elaborate___closed__1;
obj* l_lean_elaborator_postprocess__notation__spec___closed__1;
obj* l_lean_elaborator_mk__state___closed__1;
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
lean::dec(x_0);
lean::dec(x_1);
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
lean::dec(x_0);
lean::dec(x_2);
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
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_6 = 0;
x_7 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_2);
lean::cnstr_set_scalar(x_7, sizeof(void*)*4, x_6);
x_8 = x_7;
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_22; uint8 x_23; 
x_10 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
x_14 = lean::cnstr_get(x_2, 2);
x_16 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_18 = x_2;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_2);
 x_18 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_3);
lean::inc(x_0);
x_22 = lean::apply_2(x_0, x_3, x_12);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_27; uint8 x_28; 
lean::inc(x_3);
lean::inc(x_12);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_12, x_3);
x_28 = lean::unbox(x_27);
if (x_28 == 0)
{
obj* x_32; obj* x_33; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_12);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_18;
}
lean::cnstr_set(x_32, 0, x_10);
lean::cnstr_set(x_32, 1, x_3);
lean::cnstr_set(x_32, 2, x_4);
lean::cnstr_set(x_32, 3, x_16);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_9);
x_33 = x_32;
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, lean::box(0), x_16, x_3, x_4);
if (lean::is_scalar(x_18)) {
 x_35 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_35 = x_18;
}
lean::cnstr_set(x_35, 0, x_10);
lean::cnstr_set(x_35, 1, x_12);
lean::cnstr_set(x_35, 2, x_14);
lean::cnstr_set(x_35, 3, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*4, x_9);
x_36 = x_35;
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, lean::box(0), x_10, x_3, x_4);
if (lean::is_scalar(x_18)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_18;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_12);
lean::cnstr_set(x_38, 2, x_14);
lean::cnstr_set(x_38, 3, x_16);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_9);
x_39 = x_38;
return x_39;
}
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_2, 0);
x_42 = lean::cnstr_get(x_2, 1);
x_44 = lean::cnstr_get(x_2, 2);
x_46 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_48 = x_2;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_2);
 x_48 = lean::box(0);
}
lean::inc(x_42);
lean::inc(x_3);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_3, x_42);
x_53 = lean::unbox(x_52);
if (x_53 == 0)
{
obj* x_57; uint8 x_58; 
lean::inc(x_3);
lean::inc(x_42);
lean::inc(x_0);
x_57 = lean::apply_2(x_0, x_42, x_3);
x_58 = lean::unbox(x_57);
if (x_58 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_0);
lean::dec(x_44);
lean::dec(x_42);
if (lean::is_scalar(x_48)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_48;
}
lean::cnstr_set(x_62, 0, x_40);
lean::cnstr_set(x_62, 1, x_3);
lean::cnstr_set(x_62, 2, x_4);
lean::cnstr_set(x_62, 3, x_46);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_9);
x_63 = x_62;
return x_63;
}
else
{
uint8 x_64; 
x_64 = l_rbnode_is__red___main___rarg(x_46);
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, lean::box(0), x_46, x_3, x_4);
if (lean::is_scalar(x_48)) {
 x_66 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_66 = x_48;
}
lean::cnstr_set(x_66, 0, x_40);
lean::cnstr_set(x_66, 1, x_42);
lean::cnstr_set(x_66, 2, x_44);
lean::cnstr_set(x_66, 3, x_65);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_9);
x_67 = x_66;
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_68 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_69 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_69 = x_48;
}
lean::cnstr_set(x_69, 0, x_40);
lean::cnstr_set(x_69, 1, x_42);
lean::cnstr_set(x_69, 2, x_44);
lean::cnstr_set(x_69, 3, x_68);
lean::cnstr_set_scalar(x_69, sizeof(void*)*4, x_9);
x_70 = x_69;
x_71 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, lean::box(0), x_46, x_3, x_4);
x_72 = l_rbnode_balance2___main___rarg(x_70, x_71);
return x_72;
}
}
}
else
{
uint8 x_73; 
x_73 = l_rbnode_is__red___main___rarg(x_40);
if (x_73 == 0)
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, lean::box(0), x_40, x_3, x_4);
if (lean::is_scalar(x_48)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_48;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_42);
lean::cnstr_set(x_75, 2, x_44);
lean::cnstr_set(x_75, 3, x_46);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_9);
x_76 = x_75;
return x_76;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_77 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_78 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_78 = x_48;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_42);
lean::cnstr_set(x_78, 2, x_44);
lean::cnstr_set(x_78, 3, x_46);
lean::cnstr_set_scalar(x_78, sizeof(void*)*4, x_9);
x_79 = x_78;
x_80 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, lean::box(0), x_40, x_3, x_4);
x_81 = l_rbnode_balance1___main___rarg(x_79, x_80);
return x_81;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_6 = 0;
x_7 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_2);
lean::cnstr_set_scalar(x_7, sizeof(void*)*4, x_6);
x_8 = x_7;
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_22; uint8 x_23; 
x_10 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
x_14 = lean::cnstr_get(x_2, 2);
x_16 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_18 = x_2;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_2);
 x_18 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_3);
lean::inc(x_0);
x_22 = lean::apply_2(x_0, x_3, x_12);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_27; uint8 x_28; 
lean::inc(x_3);
lean::inc(x_12);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_12, x_3);
x_28 = lean::unbox(x_27);
if (x_28 == 0)
{
obj* x_32; obj* x_33; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_12);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_18;
}
lean::cnstr_set(x_32, 0, x_10);
lean::cnstr_set(x_32, 1, x_3);
lean::cnstr_set(x_32, 2, x_4);
lean::cnstr_set(x_32, 3, x_16);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_9);
x_33 = x_32;
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, lean::box(0), x_16, x_3, x_4);
if (lean::is_scalar(x_18)) {
 x_35 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_35 = x_18;
}
lean::cnstr_set(x_35, 0, x_10);
lean::cnstr_set(x_35, 1, x_12);
lean::cnstr_set(x_35, 2, x_14);
lean::cnstr_set(x_35, 3, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*4, x_9);
x_36 = x_35;
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, lean::box(0), x_10, x_3, x_4);
if (lean::is_scalar(x_18)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_18;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_12);
lean::cnstr_set(x_38, 2, x_14);
lean::cnstr_set(x_38, 3, x_16);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_9);
x_39 = x_38;
return x_39;
}
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_2, 0);
x_42 = lean::cnstr_get(x_2, 1);
x_44 = lean::cnstr_get(x_2, 2);
x_46 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_48 = x_2;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_2);
 x_48 = lean::box(0);
}
lean::inc(x_42);
lean::inc(x_3);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_3, x_42);
x_53 = lean::unbox(x_52);
if (x_53 == 0)
{
obj* x_57; uint8 x_58; 
lean::inc(x_3);
lean::inc(x_42);
lean::inc(x_0);
x_57 = lean::apply_2(x_0, x_42, x_3);
x_58 = lean::unbox(x_57);
if (x_58 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_0);
lean::dec(x_44);
lean::dec(x_42);
if (lean::is_scalar(x_48)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_48;
}
lean::cnstr_set(x_62, 0, x_40);
lean::cnstr_set(x_62, 1, x_3);
lean::cnstr_set(x_62, 2, x_4);
lean::cnstr_set(x_62, 3, x_46);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_9);
x_63 = x_62;
return x_63;
}
else
{
uint8 x_64; 
x_64 = l_rbnode_is__red___main___rarg(x_46);
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, lean::box(0), x_46, x_3, x_4);
if (lean::is_scalar(x_48)) {
 x_66 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_66 = x_48;
}
lean::cnstr_set(x_66, 0, x_40);
lean::cnstr_set(x_66, 1, x_42);
lean::cnstr_set(x_66, 2, x_44);
lean::cnstr_set(x_66, 3, x_65);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_9);
x_67 = x_66;
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_68 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_69 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_69 = x_48;
}
lean::cnstr_set(x_69, 0, x_40);
lean::cnstr_set(x_69, 1, x_42);
lean::cnstr_set(x_69, 2, x_44);
lean::cnstr_set(x_69, 3, x_68);
lean::cnstr_set_scalar(x_69, sizeof(void*)*4, x_9);
x_70 = x_69;
x_71 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, lean::box(0), x_46, x_3, x_4);
x_72 = l_rbnode_balance2___main___rarg(x_70, x_71);
return x_72;
}
}
}
else
{
uint8 x_73; 
x_73 = l_rbnode_is__red___main___rarg(x_40);
if (x_73 == 0)
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, lean::box(0), x_40, x_3, x_4);
if (lean::is_scalar(x_48)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_48;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_42);
lean::cnstr_set(x_75, 2, x_44);
lean::cnstr_set(x_75, 3, x_46);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_9);
x_76 = x_75;
return x_76;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_77 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_78 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_78 = x_48;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_42);
lean::cnstr_set(x_78, 2, x_44);
lean::cnstr_set(x_78, 3, x_46);
lean::cnstr_set_scalar(x_78, sizeof(void*)*4, x_9);
x_79 = x_78;
x_80 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, lean::box(0), x_40, x_3, x_4);
x_81 = l_rbnode_balance1___main___rarg(x_79, x_80);
return x_81;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_rbnode_is__red___main___rarg(x_2);
if (x_5 == 0)
{
obj* x_6; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, lean::box(0), x_2, x_3, x_4);
return x_6;
}
else
{
obj* x_7; obj* x_8; 
x_7 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, lean::box(0), x_2, x_3, x_4);
x_8 = l_rbnode_set__black___main___rarg(x_7);
return x_8;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(x_0, lean::box(0), x_1, x_2, x_3);
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
x_17 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(x_0, lean::box(0), x_10, x_2, x_16);
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
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
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
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_6 = 0;
x_7 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_2);
lean::cnstr_set_scalar(x_7, sizeof(void*)*4, x_6);
x_8 = x_7;
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_22; uint8 x_23; 
x_10 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
x_14 = lean::cnstr_get(x_2, 2);
x_16 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_18 = x_2;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_2);
 x_18 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_3);
lean::inc(x_0);
x_22 = lean::apply_2(x_0, x_3, x_12);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_27; uint8 x_28; 
lean::inc(x_3);
lean::inc(x_12);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_12, x_3);
x_28 = lean::unbox(x_27);
if (x_28 == 0)
{
obj* x_32; obj* x_33; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_12);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_18;
}
lean::cnstr_set(x_32, 0, x_10);
lean::cnstr_set(x_32, 1, x_3);
lean::cnstr_set(x_32, 2, x_4);
lean::cnstr_set(x_32, 3, x_16);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_9);
x_33 = x_32;
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, lean::box(0), x_16, x_3, x_4);
if (lean::is_scalar(x_18)) {
 x_35 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_35 = x_18;
}
lean::cnstr_set(x_35, 0, x_10);
lean::cnstr_set(x_35, 1, x_12);
lean::cnstr_set(x_35, 2, x_14);
lean::cnstr_set(x_35, 3, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*4, x_9);
x_36 = x_35;
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, lean::box(0), x_10, x_3, x_4);
if (lean::is_scalar(x_18)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_18;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_12);
lean::cnstr_set(x_38, 2, x_14);
lean::cnstr_set(x_38, 3, x_16);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_9);
x_39 = x_38;
return x_39;
}
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_2, 0);
x_42 = lean::cnstr_get(x_2, 1);
x_44 = lean::cnstr_get(x_2, 2);
x_46 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_48 = x_2;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_2);
 x_48 = lean::box(0);
}
lean::inc(x_42);
lean::inc(x_3);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_3, x_42);
x_53 = lean::unbox(x_52);
if (x_53 == 0)
{
obj* x_57; uint8 x_58; 
lean::inc(x_3);
lean::inc(x_42);
lean::inc(x_0);
x_57 = lean::apply_2(x_0, x_42, x_3);
x_58 = lean::unbox(x_57);
if (x_58 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_0);
lean::dec(x_44);
lean::dec(x_42);
if (lean::is_scalar(x_48)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_48;
}
lean::cnstr_set(x_62, 0, x_40);
lean::cnstr_set(x_62, 1, x_3);
lean::cnstr_set(x_62, 2, x_4);
lean::cnstr_set(x_62, 3, x_46);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_9);
x_63 = x_62;
return x_63;
}
else
{
uint8 x_64; 
x_64 = l_rbnode_is__red___main___rarg(x_46);
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, lean::box(0), x_46, x_3, x_4);
if (lean::is_scalar(x_48)) {
 x_66 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_66 = x_48;
}
lean::cnstr_set(x_66, 0, x_40);
lean::cnstr_set(x_66, 1, x_42);
lean::cnstr_set(x_66, 2, x_44);
lean::cnstr_set(x_66, 3, x_65);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_9);
x_67 = x_66;
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_68 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_69 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_69 = x_48;
}
lean::cnstr_set(x_69, 0, x_40);
lean::cnstr_set(x_69, 1, x_42);
lean::cnstr_set(x_69, 2, x_44);
lean::cnstr_set(x_69, 3, x_68);
lean::cnstr_set_scalar(x_69, sizeof(void*)*4, x_9);
x_70 = x_69;
x_71 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, lean::box(0), x_46, x_3, x_4);
x_72 = l_rbnode_balance2___main___rarg(x_70, x_71);
return x_72;
}
}
}
else
{
uint8 x_73; 
x_73 = l_rbnode_is__red___main___rarg(x_40);
if (x_73 == 0)
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, lean::box(0), x_40, x_3, x_4);
if (lean::is_scalar(x_48)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_48;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_42);
lean::cnstr_set(x_75, 2, x_44);
lean::cnstr_set(x_75, 3, x_46);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_9);
x_76 = x_75;
return x_76;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_77 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_78 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_78 = x_48;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_42);
lean::cnstr_set(x_78, 2, x_44);
lean::cnstr_set(x_78, 3, x_46);
lean::cnstr_set_scalar(x_78, sizeof(void*)*4, x_9);
x_79 = x_78;
x_80 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, lean::box(0), x_40, x_3, x_4);
x_81 = l_rbnode_balance1___main___rarg(x_79, x_80);
return x_81;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_6 = 0;
x_7 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_2);
lean::cnstr_set_scalar(x_7, sizeof(void*)*4, x_6);
x_8 = x_7;
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_22; uint8 x_23; 
x_10 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
x_14 = lean::cnstr_get(x_2, 2);
x_16 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_18 = x_2;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_2);
 x_18 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_3);
lean::inc(x_0);
x_22 = lean::apply_2(x_0, x_3, x_12);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_27; uint8 x_28; 
lean::inc(x_3);
lean::inc(x_12);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_12, x_3);
x_28 = lean::unbox(x_27);
if (x_28 == 0)
{
obj* x_32; obj* x_33; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_12);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_18;
}
lean::cnstr_set(x_32, 0, x_10);
lean::cnstr_set(x_32, 1, x_3);
lean::cnstr_set(x_32, 2, x_4);
lean::cnstr_set(x_32, 3, x_16);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_9);
x_33 = x_32;
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, lean::box(0), x_16, x_3, x_4);
if (lean::is_scalar(x_18)) {
 x_35 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_35 = x_18;
}
lean::cnstr_set(x_35, 0, x_10);
lean::cnstr_set(x_35, 1, x_12);
lean::cnstr_set(x_35, 2, x_14);
lean::cnstr_set(x_35, 3, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*4, x_9);
x_36 = x_35;
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, lean::box(0), x_10, x_3, x_4);
if (lean::is_scalar(x_18)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_18;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_12);
lean::cnstr_set(x_38, 2, x_14);
lean::cnstr_set(x_38, 3, x_16);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_9);
x_39 = x_38;
return x_39;
}
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_2, 0);
x_42 = lean::cnstr_get(x_2, 1);
x_44 = lean::cnstr_get(x_2, 2);
x_46 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_48 = x_2;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_2);
 x_48 = lean::box(0);
}
lean::inc(x_42);
lean::inc(x_3);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_3, x_42);
x_53 = lean::unbox(x_52);
if (x_53 == 0)
{
obj* x_57; uint8 x_58; 
lean::inc(x_3);
lean::inc(x_42);
lean::inc(x_0);
x_57 = lean::apply_2(x_0, x_42, x_3);
x_58 = lean::unbox(x_57);
if (x_58 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_0);
lean::dec(x_44);
lean::dec(x_42);
if (lean::is_scalar(x_48)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_48;
}
lean::cnstr_set(x_62, 0, x_40);
lean::cnstr_set(x_62, 1, x_3);
lean::cnstr_set(x_62, 2, x_4);
lean::cnstr_set(x_62, 3, x_46);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_9);
x_63 = x_62;
return x_63;
}
else
{
uint8 x_64; 
x_64 = l_rbnode_is__red___main___rarg(x_46);
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, lean::box(0), x_46, x_3, x_4);
if (lean::is_scalar(x_48)) {
 x_66 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_66 = x_48;
}
lean::cnstr_set(x_66, 0, x_40);
lean::cnstr_set(x_66, 1, x_42);
lean::cnstr_set(x_66, 2, x_44);
lean::cnstr_set(x_66, 3, x_65);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_9);
x_67 = x_66;
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_68 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_69 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_69 = x_48;
}
lean::cnstr_set(x_69, 0, x_40);
lean::cnstr_set(x_69, 1, x_42);
lean::cnstr_set(x_69, 2, x_44);
lean::cnstr_set(x_69, 3, x_68);
lean::cnstr_set_scalar(x_69, sizeof(void*)*4, x_9);
x_70 = x_69;
x_71 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, lean::box(0), x_46, x_3, x_4);
x_72 = l_rbnode_balance2___main___rarg(x_70, x_71);
return x_72;
}
}
}
else
{
uint8 x_73; 
x_73 = l_rbnode_is__red___main___rarg(x_40);
if (x_73 == 0)
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, lean::box(0), x_40, x_3, x_4);
if (lean::is_scalar(x_48)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_48;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_42);
lean::cnstr_set(x_75, 2, x_44);
lean::cnstr_set(x_75, 3, x_46);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_9);
x_76 = x_75;
return x_76;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_77 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_78 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_78 = x_48;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_42);
lean::cnstr_set(x_78, 2, x_44);
lean::cnstr_set(x_78, 3, x_46);
lean::cnstr_set_scalar(x_78, sizeof(void*)*4, x_9);
x_79 = x_78;
x_80 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, lean::box(0), x_40, x_3, x_4);
x_81 = l_rbnode_balance1___main___rarg(x_79, x_80);
return x_81;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_rbnode_is__red___main___rarg(x_2);
if (x_5 == 0)
{
obj* x_6; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, lean::box(0), x_2, x_3, x_4);
return x_6;
}
else
{
obj* x_7; obj* x_8; 
x_7 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, lean::box(0), x_2, x_3, x_4);
x_8 = l_rbnode_set__black___main___rarg(x_7);
return x_8;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(x_0, lean::box(0), x_1, x_2, x_3);
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
x_17 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(x_0, lean::box(0), x_10, x_2, x_16);
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
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
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
obj* _init_l_lean_elaborator_elaborator__m_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_except__t_monad___rarg(x_9);
x_11 = l_state__t_monad___rarg(x_10);
x_12 = l_reader__t_monad___rarg(x_11);
x_13 = l_reader__t_monad___rarg(x_12);
return x_13;
}
}
obj* _init_l_lean_elaborator_elaborator__m_lean_parser_monad__rec() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_except__t_monad___rarg(x_9);
x_11 = l_state__t_monad___rarg(x_10);
x_12 = l_reader__t_monad___rarg(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg), 3, 1);
lean::closure_set(x_13, 0, x_12);
return x_13;
}
}
obj* _init_l_lean_elaborator_elaborator__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_except__t_monad___rarg(x_9);
x_11 = l_state__t_monad___rarg(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_read___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___rarg___boxed), 2, 1);
lean::closure_set(x_13, 0, x_12);
return x_13;
}
}
obj* _init_l_lean_elaborator_elaborator__m_monad__state() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_except__t_monad___rarg(x_9);
lean::inc(x_10);
x_12 = l_state__t_monad___rarg(x_10);
lean::inc(x_12);
x_14 = l_reader__t_monad___rarg(x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_15, 0, lean::box(0));
lean::closure_set(x_15, 1, lean::box(0));
lean::closure_set(x_15, 2, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_16, 0, lean::box(0));
lean::closure_set(x_16, 1, lean::box(0));
lean::closure_set(x_16, 2, x_12);
x_17 = l_state__t_monad__state___rarg(x_10);
x_18 = l_monad__state__trans___rarg(x_16, x_17);
x_19 = l_monad__state__trans___rarg(x_15, x_18);
return x_19;
}
}
obj* _init_l_lean_elaborator_elaborator__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_except__t_monad___rarg(x_9);
x_12 = l_except__t_monad__except___rarg(x_9);
x_13 = l_state__t_monad__except___rarg(x_11, lean::box(0), x_12);
x_14 = l_reader__t_monad__except___rarg(x_13);
x_15 = l_reader__t_monad__except___rarg(x_14);
return x_15;
}
}
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::apply_3(x_1, x_0, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_command_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::apply_3(x_1, x_0, x_2, x_3);
return x_4;
}
}
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = l_lean_expander_error___rarg___lambda__1___closed__1;
x_15 = l_lean_file__map_to__position(x_10, x_14);
x_16 = 2;
x_17 = l_string_iterator_extract___main___closed__1;
x_18 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_18, 0, x_8);
lean::cnstr_set(x_18, 1, x_15);
lean::cnstr_set(x_18, 2, x_13);
lean::cnstr_set(x_18, 3, x_17);
lean::cnstr_set(x_18, 4, x_1);
lean::cnstr_set_scalar(x_18, sizeof(void*)*5, x_16);
x_19 = x_18;
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_21 = lean::cnstr_get(x_0, 0);
x_22 = l_lean_parser_syntax_get__pos(x_21);
x_23 = lean::mk_nat_obj(0u);
x_24 = l_option_get__or__else___main___rarg(x_22, x_23);
lean::dec(x_22);
x_26 = l_lean_file__map_to__position(x_10, x_24);
x_27 = 2;
x_28 = l_string_iterator_extract___main___closed__1;
x_29 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set(x_29, 4, x_1);
lean::cnstr_set_scalar(x_29, sizeof(void*)*5, x_27);
x_30 = x_29;
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
}
}
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* _init_l_lean_elaborator_current__scope___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("current_scope: unreachable");
return x_0;
}
}
obj* l_lean_elaborator_current__scope(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 4);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(0);
x_6 = l_lean_elaborator_current__scope___closed__1;
x_7 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_5, x_6, x_0, x_1, x_2);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_13; obj* x_14; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_2);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
}
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_current__scope___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_current__scope(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* _init_l_lean_elaborator_modify__current__scope___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("modify_current_scope: unreachable");
return x_0;
}
}
obj* l_lean_elaborator_modify__current__scope(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_3, 4);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = l_lean_elaborator_modify__current__scope___closed__1;
x_9 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_7, x_8, x_1, x_2, x_3);
lean::dec(x_3);
return x_9;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_2);
x_12 = lean::cnstr_get(x_4, 0);
x_14 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_16 = x_4;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_4);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_3, 2);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_3, 3);
lean::inc(x_23);
x_25 = lean::apply_1(x_0, x_12);
if (lean::is_scalar(x_16)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_16;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_14);
x_27 = lean::cnstr_get(x_3, 5);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_3, 6);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_3, 7);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_3, 8);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_3, 9);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_3, 10);
lean::inc(x_37);
lean::dec(x_3);
x_40 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_40, 0, x_17);
lean::cnstr_set(x_40, 1, x_19);
lean::cnstr_set(x_40, 2, x_21);
lean::cnstr_set(x_40, 3, x_23);
lean::cnstr_set(x_40, 4, x_26);
lean::cnstr_set(x_40, 5, x_27);
lean::cnstr_set(x_40, 6, x_29);
lean::cnstr_set(x_40, 7, x_31);
lean::cnstr_set(x_40, 8, x_33);
lean::cnstr_set(x_40, 9, x_35);
lean::cnstr_set(x_40, 10, x_37);
x_41 = lean::box(0);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
return x_43;
}
}
}
obj* l_lean_elaborator_modify__current__scope___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_modify__current__scope(x_0, x_1, x_2, x_3);
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
obj* _init_l_lean_elaborator_level__get__app__args___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("level_get_app_args: unexpected input: ");
return x_0;
}
}
obj* l_lean_elaborator_level__get__app__args___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_0);
x_5 = l_lean_parser_syntax_kind___main(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_0);
x_8 = l_lean_parser_syntax_to__format___main(x_0);
x_9 = lean::mk_nat_obj(80u);
x_10 = l_lean_format_pretty(x_8, x_9);
x_11 = l_lean_elaborator_level__get__app__args___main___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_7, x_12, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_7);
return x_14;
}
else
{
obj* x_17; obj* x_19; obj* x_20; uint8 x_21; 
x_17 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_19 = x_5;
} else {
 lean::inc(x_17);
 lean::dec(x_5);
 x_19 = lean::box(0);
}
x_20 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_21 = lean_name_dec_eq(x_17, x_20);
if (x_21 == 0)
{
obj* x_22; uint8 x_23; 
x_22 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_23 = lean_name_dec_eq(x_17, x_22);
lean::dec(x_17);
if (x_23 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
lean::inc(x_0);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_0);
x_27 = l_lean_parser_syntax_to__format___main(x_0);
x_28 = lean::mk_nat_obj(80u);
x_29 = l_lean_format_pretty(x_27, x_28);
x_30 = l_lean_elaborator_level__get__app__args___main___closed__1;
x_31 = lean::string_append(x_30, x_29);
lean::dec(x_29);
x_33 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_26, x_31, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_26);
return x_33;
}
else
{
obj* x_37; obj* x_38; obj* x_42; 
lean::dec(x_19);
x_37 = l_lean_parser_level_trailing_has__view;
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
lean::dec(x_37);
lean::inc(x_0);
x_42 = lean::apply_1(x_38, x_0);
if (lean::obj_tag(x_42) == 0)
{
obj* x_44; obj* x_47; obj* x_49; 
lean::dec(x_0);
x_44 = lean::cnstr_get(x_42, 0);
lean::inc(x_44);
lean::dec(x_42);
x_47 = lean::cnstr_get(x_44, 0);
lean::inc(x_47);
x_49 = l_lean_elaborator_level__get__app__args___main(x_47, x_1, x_2, x_3);
if (lean::obj_tag(x_49) == 0)
{
obj* x_51; obj* x_53; obj* x_54; 
lean::dec(x_44);
x_51 = lean::cnstr_get(x_49, 0);
if (lean::is_exclusive(x_49)) {
 x_53 = x_49;
} else {
 lean::inc(x_51);
 lean::dec(x_49);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
return x_54;
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_55 = lean::cnstr_get(x_49, 0);
if (lean::is_exclusive(x_49)) {
 x_57 = x_49;
} else {
 lean::inc(x_55);
 lean::dec(x_49);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_55, 0);
x_60 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 x_62 = x_55;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_55);
 x_62 = lean::box(0);
}
x_63 = lean::cnstr_get(x_58, 0);
x_65 = lean::cnstr_get(x_58, 1);
if (lean::is_exclusive(x_58)) {
 x_67 = x_58;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_58);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_44, 1);
lean::inc(x_68);
lean::dec(x_44);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_65);
if (lean::is_scalar(x_67)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_67;
}
lean::cnstr_set(x_72, 0, x_63);
lean::cnstr_set(x_72, 1, x_71);
if (lean::is_scalar(x_62)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_62;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_60);
if (lean::is_scalar(x_57)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_57;
}
lean::cnstr_set(x_74, 0, x_73);
return x_74;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_2);
lean::dec(x_42);
x_77 = lean::box(0);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_0);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_3);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_19);
lean::dec(x_2);
lean::dec(x_17);
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_0);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_3);
x_87 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
return x_87;
}
}
}
}
obj* l_lean_elaborator_level__get__app__args___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_level__get__app__args___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_level__get__app__args(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_level__get__app__args___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_level__get__app__args___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_level__get__app__args(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_lean_elaborator_to__level___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
x_30 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
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
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
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
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_lean_elaborator_to__level___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
x_30 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
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
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
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
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_name_quick__lt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = l_lean_name_quick__lt(x_5, x_1);
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___rarg___boxed), 2, 0);
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
x_5 = l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___rarg(x_2, x_1);
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
obj* l_lean_elaborator_to__level___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; 
lean::inc(x_2);
lean::inc(x_0);
x_6 = l_lean_elaborator_level__get__app__args___main(x_0, x_1, x_2, x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_18; obj* x_21; obj* x_23; obj* x_27; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::dec(x_13);
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_16, 1);
lean::inc(x_23);
lean::dec(x_16);
lean::inc(x_2);
x_27 = l_lean_elaborator_current__scope(x_1, x_2, x_18);
if (lean::obj_tag(x_27) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_21);
lean::dec(x_23);
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_45; 
x_36 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_set(x_27, 0, lean::box(0));
 x_38 = x_27;
} else {
 lean::inc(x_36);
 lean::dec(x_27);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
x_41 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_set(x_36, 0, lean::box(0));
 lean::cnstr_set(x_36, 1, lean::box(0));
 x_43 = x_36;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_36);
 x_43 = lean::box(0);
}
lean::inc(x_21);
x_45 = l_lean_parser_syntax_kind___main(x_21);
if (lean::obj_tag(x_45) == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_59; 
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::inc(x_0);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_0);
x_53 = l_lean_parser_syntax_to__format___main(x_0);
x_54 = lean::mk_nat_obj(80u);
x_55 = l_lean_format_pretty(x_53, x_54);
x_56 = l_lean_elaborator_to__level___main___closed__1;
x_57 = lean::string_append(x_56, x_55);
lean::dec(x_55);
x_59 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_52, x_57, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_52);
return x_59;
}
else
{
obj* x_62; obj* x_64; obj* x_65; uint8 x_66; 
x_62 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_set(x_45, 0, lean::box(0));
 x_64 = x_45;
} else {
 lean::inc(x_62);
 lean::dec(x_45);
 x_64 = lean::box(0);
}
x_65 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_66 = lean_name_dec_eq(x_62, x_65);
if (x_66 == 0)
{
obj* x_70; uint8 x_71; 
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
x_70 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_71 = lean_name_dec_eq(x_62, x_70);
lean::dec(x_62);
if (x_71 == 0)
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_83; 
lean::dec(x_21);
lean::dec(x_23);
lean::inc(x_0);
if (lean::is_scalar(x_64)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_64;
}
lean::cnstr_set(x_76, 0, x_0);
x_77 = l_lean_parser_syntax_to__format___main(x_0);
x_78 = lean::mk_nat_obj(80u);
x_79 = l_lean_format_pretty(x_77, x_78);
x_80 = l_lean_elaborator_to__level___main___closed__1;
x_81 = lean::string_append(x_80, x_79);
lean::dec(x_79);
x_83 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_76, x_81, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_76);
return x_83;
}
else
{
obj* x_86; obj* x_87; obj* x_90; 
x_86 = l_lean_parser_level_trailing_has__view;
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
lean::dec(x_86);
x_90 = lean::apply_1(x_87, x_21);
if (lean::obj_tag(x_90) == 0)
{
obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_90);
lean::dec(x_23);
if (lean::is_scalar(x_64)) {
 x_93 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_93 = x_64;
}
lean::cnstr_set(x_93, 0, x_0);
x_94 = l_lean_elaborator_to__level___main___closed__2;
x_95 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_93, x_94, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_93);
return x_95;
}
else
{
if (lean::obj_tag(x_23) == 0)
{
obj* x_100; obj* x_103; obj* x_105; 
lean::dec(x_64);
lean::dec(x_0);
x_100 = lean::cnstr_get(x_90, 0);
lean::inc(x_100);
lean::dec(x_90);
x_103 = lean::cnstr_get(x_100, 0);
lean::inc(x_103);
x_105 = l_lean_elaborator_to__level___main(x_103, x_1, x_2, x_41);
if (lean::obj_tag(x_105) == 0)
{
obj* x_107; obj* x_109; obj* x_110; 
lean::dec(x_100);
x_107 = lean::cnstr_get(x_105, 0);
if (lean::is_exclusive(x_105)) {
 x_109 = x_105;
} else {
 lean::inc(x_107);
 lean::dec(x_105);
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
obj* x_111; obj* x_113; obj* x_114; obj* x_116; obj* x_118; obj* x_119; obj* x_122; obj* x_123; obj* x_126; obj* x_127; 
x_111 = lean::cnstr_get(x_105, 0);
if (lean::is_exclusive(x_105)) {
 x_113 = x_105;
} else {
 lean::inc(x_111);
 lean::dec(x_105);
 x_113 = lean::box(0);
}
x_114 = lean::cnstr_get(x_111, 0);
x_116 = lean::cnstr_get(x_111, 1);
if (lean::is_exclusive(x_111)) {
 x_118 = x_111;
} else {
 lean::inc(x_114);
 lean::inc(x_116);
 lean::dec(x_111);
 x_118 = lean::box(0);
}
x_119 = lean::cnstr_get(x_100, 2);
lean::inc(x_119);
lean::dec(x_100);
x_122 = l_lean_parser_number_view_to__nat___main(x_119);
x_123 = l_lean_elaborator_level__add___main(x_114, x_122);
lean::dec(x_122);
lean::dec(x_114);
if (lean::is_scalar(x_118)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_118;
}
lean::cnstr_set(x_126, 0, x_123);
lean::cnstr_set(x_126, 1, x_116);
if (lean::is_scalar(x_113)) {
 x_127 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_127 = x_113;
}
lean::cnstr_set(x_127, 0, x_126);
return x_127;
}
}
else
{
obj* x_130; obj* x_131; obj* x_132; 
lean::dec(x_90);
lean::dec(x_23);
if (lean::is_scalar(x_64)) {
 x_130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_130 = x_64;
}
lean::cnstr_set(x_130, 0, x_0);
x_131 = l_lean_elaborator_to__level___main___closed__2;
x_132 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_130, x_131, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_130);
return x_132;
}
}
}
}
else
{
obj* x_136; obj* x_137; obj* x_140; 
lean::dec(x_62);
x_136 = l_lean_parser_level_leading_has__view;
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
lean::dec(x_136);
x_140 = lean::apply_1(x_137, x_21);
switch (lean::obj_tag(x_140)) {
case 0:
{
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::dec(x_140);
if (lean::obj_tag(x_23) == 0)
{
obj* x_145; obj* x_146; obj* x_147; 
if (lean::is_scalar(x_64)) {
 x_145 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_145 = x_64;
}
lean::cnstr_set(x_145, 0, x_0);
x_146 = l_lean_elaborator_to__level___main___closed__2;
x_147 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_145, x_146, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_145);
return x_147;
}
else
{
obj* x_152; obj* x_154; obj* x_158; 
lean::dec(x_64);
lean::dec(x_0);
x_152 = lean::cnstr_get(x_23, 0);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_23, 1);
lean::inc(x_154);
lean::dec(x_23);
lean::inc(x_2);
x_158 = l_lean_elaborator_to__level___main(x_152, x_1, x_2, x_41);
if (lean::obj_tag(x_158) == 0)
{
obj* x_161; obj* x_163; obj* x_164; 
lean::dec(x_154);
lean::dec(x_2);
x_161 = lean::cnstr_get(x_158, 0);
if (lean::is_exclusive(x_158)) {
 x_163 = x_158;
} else {
 lean::inc(x_161);
 lean::dec(x_158);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_161);
return x_164;
}
else
{
obj* x_165; obj* x_168; obj* x_170; obj* x_173; 
x_165 = lean::cnstr_get(x_158, 0);
lean::inc(x_165);
lean::dec(x_158);
x_168 = lean::cnstr_get(x_165, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_165, 1);
lean::inc(x_170);
lean::dec(x_165);
x_173 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_154, x_1, x_2, x_170);
if (lean::obj_tag(x_173) == 0)
{
obj* x_175; obj* x_177; obj* x_178; 
lean::dec(x_168);
x_175 = lean::cnstr_get(x_173, 0);
if (lean::is_exclusive(x_173)) {
 x_177 = x_173;
} else {
 lean::inc(x_175);
 lean::dec(x_173);
 x_177 = lean::box(0);
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_175);
return x_178;
}
else
{
obj* x_179; obj* x_181; obj* x_182; obj* x_184; obj* x_186; obj* x_187; obj* x_189; obj* x_190; 
x_179 = lean::cnstr_get(x_173, 0);
if (lean::is_exclusive(x_173)) {
 x_181 = x_173;
} else {
 lean::inc(x_179);
 lean::dec(x_173);
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
x_187 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(x_168, x_182);
lean::dec(x_168);
if (lean::is_scalar(x_186)) {
 x_189 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_189 = x_186;
}
lean::cnstr_set(x_189, 0, x_187);
lean::cnstr_set(x_189, 1, x_184);
if (lean::is_scalar(x_181)) {
 x_190 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_190 = x_181;
}
lean::cnstr_set(x_190, 0, x_189);
return x_190;
}
}
}
}
case 1:
{
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::dec(x_140);
if (lean::obj_tag(x_23) == 0)
{
obj* x_195; obj* x_196; obj* x_197; 
if (lean::is_scalar(x_64)) {
 x_195 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_195 = x_64;
}
lean::cnstr_set(x_195, 0, x_0);
x_196 = l_lean_elaborator_to__level___main___closed__2;
x_197 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_195, x_196, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_195);
return x_197;
}
else
{
obj* x_202; obj* x_204; obj* x_208; 
lean::dec(x_64);
lean::dec(x_0);
x_202 = lean::cnstr_get(x_23, 0);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_23, 1);
lean::inc(x_204);
lean::dec(x_23);
lean::inc(x_2);
x_208 = l_lean_elaborator_to__level___main(x_202, x_1, x_2, x_41);
if (lean::obj_tag(x_208) == 0)
{
obj* x_211; obj* x_213; obj* x_214; 
lean::dec(x_204);
lean::dec(x_2);
x_211 = lean::cnstr_get(x_208, 0);
if (lean::is_exclusive(x_208)) {
 x_213 = x_208;
} else {
 lean::inc(x_211);
 lean::dec(x_208);
 x_213 = lean::box(0);
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
obj* x_215; obj* x_218; obj* x_220; obj* x_223; 
x_215 = lean::cnstr_get(x_208, 0);
lean::inc(x_215);
lean::dec(x_208);
x_218 = lean::cnstr_get(x_215, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_215, 1);
lean::inc(x_220);
lean::dec(x_215);
x_223 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_204, x_1, x_2, x_220);
if (lean::obj_tag(x_223) == 0)
{
obj* x_225; obj* x_227; obj* x_228; 
lean::dec(x_218);
x_225 = lean::cnstr_get(x_223, 0);
if (lean::is_exclusive(x_223)) {
 x_227 = x_223;
} else {
 lean::inc(x_225);
 lean::dec(x_223);
 x_227 = lean::box(0);
}
if (lean::is_scalar(x_227)) {
 x_228 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_228 = x_227;
}
lean::cnstr_set(x_228, 0, x_225);
return x_228;
}
else
{
obj* x_229; obj* x_231; obj* x_232; obj* x_234; obj* x_236; obj* x_237; obj* x_239; obj* x_240; 
x_229 = lean::cnstr_get(x_223, 0);
if (lean::is_exclusive(x_223)) {
 x_231 = x_223;
} else {
 lean::inc(x_229);
 lean::dec(x_223);
 x_231 = lean::box(0);
}
x_232 = lean::cnstr_get(x_229, 0);
x_234 = lean::cnstr_get(x_229, 1);
if (lean::is_exclusive(x_229)) {
 x_236 = x_229;
} else {
 lean::inc(x_232);
 lean::inc(x_234);
 lean::dec(x_229);
 x_236 = lean::box(0);
}
x_237 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(x_218, x_232);
lean::dec(x_218);
if (lean::is_scalar(x_236)) {
 x_239 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_239 = x_236;
}
lean::cnstr_set(x_239, 0, x_237);
lean::cnstr_set(x_239, 1, x_234);
if (lean::is_scalar(x_231)) {
 x_240 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_240 = x_231;
}
lean::cnstr_set(x_240, 0, x_239);
return x_240;
}
}
}
}
case 2:
{
lean::dec(x_39);
lean::dec(x_140);
if (lean::obj_tag(x_23) == 0)
{
obj* x_246; obj* x_247; obj* x_248; 
lean::dec(x_64);
lean::dec(x_0);
lean::dec(x_2);
x_246 = l_lean_elaborator_to__level___main___closed__3;
if (lean::is_scalar(x_43)) {
 x_247 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_247 = x_43;
}
lean::cnstr_set(x_247, 0, x_246);
lean::cnstr_set(x_247, 1, x_41);
if (lean::is_scalar(x_38)) {
 x_248 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_248 = x_38;
}
lean::cnstr_set(x_248, 0, x_247);
return x_248;
}
else
{
obj* x_252; obj* x_253; obj* x_254; 
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_43);
if (lean::is_scalar(x_64)) {
 x_252 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_252 = x_64;
}
lean::cnstr_set(x_252, 0, x_0);
x_253 = l_lean_elaborator_to__level___main___closed__2;
x_254 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_252, x_253, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_252);
return x_254;
}
}
case 3:
{
obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::dec(x_140);
if (lean::is_scalar(x_64)) {
 x_262 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_262 = x_64;
}
lean::cnstr_set(x_262, 0, x_0);
x_263 = l_lean_elaborator_to__level___main___closed__2;
x_264 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_262, x_263, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_262);
return x_264;
}
case 4:
{
lean::dec(x_39);
if (lean::obj_tag(x_23) == 0)
{
obj* x_271; obj* x_274; obj* x_275; obj* x_277; obj* x_278; 
lean::dec(x_64);
lean::dec(x_0);
lean::dec(x_2);
x_271 = lean::cnstr_get(x_140, 0);
lean::inc(x_271);
lean::dec(x_140);
x_274 = l_lean_parser_number_view_to__nat___main(x_271);
x_275 = l_lean_level_of__nat___main(x_274);
lean::dec(x_274);
if (lean::is_scalar(x_43)) {
 x_277 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_277 = x_43;
}
lean::cnstr_set(x_277, 0, x_275);
lean::cnstr_set(x_277, 1, x_41);
if (lean::is_scalar(x_38)) {
 x_278 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_278 = x_38;
}
lean::cnstr_set(x_278, 0, x_277);
return x_278;
}
else
{
obj* x_283; obj* x_284; obj* x_285; 
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_43);
lean::dec(x_140);
if (lean::is_scalar(x_64)) {
 x_283 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_283 = x_64;
}
lean::cnstr_set(x_283, 0, x_0);
x_284 = l_lean_elaborator_to__level___main___closed__2;
x_285 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_283, x_284, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_283);
return x_285;
}
}
default:
{
if (lean::obj_tag(x_23) == 0)
{
obj* x_288; obj* x_291; obj* x_292; obj* x_295; 
x_288 = lean::cnstr_get(x_140, 0);
lean::inc(x_288);
lean::dec(x_140);
x_291 = l_lean_elaborator_mangle__ident(x_288);
x_292 = lean::cnstr_get(x_39, 3);
lean::inc(x_292);
lean::dec(x_39);
x_295 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_292, x_291);
if (lean::obj_tag(x_295) == 0)
{
obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_304; obj* x_305; obj* x_306; 
lean::dec(x_38);
lean::dec(x_43);
if (lean::is_scalar(x_64)) {
 x_298 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_298 = x_64;
}
lean::cnstr_set(x_298, 0, x_0);
x_299 = l_lean_name_to__string___closed__1;
x_300 = l_lean_name_to__string__with__sep___main(x_299, x_291);
x_301 = l_lean_elaborator_to__level___main___closed__4;
x_302 = lean::string_append(x_301, x_300);
lean::dec(x_300);
x_304 = l_char_has__repr___closed__1;
x_305 = lean::string_append(x_302, x_304);
x_306 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_298, x_305, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_298);
return x_306;
}
else
{
obj* x_313; obj* x_314; obj* x_315; 
lean::dec(x_64);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_295);
x_313 = level_mk_param(x_291);
if (lean::is_scalar(x_43)) {
 x_314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_314 = x_43;
}
lean::cnstr_set(x_314, 0, x_313);
lean::cnstr_set(x_314, 1, x_41);
if (lean::is_scalar(x_38)) {
 x_315 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_315 = x_38;
}
lean::cnstr_set(x_315, 0, x_314);
return x_315;
}
}
else
{
obj* x_321; obj* x_322; obj* x_323; 
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::dec(x_140);
if (lean::is_scalar(x_64)) {
 x_321 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_321 = x_64;
}
lean::cnstr_set(x_321, 0, x_0);
x_322 = l_lean_elaborator_to__level___main___closed__2;
x_323 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_321, x_322, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_321);
return x_323;
}
}
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___rarg(x_0, x_1);
lean::dec(x_1);
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
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_to__level___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_to__level___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_to__level(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_to__level___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_to__level___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_to__level(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
lean::inc(x_2);
x_17 = l_lean_elaborator_to__pexpr___main(x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
x_33 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__1(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_12);
lean::dec(x_28);
x_36 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_38 = x_33;
} else {
 lean::inc(x_36);
 lean::dec(x_33);
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
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_42 = x_33;
} else {
 lean::inc(x_40);
 lean::dec(x_33);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 0);
x_45 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 x_47 = x_40;
} else {
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_12;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_43);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
if (lean::is_scalar(x_42)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_42;
}
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__2(obj* x_0) {
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
x_10 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__2(x_4);
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
obj* _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_match_fn");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_16; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::inc(x_2);
x_16 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__1(x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_16) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
obj* x_25; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_37; 
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
x_33 = lean::cnstr_get(x_8, 2);
lean::inc(x_33);
lean::dec(x_8);
lean::inc(x_2);
x_37 = l_lean_elaborator_to__pexpr___main(x_33, x_1, x_2, x_30);
if (lean::obj_tag(x_37) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_28);
lean::dec(x_32);
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
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
obj* x_47; obj* x_50; obj* x_52; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_37, 0);
lean::inc(x_47);
lean::dec(x_37);
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
x_55 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3(x_10, x_1, x_2, x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_61; obj* x_63; obj* x_64; 
lean::dec(x_12);
lean::dec(x_28);
lean::dec(x_32);
lean::dec(x_50);
lean::dec(x_54);
x_61 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 x_63 = x_55;
} else {
 lean::inc(x_61);
 lean::dec(x_55);
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
obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_65 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 x_67 = x_55;
} else {
 lean::inc(x_65);
 lean::dec(x_55);
 x_67 = lean::box(0);
}
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
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_28);
lean::cnstr_set(x_73, 1, x_50);
x_74 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3___closed__1;
if (lean::is_scalar(x_54)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_54;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_73);
if (lean::is_scalar(x_12)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_12;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_68);
if (lean::is_scalar(x_32)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_32;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_70);
if (lean::is_scalar(x_67)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_67;
}
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
lean::inc(x_2);
x_17 = l_lean_elaborator_to__pexpr___main(x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
x_33 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_12);
lean::dec(x_28);
x_36 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_38 = x_33;
} else {
 lean::inc(x_36);
 lean::dec(x_33);
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
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_42 = x_33;
} else {
 lean::inc(x_40);
 lean::dec(x_33);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 0);
x_45 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 x_47 = x_40;
} else {
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_12;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_43);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
if (lean::is_scalar(x_42)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_42;
}
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__5(obj* x_0) {
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
x_16 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__5(x_7);
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
x_34 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__5(x_25);
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
x_39 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_30);
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
x_57 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_48);
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
obj* _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("field");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("to_pexpr: unreachable");
return x_0;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_24; 
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
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_3);
x_24 = l_lean_elaborator_to__pexpr___main(x_21, x_2, x_3, x_4);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
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
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_37);
lean::dec(x_17);
lean::dec(x_18);
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
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_50 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_52 = x_42;
} else {
 lean::inc(x_50);
 lean::dec(x_42);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_50, 0);
x_55 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_57 = x_50;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_50);
 x_57 = lean::box(0);
}
x_58 = lean::box(0);
x_59 = lean::cnstr_get(x_18, 0);
lean::inc(x_59);
lean::dec(x_18);
x_62 = l_lean_elaborator_mangle__ident(x_59);
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__1;
x_64 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_65 = lean_expr_mk_mdata(x_64, x_37);
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_57)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_57;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_52;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_12);
x_70 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_72 = x_1;
} else {
 lean::inc(x_70);
 lean::dec(x_1);
 x_72 = lean::box(0);
}
lean::inc(x_0);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_0);
x_75 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_77 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_74, x_75, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_70);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_86 = x_77;
} else {
 lean::inc(x_84);
 lean::dec(x_77);
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
obj* x_88; obj* x_91; obj* x_93; obj* x_96; 
x_88 = lean::cnstr_get(x_77, 0);
lean::inc(x_88);
lean::dec(x_77);
x_91 = lean::cnstr_get(x_88, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
x_96 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7(x_0, x_70, x_2, x_3, x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_72);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_101 = x_96;
} else {
 lean::inc(x_99);
 lean::dec(x_96);
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
obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_105 = x_96;
} else {
 lean::inc(x_103);
 lean::dec(x_96);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_103, 0);
x_108 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 x_110 = x_103;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_103);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_72;
}
lean::cnstr_set(x_111, 0, x_91);
lean::cnstr_set(x_111, 1, x_106);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_108);
if (lean::is_scalar(x_105)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_105;
}
lean::cnstr_set(x_113, 0, x_112);
return x_113;
}
}
}
}
}
}
obj* _init_l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean_expr_mk_sort(x_0);
return x_1;
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
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
x_7 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8(x_4);
x_8 = lean_expr_mk_app(x_2, x_7);
return x_8;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
lean::dec(x_12);
x_16 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_0);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_0);
x_21 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_23 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_20, x_21, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_32 = x_23;
} else {
 lean::inc(x_30);
 lean::dec(x_23);
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
x_34 = lean::cnstr_get(x_23, 0);
lean::inc(x_34);
lean::dec(x_23);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9(x_0, x_16, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_37);
lean::dec(x_18);
x_45 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_47 = x_42;
} else {
 lean::inc(x_45);
 lean::dec(x_42);
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
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_51 = x_42;
} else {
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 x_56 = x_49;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_49);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_52);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_51;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_63; 
x_60 = lean::cnstr_get(x_12, 0);
lean::inc(x_60);
lean::dec(x_12);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; 
x_66 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_68 = x_1;
} else {
 lean::inc(x_66);
 lean::dec(x_1);
 x_68 = lean::box(0);
}
lean::inc(x_0);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_0);
x_71 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_73 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_70, x_71, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_68);
lean::dec(x_66);
x_80 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_82 = x_73;
} else {
 lean::inc(x_80);
 lean::dec(x_73);
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
x_84 = lean::cnstr_get(x_73, 0);
lean::inc(x_84);
lean::dec(x_73);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9(x_0, x_66, x_2, x_3, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_68);
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
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
x_104 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_106 = x_99;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_99);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_68;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_106;
}
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
else
{
obj* x_110; obj* x_112; obj* x_113; obj* x_117; 
x_110 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_112 = x_1;
} else {
 lean::inc(x_110);
 lean::dec(x_1);
 x_112 = lean::box(0);
}
x_113 = lean::cnstr_get(x_63, 0);
lean::inc(x_113);
lean::dec(x_63);
lean::inc(x_3);
x_117 = l_lean_elaborator_to__pexpr___main(x_113, x_2, x_3, x_4);
if (lean::obj_tag(x_117) == 0)
{
obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_110);
lean::dec(x_112);
x_122 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_124 = x_117;
} else {
 lean::inc(x_122);
 lean::dec(x_117);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
return x_125;
}
else
{
obj* x_126; obj* x_129; obj* x_131; obj* x_134; 
x_126 = lean::cnstr_get(x_117, 0);
lean::inc(x_126);
lean::dec(x_117);
x_129 = lean::cnstr_get(x_126, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_126, 1);
lean::inc(x_131);
lean::dec(x_126);
x_134 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9(x_0, x_110, x_2, x_3, x_131);
if (lean::obj_tag(x_134) == 0)
{
obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_112);
lean::dec(x_129);
x_137 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_139 = x_134;
} else {
 lean::inc(x_137);
 lean::dec(x_134);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_137);
return x_140;
}
else
{
obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_141 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_143 = x_134;
} else {
 lean::inc(x_141);
 lean::dec(x_134);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_141, 0);
x_146 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 x_148 = x_141;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::dec(x_141);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_112;
}
lean::cnstr_set(x_149, 0, x_129);
lean::cnstr_set(x_149, 1, x_144);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
if (lean::is_scalar(x_143)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_143;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_24; 
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
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_3);
x_24 = l_lean_elaborator_to__pexpr___main(x_21, x_2, x_3, x_4);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
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
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_37);
lean::dec(x_17);
lean::dec(x_18);
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
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_50 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_52 = x_42;
} else {
 lean::inc(x_50);
 lean::dec(x_42);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_50, 0);
x_55 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_57 = x_50;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_50);
 x_57 = lean::box(0);
}
x_58 = lean::box(0);
x_59 = lean::cnstr_get(x_18, 0);
lean::inc(x_59);
lean::dec(x_18);
x_62 = l_lean_elaborator_mangle__ident(x_59);
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__1;
x_64 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_65 = lean_expr_mk_mdata(x_64, x_37);
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_57)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_57;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_52;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_12);
x_70 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_72 = x_1;
} else {
 lean::inc(x_70);
 lean::dec(x_1);
 x_72 = lean::box(0);
}
lean::inc(x_0);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_0);
x_75 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_77 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_74, x_75, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_70);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_86 = x_77;
} else {
 lean::inc(x_84);
 lean::dec(x_77);
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
obj* x_88; obj* x_91; obj* x_93; obj* x_96; 
x_88 = lean::cnstr_get(x_77, 0);
lean::inc(x_88);
lean::dec(x_77);
x_91 = lean::cnstr_get(x_88, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
x_96 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_70, x_2, x_3, x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_72);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_101 = x_96;
} else {
 lean::inc(x_99);
 lean::dec(x_96);
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
obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_105 = x_96;
} else {
 lean::inc(x_103);
 lean::dec(x_96);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_103, 0);
x_108 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 x_110 = x_103;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_103);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_72;
}
lean::cnstr_set(x_111, 0, x_91);
lean::cnstr_set(x_111, 1, x_106);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_108);
if (lean::is_scalar(x_105)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_105;
}
lean::cnstr_set(x_113, 0, x_112);
return x_113;
}
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
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
x_7 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11(x_4);
x_8 = lean_expr_mk_app(x_2, x_7);
return x_8;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
lean::dec(x_12);
x_16 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_0);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_0);
x_21 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_23 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_20, x_21, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_32 = x_23;
} else {
 lean::inc(x_30);
 lean::dec(x_23);
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
x_34 = lean::cnstr_get(x_23, 0);
lean::inc(x_34);
lean::dec(x_23);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12(x_0, x_16, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_37);
lean::dec(x_18);
x_45 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_47 = x_42;
} else {
 lean::inc(x_45);
 lean::dec(x_42);
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
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_51 = x_42;
} else {
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 x_56 = x_49;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_49);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_52);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_51;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_63; 
x_60 = lean::cnstr_get(x_12, 0);
lean::inc(x_60);
lean::dec(x_12);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; 
x_66 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_68 = x_1;
} else {
 lean::inc(x_66);
 lean::dec(x_1);
 x_68 = lean::box(0);
}
lean::inc(x_0);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_0);
x_71 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_73 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_70, x_71, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_68);
lean::dec(x_66);
x_80 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_82 = x_73;
} else {
 lean::inc(x_80);
 lean::dec(x_73);
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
x_84 = lean::cnstr_get(x_73, 0);
lean::inc(x_84);
lean::dec(x_73);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12(x_0, x_66, x_2, x_3, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_68);
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
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
x_104 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_106 = x_99;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_99);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_68;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_106;
}
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
else
{
obj* x_110; obj* x_112; obj* x_113; obj* x_117; 
x_110 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_112 = x_1;
} else {
 lean::inc(x_110);
 lean::dec(x_1);
 x_112 = lean::box(0);
}
x_113 = lean::cnstr_get(x_63, 0);
lean::inc(x_113);
lean::dec(x_63);
lean::inc(x_3);
x_117 = l_lean_elaborator_to__pexpr___main(x_113, x_2, x_3, x_4);
if (lean::obj_tag(x_117) == 0)
{
obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_110);
lean::dec(x_112);
x_122 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_124 = x_117;
} else {
 lean::inc(x_122);
 lean::dec(x_117);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
return x_125;
}
else
{
obj* x_126; obj* x_129; obj* x_131; obj* x_134; 
x_126 = lean::cnstr_get(x_117, 0);
lean::inc(x_126);
lean::dec(x_117);
x_129 = lean::cnstr_get(x_126, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_126, 1);
lean::inc(x_131);
lean::dec(x_126);
x_134 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12(x_0, x_110, x_2, x_3, x_131);
if (lean::obj_tag(x_134) == 0)
{
obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_112);
lean::dec(x_129);
x_137 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_139 = x_134;
} else {
 lean::inc(x_137);
 lean::dec(x_134);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_137);
return x_140;
}
else
{
obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_141 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_143 = x_134;
} else {
 lean::inc(x_141);
 lean::dec(x_134);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_141, 0);
x_146 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 x_148 = x_141;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::dec(x_141);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_112;
}
lean::cnstr_set(x_149, 0, x_129);
lean::cnstr_set(x_149, 1, x_144);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
if (lean::is_scalar(x_143)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_143;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_24; 
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
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_3);
x_24 = l_lean_elaborator_to__pexpr___main(x_21, x_2, x_3, x_4);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
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
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_37);
lean::dec(x_17);
lean::dec(x_18);
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
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_50 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_52 = x_42;
} else {
 lean::inc(x_50);
 lean::dec(x_42);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_50, 0);
x_55 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_57 = x_50;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_50);
 x_57 = lean::box(0);
}
x_58 = lean::box(0);
x_59 = lean::cnstr_get(x_18, 0);
lean::inc(x_59);
lean::dec(x_18);
x_62 = l_lean_elaborator_mangle__ident(x_59);
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__1;
x_64 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_65 = lean_expr_mk_mdata(x_64, x_37);
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_57)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_57;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_52;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_12);
x_70 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_72 = x_1;
} else {
 lean::inc(x_70);
 lean::dec(x_1);
 x_72 = lean::box(0);
}
lean::inc(x_0);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_0);
x_75 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_77 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_74, x_75, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_70);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_86 = x_77;
} else {
 lean::inc(x_84);
 lean::dec(x_77);
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
obj* x_88; obj* x_91; obj* x_93; obj* x_96; 
x_88 = lean::cnstr_get(x_77, 0);
lean::inc(x_88);
lean::dec(x_77);
x_91 = lean::cnstr_get(x_88, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
x_96 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_70, x_2, x_3, x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_72);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_101 = x_96;
} else {
 lean::inc(x_99);
 lean::dec(x_96);
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
obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_105 = x_96;
} else {
 lean::inc(x_103);
 lean::dec(x_96);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_103, 0);
x_108 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 x_110 = x_103;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_103);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_72;
}
lean::cnstr_set(x_111, 0, x_91);
lean::cnstr_set(x_111, 1, x_106);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_108);
if (lean::is_scalar(x_105)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_105;
}
lean::cnstr_set(x_113, 0, x_112);
return x_113;
}
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
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
x_7 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14(x_4);
x_8 = lean_expr_mk_app(x_2, x_7);
return x_8;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
lean::dec(x_12);
x_16 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_0);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_0);
x_21 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_23 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_20, x_21, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_32 = x_23;
} else {
 lean::inc(x_30);
 lean::dec(x_23);
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
x_34 = lean::cnstr_get(x_23, 0);
lean::inc(x_34);
lean::dec(x_23);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15(x_0, x_16, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_37);
lean::dec(x_18);
x_45 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_47 = x_42;
} else {
 lean::inc(x_45);
 lean::dec(x_42);
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
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_51 = x_42;
} else {
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 x_56 = x_49;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_49);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_52);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_51;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_63; 
x_60 = lean::cnstr_get(x_12, 0);
lean::inc(x_60);
lean::dec(x_12);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; 
x_66 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_68 = x_1;
} else {
 lean::inc(x_66);
 lean::dec(x_1);
 x_68 = lean::box(0);
}
lean::inc(x_0);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_0);
x_71 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_73 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_70, x_71, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_68);
lean::dec(x_66);
x_80 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_82 = x_73;
} else {
 lean::inc(x_80);
 lean::dec(x_73);
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
x_84 = lean::cnstr_get(x_73, 0);
lean::inc(x_84);
lean::dec(x_73);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15(x_0, x_66, x_2, x_3, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_68);
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
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
x_104 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_106 = x_99;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_99);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_68;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_106;
}
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
else
{
obj* x_110; obj* x_112; obj* x_113; obj* x_117; 
x_110 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_112 = x_1;
} else {
 lean::inc(x_110);
 lean::dec(x_1);
 x_112 = lean::box(0);
}
x_113 = lean::cnstr_get(x_63, 0);
lean::inc(x_113);
lean::dec(x_63);
lean::inc(x_3);
x_117 = l_lean_elaborator_to__pexpr___main(x_113, x_2, x_3, x_4);
if (lean::obj_tag(x_117) == 0)
{
obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_110);
lean::dec(x_112);
x_122 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_124 = x_117;
} else {
 lean::inc(x_122);
 lean::dec(x_117);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
return x_125;
}
else
{
obj* x_126; obj* x_129; obj* x_131; obj* x_134; 
x_126 = lean::cnstr_get(x_117, 0);
lean::inc(x_126);
lean::dec(x_117);
x_129 = lean::cnstr_get(x_126, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_126, 1);
lean::inc(x_131);
lean::dec(x_126);
x_134 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15(x_0, x_110, x_2, x_3, x_131);
if (lean::obj_tag(x_134) == 0)
{
obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_112);
lean::dec(x_129);
x_137 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_139 = x_134;
} else {
 lean::inc(x_137);
 lean::dec(x_134);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_137);
return x_140;
}
else
{
obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_141 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_143 = x_134;
} else {
 lean::inc(x_141);
 lean::dec(x_134);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_141, 0);
x_146 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 x_148 = x_141;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::dec(x_141);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_112;
}
lean::cnstr_set(x_149, 0, x_129);
lean::cnstr_set(x_149, 1, x_144);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
if (lean::is_scalar(x_143)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_143;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_24; 
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
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_3);
x_24 = l_lean_elaborator_to__pexpr___main(x_21, x_2, x_3, x_4);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
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
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_37);
lean::dec(x_17);
lean::dec(x_18);
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
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_50 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_52 = x_42;
} else {
 lean::inc(x_50);
 lean::dec(x_42);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_50, 0);
x_55 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_57 = x_50;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_50);
 x_57 = lean::box(0);
}
x_58 = lean::box(0);
x_59 = lean::cnstr_get(x_18, 0);
lean::inc(x_59);
lean::dec(x_18);
x_62 = l_lean_elaborator_mangle__ident(x_59);
x_63 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__1;
x_64 = l_lean_kvmap_set__name(x_58, x_63, x_62);
x_65 = lean_expr_mk_mdata(x_64, x_37);
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_57)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_57;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_52;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_12);
x_70 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_72 = x_1;
} else {
 lean::inc(x_70);
 lean::dec(x_1);
 x_72 = lean::box(0);
}
lean::inc(x_0);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_0);
x_75 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_77 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_74, x_75, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_70);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_86 = x_77;
} else {
 lean::inc(x_84);
 lean::dec(x_77);
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
obj* x_88; obj* x_91; obj* x_93; obj* x_96; 
x_88 = lean::cnstr_get(x_77, 0);
lean::inc(x_88);
lean::dec(x_77);
x_91 = lean::cnstr_get(x_88, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
x_96 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_70, x_2, x_3, x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_72);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_101 = x_96;
} else {
 lean::inc(x_99);
 lean::dec(x_96);
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
obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_105 = x_96;
} else {
 lean::inc(x_103);
 lean::dec(x_96);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_103, 0);
x_108 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 x_110 = x_103;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_103);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_72;
}
lean::cnstr_set(x_111, 0, x_91);
lean::cnstr_set(x_111, 1, x_106);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_108);
if (lean::is_scalar(x_105)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_105;
}
lean::cnstr_set(x_113, 0, x_112);
return x_113;
}
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
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
x_7 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17(x_4);
x_8 = lean_expr_mk_app(x_2, x_7);
return x_8;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
lean::dec(x_12);
x_16 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_0);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_0);
x_21 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_23 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_20, x_21, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_32 = x_23;
} else {
 lean::inc(x_30);
 lean::dec(x_23);
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
x_34 = lean::cnstr_get(x_23, 0);
lean::inc(x_34);
lean::dec(x_23);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18(x_0, x_16, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_37);
lean::dec(x_18);
x_45 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_47 = x_42;
} else {
 lean::inc(x_45);
 lean::dec(x_42);
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
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_51 = x_42;
} else {
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 x_56 = x_49;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_49);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_52);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_51;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_63; 
x_60 = lean::cnstr_get(x_12, 0);
lean::inc(x_60);
lean::dec(x_12);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; 
x_66 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_68 = x_1;
} else {
 lean::inc(x_66);
 lean::dec(x_1);
 x_68 = lean::box(0);
}
lean::inc(x_0);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_0);
x_71 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_3);
x_73 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_70, x_71, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_68);
lean::dec(x_66);
x_80 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_82 = x_73;
} else {
 lean::inc(x_80);
 lean::dec(x_73);
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
x_84 = lean::cnstr_get(x_73, 0);
lean::inc(x_84);
lean::dec(x_73);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18(x_0, x_66, x_2, x_3, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_68);
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
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
x_104 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_106 = x_99;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_99);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_68;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_106;
}
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
else
{
obj* x_110; obj* x_112; obj* x_113; obj* x_117; 
x_110 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_112 = x_1;
} else {
 lean::inc(x_110);
 lean::dec(x_1);
 x_112 = lean::box(0);
}
x_113 = lean::cnstr_get(x_63, 0);
lean::inc(x_113);
lean::dec(x_63);
lean::inc(x_3);
x_117 = l_lean_elaborator_to__pexpr___main(x_113, x_2, x_3, x_4);
if (lean::obj_tag(x_117) == 0)
{
obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_110);
lean::dec(x_112);
x_122 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_124 = x_117;
} else {
 lean::inc(x_122);
 lean::dec(x_117);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
return x_125;
}
else
{
obj* x_126; obj* x_129; obj* x_131; obj* x_134; 
x_126 = lean::cnstr_get(x_117, 0);
lean::inc(x_126);
lean::dec(x_117);
x_129 = lean::cnstr_get(x_126, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_126, 1);
lean::inc(x_131);
lean::dec(x_126);
x_134 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18(x_0, x_110, x_2, x_3, x_131);
if (lean::obj_tag(x_134) == 0)
{
obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_112);
lean::dec(x_129);
x_137 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_139 = x_134;
} else {
 lean::inc(x_137);
 lean::dec(x_134);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_137);
return x_140;
}
else
{
obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_141 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_143 = x_134;
} else {
 lean::inc(x_141);
 lean::dec(x_134);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_141, 0);
x_146 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 x_148 = x_141;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::dec(x_141);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_112;
}
lean::cnstr_set(x_149, 0, x_129);
lean::cnstr_set(x_149, 1, x_144);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
if (lean::is_scalar(x_143)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_143;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_lean_elaborator_to__pexpr___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
x_30 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
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
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__20(obj* x_0, obj* x_1) {
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
x_8 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__20(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
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
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_lean_elaborator_to__level___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
x_30 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
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
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
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
obj* _init_l_lean_elaborator_to__pexpr___main___closed__6() {
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
obj* _init_l_lean_elaborator_to__pexpr___main___closed__7() {
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
x_7 = lean::mk_string("sort_app");
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
x_7 = lean::mk_string("anonymous_constructor");
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
x_7 = lean::mk_string("hole");
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
x_7 = lean::mk_string("have");
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
x_7 = lean::mk_string("show");
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
x_7 = lean::mk_string("let");
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
x_7 = lean::mk_string("projection");
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
x_7 = lean::mk_string("explicit");
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
x_7 = lean::mk_string("inaccessible");
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
x_7 = lean::mk_string("borrowed");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__18() {
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
x_7 = lean::mk_string("struct_inst");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__20() {
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
obj* _init_l_lean_elaborator_to__pexpr___main___closed__21() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("to_pexpr: unexpected node: ");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__22() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("match");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__23() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("structure instance");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__24() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("catchall");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__25() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("struct");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__26() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = l_option_get__or__else___main___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__27() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected item in structure instance notation");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__28() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed choice");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__29() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("choice");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__30() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("NOT_A_STRING");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__31() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("borrowed");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__32() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("innaccessible");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__33() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@@");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__34() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("field_notation");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__35() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed let");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__36() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__37() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean_expr_mk_bvar(x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__38() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("show");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__39() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("have");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__40() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_option_get__or__else___main___rarg(x_3, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__41() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_lean_elaborator_dummy;
x_2 = lean_expr_mk_mvar(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__42() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("anonymous_constructor");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__43() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = level_mk_succ(x_0);
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__44() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed pi");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__45() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed lambda");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__46() {
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
obj* l_lean_elaborator_to__pexpr___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 2:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_17; uint8 x_18; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::dec(x_6);
x_17 = l_lean_elaborator_to__pexpr___main___closed__5;
x_18 = lean_name_dec_eq(x_8, x_17);
if (x_18 == 0)
{
obj* x_19; uint8 x_20; 
x_19 = l_lean_elaborator_to__pexpr___main___closed__2;
x_20 = lean_name_dec_eq(x_8, x_19);
if (x_20 == 0)
{
obj* x_21; uint8 x_22; 
x_21 = l_lean_elaborator_to__pexpr___main___closed__6;
x_22 = lean_name_dec_eq(x_8, x_21);
if (x_22 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = l_lean_elaborator_to__pexpr___main___closed__7;
x_24 = lean_name_dec_eq(x_8, x_23);
if (x_24 == 0)
{
obj* x_25; uint8 x_26; 
x_25 = l_lean_parser_term_sort_has__view_x_27___lambda__1___closed__4;
x_26 = lean_name_dec_eq(x_8, x_25);
if (x_26 == 0)
{
obj* x_27; uint8 x_28; 
x_27 = l_lean_elaborator_to__pexpr___main___closed__8;
x_28 = lean_name_dec_eq(x_8, x_27);
if (x_28 == 0)
{
obj* x_29; uint8 x_30; 
x_29 = l_lean_elaborator_to__pexpr___main___closed__9;
x_30 = lean_name_dec_eq(x_8, x_29);
if (x_30 == 0)
{
obj* x_31; uint8 x_32; 
x_31 = l_lean_elaborator_to__pexpr___main___closed__10;
x_32 = lean_name_dec_eq(x_8, x_31);
if (x_32 == 0)
{
obj* x_33; uint8 x_34; 
x_33 = l_lean_elaborator_to__pexpr___main___closed__11;
x_34 = lean_name_dec_eq(x_8, x_33);
if (x_34 == 0)
{
obj* x_35; uint8 x_36; 
x_35 = l_lean_elaborator_to__pexpr___main___closed__12;
x_36 = lean_name_dec_eq(x_8, x_35);
if (x_36 == 0)
{
obj* x_37; uint8 x_38; 
x_37 = l_lean_elaborator_to__pexpr___main___closed__13;
x_38 = lean_name_dec_eq(x_8, x_37);
if (x_38 == 0)
{
obj* x_39; uint8 x_40; 
x_39 = l_lean_elaborator_to__pexpr___main___closed__14;
x_40 = lean_name_dec_eq(x_8, x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_elaborator_to__pexpr___main___closed__15;
x_42 = lean_name_dec_eq(x_8, x_41);
if (x_42 == 0)
{
obj* x_43; uint8 x_44; 
x_43 = l_lean_elaborator_to__pexpr___main___closed__16;
x_44 = lean_name_dec_eq(x_8, x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_elaborator_to__pexpr___main___closed__17;
x_46 = lean_name_dec_eq(x_8, x_45);
if (x_46 == 0)
{
obj* x_47; uint8 x_48; 
x_47 = l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
x_48 = lean_name_dec_eq(x_8, x_47);
if (x_48 == 0)
{
obj* x_49; uint8 x_50; 
x_49 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
x_50 = lean_name_dec_eq(x_8, x_49);
if (x_50 == 0)
{
obj* x_51; uint8 x_52; 
x_51 = l_lean_elaborator_to__pexpr___main___closed__18;
x_52 = lean_name_dec_eq(x_8, x_51);
if (x_52 == 0)
{
obj* x_54; uint8 x_55; 
lean::dec(x_10);
x_54 = l_lean_elaborator_to__pexpr___main___closed__19;
x_55 = lean_name_dec_eq(x_8, x_54);
if (x_55 == 0)
{
obj* x_56; uint8 x_57; 
x_56 = l_lean_elaborator_to__pexpr___main___closed__20;
x_57 = lean_name_dec_eq(x_8, x_56);
if (x_57 == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_66; 
lean::inc(x_0);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_0);
x_60 = l_lean_name_to__string___closed__1;
x_61 = l_lean_name_to__string__with__sep___main(x_60, x_8);
x_62 = l_lean_elaborator_to__pexpr___main___closed__21;
x_63 = lean::string_append(x_62, x_61);
lean::dec(x_61);
lean::inc(x_2);
x_66 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_59, x_63, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_59);
if (lean::obj_tag(x_66) == 0)
{
obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_0);
lean::dec(x_2);
x_71 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
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
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_77 = x_66;
} else {
 lean::inc(x_75);
 lean::dec(x_66);
 x_77 = lean::box(0);
}
if (x_20 == 0)
{
obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
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
x_83 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_83) == 0)
{
obj* x_86; obj* x_87; 
lean::dec(x_2);
if (lean::is_scalar(x_82)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_82;
}
lean::cnstr_set(x_86, 0, x_78);
lean::cnstr_set(x_86, 1, x_80);
if (lean::is_scalar(x_77)) {
 x_87 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_87 = x_77;
}
lean::cnstr_set(x_87, 0, x_86);
return x_87;
}
else
{
obj* x_88; obj* x_91; obj* x_94; obj* x_97; obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_88 = lean::cnstr_get(x_83, 0);
lean::inc(x_88);
lean::dec(x_83);
x_91 = lean::cnstr_get(x_2, 0);
lean::inc(x_91);
lean::dec(x_2);
x_94 = lean::cnstr_get(x_91, 2);
lean::inc(x_94);
lean::dec(x_91);
x_97 = l_lean_file__map_to__position(x_94, x_88);
x_98 = lean::box(0);
x_99 = lean::cnstr_get(x_97, 1);
lean::inc(x_99);
x_101 = l_lean_elaborator_to__pexpr___main___closed__3;
x_102 = l_lean_kvmap_set__nat(x_98, x_101, x_99);
x_103 = lean::cnstr_get(x_97, 0);
lean::inc(x_103);
lean::dec(x_97);
x_106 = l_lean_elaborator_to__pexpr___main___closed__4;
x_107 = l_lean_kvmap_set__nat(x_102, x_106, x_103);
x_108 = lean_expr_mk_mdata(x_107, x_78);
if (lean::is_scalar(x_82)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_82;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_80);
if (lean::is_scalar(x_77)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_77;
}
lean::cnstr_set(x_110, 0, x_109);
return x_110;
}
}
else
{
obj* x_113; obj* x_115; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_0);
lean::dec(x_2);
x_113 = lean::cnstr_get(x_75, 0);
x_115 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 x_117 = x_75;
} else {
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_75);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_113);
lean::cnstr_set(x_118, 1, x_115);
if (lean::is_scalar(x_77)) {
 x_119 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_119 = x_77;
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
x_128 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__2(x_126);
lean::inc(x_2);
x_130 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3(x_128, x_1, x_2, x_3);
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
x_13 = x_135;
goto lbl_14;
}
else
{
obj* x_136; obj* x_139; obj* x_141; obj* x_144; obj* x_146; obj* x_149; 
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
lean::dec(x_144);
lean::inc(x_2);
x_149 = l_lean_elaborator_to__pexpr___main(x_146, x_1, x_2, x_141);
if (lean::obj_tag(x_149) == 0)
{
obj* x_152; obj* x_154; obj* x_155; 
lean::dec(x_139);
lean::dec(x_125);
x_152 = lean::cnstr_get(x_149, 0);
if (lean::is_exclusive(x_149)) {
 x_154 = x_149;
} else {
 lean::inc(x_152);
 lean::dec(x_149);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_152);
x_13 = x_155;
goto lbl_14;
}
else
{
obj* x_156; obj* x_159; obj* x_161; obj* x_164; 
x_156 = lean::cnstr_get(x_149, 0);
lean::inc(x_156);
lean::dec(x_149);
x_159 = lean::cnstr_get(x_156, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_156, 1);
lean::inc(x_161);
lean::dec(x_156);
x_164 = l_lean_elaborator_mk__eqns(x_159, x_139);
switch (lean::obj_tag(x_164)) {
case 10:
{
obj* x_165; obj* x_167; obj* x_170; obj* x_174; 
x_165 = lean::cnstr_get(x_164, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_164, 1);
lean::inc(x_167);
lean::dec(x_164);
x_170 = lean::cnstr_get(x_125, 1);
lean::inc(x_170);
lean::dec(x_125);
lean::inc(x_2);
x_174 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_170, x_1, x_2, x_161);
if (lean::obj_tag(x_174) == 0)
{
obj* x_177; obj* x_179; obj* x_180; 
lean::dec(x_167);
lean::dec(x_165);
x_177 = lean::cnstr_get(x_174, 0);
if (lean::is_exclusive(x_174)) {
 x_179 = x_174;
} else {
 lean::inc(x_177);
 lean::dec(x_174);
 x_179 = lean::box(0);
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_177);
x_13 = x_180;
goto lbl_14;
}
else
{
obj* x_181; obj* x_183; obj* x_184; obj* x_186; obj* x_188; obj* x_189; uint8 x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
x_181 = lean::cnstr_get(x_174, 0);
if (lean::is_exclusive(x_174)) {
 x_183 = x_174;
} else {
 lean::inc(x_181);
 lean::dec(x_174);
 x_183 = lean::box(0);
}
x_184 = lean::cnstr_get(x_181, 0);
x_186 = lean::cnstr_get(x_181, 1);
if (lean::is_exclusive(x_181)) {
 x_188 = x_181;
} else {
 lean::inc(x_184);
 lean::inc(x_186);
 lean::dec(x_181);
 x_188 = lean::box(0);
}
x_189 = l_lean_elaborator_to__pexpr___main___closed__22;
x_190 = 1;
x_191 = l_lean_kvmap_set__bool(x_165, x_189, x_190);
x_192 = lean_expr_mk_mdata(x_191, x_167);
x_193 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_192, x_184);
if (lean::is_scalar(x_188)) {
 x_194 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_194 = x_188;
}
lean::cnstr_set(x_194, 0, x_193);
lean::cnstr_set(x_194, 1, x_186);
if (lean::is_scalar(x_183)) {
 x_195 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_195 = x_183;
}
lean::cnstr_set(x_195, 0, x_194);
x_13 = x_195;
goto lbl_14;
}
}
default:
{
obj* x_199; obj* x_200; obj* x_202; 
lean::dec(x_164);
lean::dec(x_125);
lean::inc(x_0);
x_199 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_199, 0, x_0);
x_200 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
lean::inc(x_2);
x_202 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_199, x_200, x_1, x_2, x_161);
lean::dec(x_161);
lean::dec(x_199);
x_13 = x_202;
goto lbl_14;
}
}
}
}
}
}
else
{
obj* x_205; obj* x_206; obj* x_210; obj* x_211; obj* x_213; obj* x_214; obj* x_216; obj* x_219; obj* x_220; 
x_205 = l_lean_parser_term_struct__inst_has__view;
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
lean::dec(x_205);
lean::inc(x_0);
x_210 = lean::apply_1(x_206, x_0);
x_211 = lean::cnstr_get(x_210, 3);
lean::inc(x_211);
x_213 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__5(x_211);
x_214 = lean::cnstr_get(x_213, 0);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_213, 1);
lean::inc(x_216);
lean::dec(x_213);
x_219 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_216);
x_220 = lean::cnstr_get(x_219, 1);
lean::inc(x_220);
if (lean::obj_tag(x_220) == 0)
{
obj* x_222; obj* x_227; 
x_222 = lean::cnstr_get(x_219, 0);
lean::inc(x_222);
lean::dec(x_219);
lean::inc(x_2);
lean::inc(x_0);
x_227 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7(x_0, x_214, x_1, x_2, x_3);
if (lean::obj_tag(x_227) == 0)
{
obj* x_233; obj* x_235; obj* x_236; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_222);
lean::dec(x_210);
x_233 = lean::cnstr_get(x_227, 0);
if (lean::is_exclusive(x_227)) {
 x_235 = x_227;
} else {
 lean::inc(x_233);
 lean::dec(x_227);
 x_235 = lean::box(0);
}
if (lean::is_scalar(x_235)) {
 x_236 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_236 = x_235;
}
lean::cnstr_set(x_236, 0, x_233);
return x_236;
}
else
{
obj* x_237; obj* x_240; obj* x_242; obj* x_245; obj* x_249; 
x_237 = lean::cnstr_get(x_227, 0);
lean::inc(x_237);
lean::dec(x_227);
x_240 = lean::cnstr_get(x_237, 0);
lean::inc(x_240);
x_242 = lean::cnstr_get(x_237, 1);
lean::inc(x_242);
lean::dec(x_237);
lean::inc(x_2);
lean::inc(x_0);
x_249 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9(x_0, x_222, x_1, x_2, x_242);
if (lean::obj_tag(x_249) == 0)
{
obj* x_255; obj* x_257; obj* x_258; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_240);
lean::dec(x_210);
x_255 = lean::cnstr_get(x_249, 0);
if (lean::is_exclusive(x_249)) {
 x_257 = x_249;
} else {
 lean::inc(x_255);
 lean::dec(x_249);
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
obj* x_259; obj* x_262; 
x_259 = lean::cnstr_get(x_249, 0);
lean::inc(x_259);
lean::dec(x_249);
x_262 = lean::cnstr_get(x_210, 2);
lean::inc(x_262);
if (lean::obj_tag(x_262) == 0)
{
obj* x_264; obj* x_266; obj* x_268; obj* x_269; 
x_264 = lean::cnstr_get(x_259, 0);
x_266 = lean::cnstr_get(x_259, 1);
if (lean::is_exclusive(x_259)) {
 x_268 = x_259;
} else {
 lean::inc(x_264);
 lean::inc(x_266);
 lean::dec(x_259);
 x_268 = lean::box(0);
}
if (lean::is_scalar(x_268)) {
 x_269 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_269 = x_268;
}
lean::cnstr_set(x_269, 0, x_264);
lean::cnstr_set(x_269, 1, x_266);
x_245 = x_269;
goto lbl_246;
}
else
{
obj* x_270; obj* x_272; obj* x_275; obj* x_278; obj* x_282; 
x_270 = lean::cnstr_get(x_259, 0);
lean::inc(x_270);
x_272 = lean::cnstr_get(x_259, 1);
lean::inc(x_272);
lean::dec(x_259);
x_275 = lean::cnstr_get(x_262, 0);
lean::inc(x_275);
lean::dec(x_262);
x_278 = lean::cnstr_get(x_275, 0);
lean::inc(x_278);
lean::dec(x_275);
lean::inc(x_2);
x_282 = l_lean_elaborator_to__pexpr___main(x_278, x_1, x_2, x_272);
if (lean::obj_tag(x_282) == 0)
{
obj* x_289; obj* x_291; obj* x_292; 
lean::dec(x_270);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_240);
lean::dec(x_210);
x_289 = lean::cnstr_get(x_282, 0);
if (lean::is_exclusive(x_282)) {
 x_291 = x_282;
} else {
 lean::inc(x_289);
 lean::dec(x_282);
 x_291 = lean::box(0);
}
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_289);
return x_292;
}
else
{
obj* x_293; obj* x_296; obj* x_298; obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; 
x_293 = lean::cnstr_get(x_282, 0);
lean::inc(x_293);
lean::dec(x_282);
x_296 = lean::cnstr_get(x_293, 0);
x_298 = lean::cnstr_get(x_293, 1);
if (lean::is_exclusive(x_293)) {
 x_300 = x_293;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_293);
 x_300 = lean::box(0);
}
x_301 = lean::box(0);
x_302 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_302, 0, x_296);
lean::cnstr_set(x_302, 1, x_301);
x_303 = l_list_append___rarg(x_270, x_302);
if (lean::is_scalar(x_300)) {
 x_304 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_304 = x_300;
}
lean::cnstr_set(x_304, 0, x_303);
lean::cnstr_set(x_304, 1, x_298);
x_245 = x_304;
goto lbl_246;
}
}
}
lbl_246:
{
obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; uint8 x_316; obj* x_317; obj* x_318; obj* x_321; obj* x_322; 
x_305 = lean::cnstr_get(x_245, 0);
x_307 = lean::cnstr_get(x_245, 1);
if (lean::is_exclusive(x_245)) {
 lean::cnstr_set(x_245, 0, lean::box(0));
 lean::cnstr_set(x_245, 1, lean::box(0));
 x_309 = x_245;
} else {
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_245);
 x_309 = lean::box(0);
}
x_310 = lean::box(0);
x_311 = lean::mk_nat_obj(0u);
x_312 = l_list_length__aux___main___rarg(x_240, x_311);
x_313 = l_lean_elaborator_to__pexpr___main___closed__23;
x_314 = l_lean_kvmap_set__nat(x_310, x_313, x_312);
x_315 = l_lean_elaborator_to__pexpr___main___closed__24;
x_316 = 0;
x_317 = l_lean_kvmap_set__bool(x_314, x_315, x_316);
x_318 = lean::cnstr_get(x_210, 1);
lean::inc(x_318);
lean::dec(x_210);
x_321 = l_list_append___rarg(x_240, x_305);
x_322 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8(x_321);
if (lean::obj_tag(x_318) == 0)
{
obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; 
x_323 = l_lean_elaborator_to__pexpr___main___closed__25;
x_324 = l_lean_elaborator_to__pexpr___main___closed__26;
x_325 = l_lean_kvmap_set__name(x_317, x_323, x_324);
x_326 = lean_expr_mk_mdata(x_325, x_322);
if (lean::is_scalar(x_309)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_309;
}
lean::cnstr_set(x_327, 0, x_326);
lean::cnstr_set(x_327, 1, x_307);
x_15 = x_327;
goto lbl_16;
}
else
{
obj* x_328; obj* x_330; obj* x_331; obj* x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_339; obj* x_340; obj* x_341; obj* x_342; 
x_328 = lean::cnstr_get(x_318, 0);
if (lean::is_exclusive(x_318)) {
 x_330 = x_318;
} else {
 lean::inc(x_328);
 lean::dec(x_318);
 x_330 = lean::box(0);
}
x_331 = lean::cnstr_get(x_328, 0);
lean::inc(x_331);
lean::dec(x_328);
x_334 = l_lean_elaborator_mangle__ident(x_331);
if (lean::is_scalar(x_330)) {
 x_335 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_335 = x_330;
}
lean::cnstr_set(x_335, 0, x_334);
x_336 = lean::box(0);
x_337 = l_option_get__or__else___main___rarg(x_335, x_336);
lean::dec(x_335);
x_339 = l_lean_elaborator_to__pexpr___main___closed__25;
x_340 = l_lean_kvmap_set__name(x_317, x_339, x_337);
x_341 = lean_expr_mk_mdata(x_340, x_322);
if (lean::is_scalar(x_309)) {
 x_342 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_342 = x_309;
}
lean::cnstr_set(x_342, 0, x_341);
lean::cnstr_set(x_342, 1, x_307);
x_15 = x_342;
goto lbl_16;
}
}
}
}
else
{
obj* x_343; obj* x_345; 
x_343 = lean::cnstr_get(x_220, 0);
lean::inc(x_343);
x_345 = lean::cnstr_get(x_343, 0);
lean::inc(x_345);
lean::dec(x_343);
if (lean::obj_tag(x_345) == 0)
{
obj* x_348; obj* x_349; obj* x_352; obj* x_353; obj* x_356; obj* x_357; obj* x_358; obj* x_360; 
if (lean::is_exclusive(x_220)) {
 lean::cnstr_release(x_220, 0);
 lean::cnstr_release(x_220, 1);
 x_348 = x_220;
} else {
 lean::dec(x_220);
 x_348 = lean::box(0);
}
x_349 = lean::cnstr_get(x_219, 0);
lean::inc(x_349);
lean::dec(x_219);
x_352 = l_lean_parser_term_struct__inst__item_has__view;
x_353 = lean::cnstr_get(x_352, 1);
lean::inc(x_353);
lean::dec(x_352);
x_356 = lean::apply_1(x_353, x_345);
x_357 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_357, 0, x_356);
x_358 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_2);
x_360 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_357, x_358, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_357);
if (lean::obj_tag(x_360) == 0)
{
obj* x_370; obj* x_372; obj* x_373; 
lean::dec(x_349);
lean::dec(x_348);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_214);
lean::dec(x_210);
x_370 = lean::cnstr_get(x_360, 0);
if (lean::is_exclusive(x_360)) {
 x_372 = x_360;
} else {
 lean::inc(x_370);
 lean::dec(x_360);
 x_372 = lean::box(0);
}
if (lean::is_scalar(x_372)) {
 x_373 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_373 = x_372;
}
lean::cnstr_set(x_373, 0, x_370);
return x_373;
}
else
{
obj* x_374; obj* x_377; obj* x_379; obj* x_384; 
x_374 = lean::cnstr_get(x_360, 0);
lean::inc(x_374);
lean::dec(x_360);
x_377 = lean::cnstr_get(x_374, 0);
lean::inc(x_377);
x_379 = lean::cnstr_get(x_374, 1);
lean::inc(x_379);
lean::dec(x_374);
lean::inc(x_2);
lean::inc(x_0);
x_384 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_214, x_1, x_2, x_379);
if (lean::obj_tag(x_384) == 0)
{
obj* x_392; obj* x_394; obj* x_395; 
lean::dec(x_349);
lean::dec(x_348);
lean::dec(x_8);
lean::dec(x_377);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_392 = lean::cnstr_get(x_384, 0);
if (lean::is_exclusive(x_384)) {
 x_394 = x_384;
} else {
 lean::inc(x_392);
 lean::dec(x_384);
 x_394 = lean::box(0);
}
if (lean::is_scalar(x_394)) {
 x_395 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_395 = x_394;
}
lean::cnstr_set(x_395, 0, x_392);
return x_395;
}
else
{
obj* x_396; obj* x_399; obj* x_401; obj* x_404; obj* x_408; 
x_396 = lean::cnstr_get(x_384, 0);
lean::inc(x_396);
lean::dec(x_384);
x_399 = lean::cnstr_get(x_396, 0);
lean::inc(x_399);
x_401 = lean::cnstr_get(x_396, 1);
lean::inc(x_401);
lean::dec(x_396);
lean::inc(x_2);
lean::inc(x_0);
x_408 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12(x_0, x_349, x_1, x_2, x_401);
if (lean::obj_tag(x_408) == 0)
{
obj* x_416; obj* x_418; obj* x_419; 
lean::dec(x_348);
lean::dec(x_8);
lean::dec(x_377);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_399);
lean::dec(x_210);
x_416 = lean::cnstr_get(x_408, 0);
if (lean::is_exclusive(x_408)) {
 x_418 = x_408;
} else {
 lean::inc(x_416);
 lean::dec(x_408);
 x_418 = lean::box(0);
}
if (lean::is_scalar(x_418)) {
 x_419 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_419 = x_418;
}
lean::cnstr_set(x_419, 0, x_416);
return x_419;
}
else
{
obj* x_420; obj* x_423; 
x_420 = lean::cnstr_get(x_408, 0);
lean::inc(x_420);
lean::dec(x_408);
x_423 = lean::cnstr_get(x_210, 2);
lean::inc(x_423);
if (lean::obj_tag(x_423) == 0)
{
obj* x_426; obj* x_428; obj* x_430; obj* x_431; 
lean::dec(x_348);
x_426 = lean::cnstr_get(x_420, 0);
x_428 = lean::cnstr_get(x_420, 1);
if (lean::is_exclusive(x_420)) {
 x_430 = x_420;
} else {
 lean::inc(x_426);
 lean::inc(x_428);
 lean::dec(x_420);
 x_430 = lean::box(0);
}
if (lean::is_scalar(x_430)) {
 x_431 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_431 = x_430;
}
lean::cnstr_set(x_431, 0, x_426);
lean::cnstr_set(x_431, 1, x_428);
x_404 = x_431;
goto lbl_405;
}
else
{
obj* x_432; obj* x_434; obj* x_437; obj* x_440; obj* x_444; 
x_432 = lean::cnstr_get(x_420, 0);
lean::inc(x_432);
x_434 = lean::cnstr_get(x_420, 1);
lean::inc(x_434);
lean::dec(x_420);
x_437 = lean::cnstr_get(x_423, 0);
lean::inc(x_437);
lean::dec(x_423);
x_440 = lean::cnstr_get(x_437, 0);
lean::inc(x_440);
lean::dec(x_437);
lean::inc(x_2);
x_444 = l_lean_elaborator_to__pexpr___main(x_440, x_1, x_2, x_434);
if (lean::obj_tag(x_444) == 0)
{
obj* x_453; obj* x_455; obj* x_456; 
lean::dec(x_348);
lean::dec(x_8);
lean::dec(x_377);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_432);
lean::dec(x_399);
lean::dec(x_210);
x_453 = lean::cnstr_get(x_444, 0);
if (lean::is_exclusive(x_444)) {
 x_455 = x_444;
} else {
 lean::inc(x_453);
 lean::dec(x_444);
 x_455 = lean::box(0);
}
if (lean::is_scalar(x_455)) {
 x_456 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_456 = x_455;
}
lean::cnstr_set(x_456, 0, x_453);
return x_456;
}
else
{
obj* x_457; obj* x_460; obj* x_462; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; 
x_457 = lean::cnstr_get(x_444, 0);
lean::inc(x_457);
lean::dec(x_444);
x_460 = lean::cnstr_get(x_457, 0);
x_462 = lean::cnstr_get(x_457, 1);
if (lean::is_exclusive(x_457)) {
 x_464 = x_457;
} else {
 lean::inc(x_460);
 lean::inc(x_462);
 lean::dec(x_457);
 x_464 = lean::box(0);
}
x_465 = lean::box(0);
if (lean::is_scalar(x_348)) {
 x_466 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_466 = x_348;
}
lean::cnstr_set(x_466, 0, x_460);
lean::cnstr_set(x_466, 1, x_465);
x_467 = l_list_append___rarg(x_432, x_466);
if (lean::is_scalar(x_464)) {
 x_468 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_468 = x_464;
}
lean::cnstr_set(x_468, 0, x_467);
lean::cnstr_set(x_468, 1, x_462);
x_404 = x_468;
goto lbl_405;
}
}
}
lbl_405:
{
obj* x_469; obj* x_471; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; uint8 x_480; obj* x_481; obj* x_482; obj* x_485; obj* x_486; 
x_469 = lean::cnstr_get(x_404, 0);
x_471 = lean::cnstr_get(x_404, 1);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_set(x_404, 0, lean::box(0));
 lean::cnstr_set(x_404, 1, lean::box(0));
 x_473 = x_404;
} else {
 lean::inc(x_469);
 lean::inc(x_471);
 lean::dec(x_404);
 x_473 = lean::box(0);
}
x_474 = lean::box(0);
x_475 = lean::mk_nat_obj(0u);
x_476 = l_list_length__aux___main___rarg(x_399, x_475);
x_477 = l_lean_elaborator_to__pexpr___main___closed__23;
x_478 = l_lean_kvmap_set__nat(x_474, x_477, x_476);
x_479 = l_lean_elaborator_to__pexpr___main___closed__24;
x_480 = lean::unbox(x_377);
x_481 = l_lean_kvmap_set__bool(x_478, x_479, x_480);
x_482 = lean::cnstr_get(x_210, 1);
lean::inc(x_482);
lean::dec(x_210);
x_485 = l_list_append___rarg(x_399, x_469);
x_486 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11(x_485);
if (lean::obj_tag(x_482) == 0)
{
obj* x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; 
x_487 = l_lean_elaborator_to__pexpr___main___closed__25;
x_488 = l_lean_elaborator_to__pexpr___main___closed__26;
x_489 = l_lean_kvmap_set__name(x_481, x_487, x_488);
x_490 = lean_expr_mk_mdata(x_489, x_486);
if (lean::is_scalar(x_473)) {
 x_491 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_491 = x_473;
}
lean::cnstr_set(x_491, 0, x_490);
lean::cnstr_set(x_491, 1, x_471);
x_15 = x_491;
goto lbl_16;
}
else
{
obj* x_492; obj* x_494; obj* x_495; obj* x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_503; obj* x_504; obj* x_505; obj* x_506; 
x_492 = lean::cnstr_get(x_482, 0);
if (lean::is_exclusive(x_482)) {
 x_494 = x_482;
} else {
 lean::inc(x_492);
 lean::dec(x_482);
 x_494 = lean::box(0);
}
x_495 = lean::cnstr_get(x_492, 0);
lean::inc(x_495);
lean::dec(x_492);
x_498 = l_lean_elaborator_mangle__ident(x_495);
if (lean::is_scalar(x_494)) {
 x_499 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_499 = x_494;
}
lean::cnstr_set(x_499, 0, x_498);
x_500 = lean::box(0);
x_501 = l_option_get__or__else___main___rarg(x_499, x_500);
lean::dec(x_499);
x_503 = l_lean_elaborator_to__pexpr___main___closed__25;
x_504 = l_lean_kvmap_set__name(x_481, x_503, x_501);
x_505 = lean_expr_mk_mdata(x_504, x_486);
if (lean::is_scalar(x_473)) {
 x_506 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_506 = x_473;
}
lean::cnstr_set(x_506, 0, x_505);
lean::cnstr_set(x_506, 1, x_471);
x_15 = x_506;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_507; obj* x_509; 
x_507 = lean::cnstr_get(x_220, 1);
if (lean::is_exclusive(x_220)) {
 lean::cnstr_release(x_220, 0);
 lean::cnstr_set(x_220, 1, lean::box(0));
 x_509 = x_220;
} else {
 lean::inc(x_507);
 lean::dec(x_220);
 x_509 = lean::box(0);
}
if (lean::obj_tag(x_507) == 0)
{
obj* x_511; obj* x_516; 
lean::dec(x_345);
x_511 = lean::cnstr_get(x_219, 0);
lean::inc(x_511);
lean::dec(x_219);
lean::inc(x_2);
lean::inc(x_0);
x_516 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_214, x_1, x_2, x_3);
if (lean::obj_tag(x_516) == 0)
{
obj* x_523; obj* x_525; obj* x_526; 
lean::dec(x_511);
lean::dec(x_509);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_523 = lean::cnstr_get(x_516, 0);
if (lean::is_exclusive(x_516)) {
 x_525 = x_516;
} else {
 lean::inc(x_523);
 lean::dec(x_516);
 x_525 = lean::box(0);
}
if (lean::is_scalar(x_525)) {
 x_526 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_526 = x_525;
}
lean::cnstr_set(x_526, 0, x_523);
return x_526;
}
else
{
obj* x_527; obj* x_530; obj* x_532; obj* x_535; obj* x_539; 
x_527 = lean::cnstr_get(x_516, 0);
lean::inc(x_527);
lean::dec(x_516);
x_530 = lean::cnstr_get(x_527, 0);
lean::inc(x_530);
x_532 = lean::cnstr_get(x_527, 1);
lean::inc(x_532);
lean::dec(x_527);
lean::inc(x_2);
lean::inc(x_0);
x_539 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15(x_0, x_511, x_1, x_2, x_532);
if (lean::obj_tag(x_539) == 0)
{
obj* x_546; obj* x_548; obj* x_549; 
lean::dec(x_509);
lean::dec(x_530);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_546 = lean::cnstr_get(x_539, 0);
if (lean::is_exclusive(x_539)) {
 x_548 = x_539;
} else {
 lean::inc(x_546);
 lean::dec(x_539);
 x_548 = lean::box(0);
}
if (lean::is_scalar(x_548)) {
 x_549 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_549 = x_548;
}
lean::cnstr_set(x_549, 0, x_546);
return x_549;
}
else
{
obj* x_550; obj* x_553; 
x_550 = lean::cnstr_get(x_539, 0);
lean::inc(x_550);
lean::dec(x_539);
x_553 = lean::cnstr_get(x_210, 2);
lean::inc(x_553);
if (lean::obj_tag(x_553) == 0)
{
obj* x_556; obj* x_558; obj* x_560; obj* x_561; 
lean::dec(x_509);
x_556 = lean::cnstr_get(x_550, 0);
x_558 = lean::cnstr_get(x_550, 1);
if (lean::is_exclusive(x_550)) {
 x_560 = x_550;
} else {
 lean::inc(x_556);
 lean::inc(x_558);
 lean::dec(x_550);
 x_560 = lean::box(0);
}
if (lean::is_scalar(x_560)) {
 x_561 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_561 = x_560;
}
lean::cnstr_set(x_561, 0, x_556);
lean::cnstr_set(x_561, 1, x_558);
x_535 = x_561;
goto lbl_536;
}
else
{
obj* x_562; obj* x_564; obj* x_567; obj* x_570; obj* x_574; 
x_562 = lean::cnstr_get(x_550, 0);
lean::inc(x_562);
x_564 = lean::cnstr_get(x_550, 1);
lean::inc(x_564);
lean::dec(x_550);
x_567 = lean::cnstr_get(x_553, 0);
lean::inc(x_567);
lean::dec(x_553);
x_570 = lean::cnstr_get(x_567, 0);
lean::inc(x_570);
lean::dec(x_567);
lean::inc(x_2);
x_574 = l_lean_elaborator_to__pexpr___main(x_570, x_1, x_2, x_564);
if (lean::obj_tag(x_574) == 0)
{
obj* x_582; obj* x_584; obj* x_585; 
lean::dec(x_562);
lean::dec(x_509);
lean::dec(x_530);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_582 = lean::cnstr_get(x_574, 0);
if (lean::is_exclusive(x_574)) {
 x_584 = x_574;
} else {
 lean::inc(x_582);
 lean::dec(x_574);
 x_584 = lean::box(0);
}
if (lean::is_scalar(x_584)) {
 x_585 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_585 = x_584;
}
lean::cnstr_set(x_585, 0, x_582);
return x_585;
}
else
{
obj* x_586; obj* x_589; obj* x_591; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_597; 
x_586 = lean::cnstr_get(x_574, 0);
lean::inc(x_586);
lean::dec(x_574);
x_589 = lean::cnstr_get(x_586, 0);
x_591 = lean::cnstr_get(x_586, 1);
if (lean::is_exclusive(x_586)) {
 x_593 = x_586;
} else {
 lean::inc(x_589);
 lean::inc(x_591);
 lean::dec(x_586);
 x_593 = lean::box(0);
}
x_594 = lean::box(0);
if (lean::is_scalar(x_509)) {
 x_595 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_595 = x_509;
}
lean::cnstr_set(x_595, 0, x_589);
lean::cnstr_set(x_595, 1, x_594);
x_596 = l_list_append___rarg(x_562, x_595);
if (lean::is_scalar(x_593)) {
 x_597 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_597 = x_593;
}
lean::cnstr_set(x_597, 0, x_596);
lean::cnstr_set(x_597, 1, x_591);
x_535 = x_597;
goto lbl_536;
}
}
}
lbl_536:
{
obj* x_598; obj* x_600; obj* x_602; obj* x_603; obj* x_604; obj* x_605; obj* x_606; obj* x_607; obj* x_608; uint8 x_609; obj* x_610; obj* x_611; obj* x_614; obj* x_615; 
x_598 = lean::cnstr_get(x_535, 0);
x_600 = lean::cnstr_get(x_535, 1);
if (lean::is_exclusive(x_535)) {
 lean::cnstr_set(x_535, 0, lean::box(0));
 lean::cnstr_set(x_535, 1, lean::box(0));
 x_602 = x_535;
} else {
 lean::inc(x_598);
 lean::inc(x_600);
 lean::dec(x_535);
 x_602 = lean::box(0);
}
x_603 = lean::box(0);
x_604 = lean::mk_nat_obj(0u);
x_605 = l_list_length__aux___main___rarg(x_530, x_604);
x_606 = l_lean_elaborator_to__pexpr___main___closed__23;
x_607 = l_lean_kvmap_set__nat(x_603, x_606, x_605);
x_608 = l_lean_elaborator_to__pexpr___main___closed__24;
x_609 = 1;
x_610 = l_lean_kvmap_set__bool(x_607, x_608, x_609);
x_611 = lean::cnstr_get(x_210, 1);
lean::inc(x_611);
lean::dec(x_210);
x_614 = l_list_append___rarg(x_530, x_598);
x_615 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14(x_614);
if (lean::obj_tag(x_611) == 0)
{
obj* x_616; obj* x_617; obj* x_618; obj* x_619; obj* x_620; 
x_616 = l_lean_elaborator_to__pexpr___main___closed__25;
x_617 = l_lean_elaborator_to__pexpr___main___closed__26;
x_618 = l_lean_kvmap_set__name(x_610, x_616, x_617);
x_619 = lean_expr_mk_mdata(x_618, x_615);
if (lean::is_scalar(x_602)) {
 x_620 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_620 = x_602;
}
lean::cnstr_set(x_620, 0, x_619);
lean::cnstr_set(x_620, 1, x_600);
x_15 = x_620;
goto lbl_16;
}
else
{
obj* x_621; obj* x_623; obj* x_624; obj* x_627; obj* x_628; obj* x_629; obj* x_630; obj* x_632; obj* x_633; obj* x_634; obj* x_635; 
x_621 = lean::cnstr_get(x_611, 0);
if (lean::is_exclusive(x_611)) {
 x_623 = x_611;
} else {
 lean::inc(x_621);
 lean::dec(x_611);
 x_623 = lean::box(0);
}
x_624 = lean::cnstr_get(x_621, 0);
lean::inc(x_624);
lean::dec(x_621);
x_627 = l_lean_elaborator_mangle__ident(x_624);
if (lean::is_scalar(x_623)) {
 x_628 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_628 = x_623;
}
lean::cnstr_set(x_628, 0, x_627);
x_629 = lean::box(0);
x_630 = l_option_get__or__else___main___rarg(x_628, x_629);
lean::dec(x_628);
x_632 = l_lean_elaborator_to__pexpr___main___closed__25;
x_633 = l_lean_kvmap_set__name(x_610, x_632, x_630);
x_634 = lean_expr_mk_mdata(x_633, x_615);
if (lean::is_scalar(x_602)) {
 x_635 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_635 = x_602;
}
lean::cnstr_set(x_635, 0, x_634);
lean::cnstr_set(x_635, 1, x_600);
x_15 = x_635;
goto lbl_16;
}
}
}
}
else
{
obj* x_637; obj* x_638; obj* x_641; obj* x_642; obj* x_645; obj* x_646; obj* x_647; obj* x_649; 
lean::dec(x_509);
if (lean::is_exclusive(x_507)) {
 lean::cnstr_release(x_507, 0);
 lean::cnstr_release(x_507, 1);
 x_637 = x_507;
} else {
 lean::dec(x_507);
 x_637 = lean::box(0);
}
x_638 = lean::cnstr_get(x_219, 0);
lean::inc(x_638);
lean::dec(x_219);
x_641 = l_lean_parser_term_struct__inst__item_has__view;
x_642 = lean::cnstr_get(x_641, 1);
lean::inc(x_642);
lean::dec(x_641);
x_645 = lean::apply_1(x_642, x_345);
x_646 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_646, 0, x_645);
x_647 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_2);
x_649 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_646, x_647, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_646);
if (lean::obj_tag(x_649) == 0)
{
obj* x_659; obj* x_661; obj* x_662; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_638);
lean::dec(x_637);
lean::dec(x_214);
lean::dec(x_210);
x_659 = lean::cnstr_get(x_649, 0);
if (lean::is_exclusive(x_649)) {
 x_661 = x_649;
} else {
 lean::inc(x_659);
 lean::dec(x_649);
 x_661 = lean::box(0);
}
if (lean::is_scalar(x_661)) {
 x_662 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_662 = x_661;
}
lean::cnstr_set(x_662, 0, x_659);
return x_662;
}
else
{
obj* x_663; obj* x_666; obj* x_668; obj* x_673; 
x_663 = lean::cnstr_get(x_649, 0);
lean::inc(x_663);
lean::dec(x_649);
x_666 = lean::cnstr_get(x_663, 0);
lean::inc(x_666);
x_668 = lean::cnstr_get(x_663, 1);
lean::inc(x_668);
lean::dec(x_663);
lean::inc(x_2);
lean::inc(x_0);
x_673 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_214, x_1, x_2, x_668);
if (lean::obj_tag(x_673) == 0)
{
obj* x_681; obj* x_683; obj* x_684; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_638);
lean::dec(x_637);
lean::dec(x_666);
lean::dec(x_210);
x_681 = lean::cnstr_get(x_673, 0);
if (lean::is_exclusive(x_673)) {
 x_683 = x_673;
} else {
 lean::inc(x_681);
 lean::dec(x_673);
 x_683 = lean::box(0);
}
if (lean::is_scalar(x_683)) {
 x_684 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_684 = x_683;
}
lean::cnstr_set(x_684, 0, x_681);
return x_684;
}
else
{
obj* x_685; obj* x_688; obj* x_690; obj* x_693; obj* x_697; 
x_685 = lean::cnstr_get(x_673, 0);
lean::inc(x_685);
lean::dec(x_673);
x_688 = lean::cnstr_get(x_685, 0);
lean::inc(x_688);
x_690 = lean::cnstr_get(x_685, 1);
lean::inc(x_690);
lean::dec(x_685);
lean::inc(x_2);
lean::inc(x_0);
x_697 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18(x_0, x_638, x_1, x_2, x_690);
if (lean::obj_tag(x_697) == 0)
{
obj* x_705; obj* x_707; obj* x_708; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_637);
lean::dec(x_666);
lean::dec(x_688);
lean::dec(x_210);
x_705 = lean::cnstr_get(x_697, 0);
if (lean::is_exclusive(x_697)) {
 x_707 = x_697;
} else {
 lean::inc(x_705);
 lean::dec(x_697);
 x_707 = lean::box(0);
}
if (lean::is_scalar(x_707)) {
 x_708 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_708 = x_707;
}
lean::cnstr_set(x_708, 0, x_705);
return x_708;
}
else
{
obj* x_709; obj* x_712; 
x_709 = lean::cnstr_get(x_697, 0);
lean::inc(x_709);
lean::dec(x_697);
x_712 = lean::cnstr_get(x_210, 2);
lean::inc(x_712);
if (lean::obj_tag(x_712) == 0)
{
obj* x_715; obj* x_717; obj* x_719; obj* x_720; 
lean::dec(x_637);
x_715 = lean::cnstr_get(x_709, 0);
x_717 = lean::cnstr_get(x_709, 1);
if (lean::is_exclusive(x_709)) {
 x_719 = x_709;
} else {
 lean::inc(x_715);
 lean::inc(x_717);
 lean::dec(x_709);
 x_719 = lean::box(0);
}
if (lean::is_scalar(x_719)) {
 x_720 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_720 = x_719;
}
lean::cnstr_set(x_720, 0, x_715);
lean::cnstr_set(x_720, 1, x_717);
x_693 = x_720;
goto lbl_694;
}
else
{
obj* x_721; obj* x_723; obj* x_726; obj* x_729; obj* x_733; 
x_721 = lean::cnstr_get(x_709, 0);
lean::inc(x_721);
x_723 = lean::cnstr_get(x_709, 1);
lean::inc(x_723);
lean::dec(x_709);
x_726 = lean::cnstr_get(x_712, 0);
lean::inc(x_726);
lean::dec(x_712);
x_729 = lean::cnstr_get(x_726, 0);
lean::inc(x_729);
lean::dec(x_726);
lean::inc(x_2);
x_733 = l_lean_elaborator_to__pexpr___main(x_729, x_1, x_2, x_723);
if (lean::obj_tag(x_733) == 0)
{
obj* x_742; obj* x_744; obj* x_745; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_637);
lean::dec(x_666);
lean::dec(x_721);
lean::dec(x_688);
lean::dec(x_210);
x_742 = lean::cnstr_get(x_733, 0);
if (lean::is_exclusive(x_733)) {
 x_744 = x_733;
} else {
 lean::inc(x_742);
 lean::dec(x_733);
 x_744 = lean::box(0);
}
if (lean::is_scalar(x_744)) {
 x_745 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_745 = x_744;
}
lean::cnstr_set(x_745, 0, x_742);
return x_745;
}
else
{
obj* x_746; obj* x_749; obj* x_751; obj* x_753; obj* x_754; obj* x_755; obj* x_756; obj* x_757; 
x_746 = lean::cnstr_get(x_733, 0);
lean::inc(x_746);
lean::dec(x_733);
x_749 = lean::cnstr_get(x_746, 0);
x_751 = lean::cnstr_get(x_746, 1);
if (lean::is_exclusive(x_746)) {
 x_753 = x_746;
} else {
 lean::inc(x_749);
 lean::inc(x_751);
 lean::dec(x_746);
 x_753 = lean::box(0);
}
x_754 = lean::box(0);
if (lean::is_scalar(x_637)) {
 x_755 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_755 = x_637;
}
lean::cnstr_set(x_755, 0, x_749);
lean::cnstr_set(x_755, 1, x_754);
x_756 = l_list_append___rarg(x_721, x_755);
if (lean::is_scalar(x_753)) {
 x_757 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_757 = x_753;
}
lean::cnstr_set(x_757, 0, x_756);
lean::cnstr_set(x_757, 1, x_751);
x_693 = x_757;
goto lbl_694;
}
}
}
lbl_694:
{
obj* x_758; obj* x_760; obj* x_762; obj* x_763; obj* x_764; obj* x_765; obj* x_766; obj* x_767; obj* x_768; uint8 x_769; obj* x_770; obj* x_771; obj* x_774; obj* x_775; 
x_758 = lean::cnstr_get(x_693, 0);
x_760 = lean::cnstr_get(x_693, 1);
if (lean::is_exclusive(x_693)) {
 lean::cnstr_set(x_693, 0, lean::box(0));
 lean::cnstr_set(x_693, 1, lean::box(0));
 x_762 = x_693;
} else {
 lean::inc(x_758);
 lean::inc(x_760);
 lean::dec(x_693);
 x_762 = lean::box(0);
}
x_763 = lean::box(0);
x_764 = lean::mk_nat_obj(0u);
x_765 = l_list_length__aux___main___rarg(x_688, x_764);
x_766 = l_lean_elaborator_to__pexpr___main___closed__23;
x_767 = l_lean_kvmap_set__nat(x_763, x_766, x_765);
x_768 = l_lean_elaborator_to__pexpr___main___closed__24;
x_769 = lean::unbox(x_666);
x_770 = l_lean_kvmap_set__bool(x_767, x_768, x_769);
x_771 = lean::cnstr_get(x_210, 1);
lean::inc(x_771);
lean::dec(x_210);
x_774 = l_list_append___rarg(x_688, x_758);
x_775 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17(x_774);
if (lean::obj_tag(x_771) == 0)
{
obj* x_776; obj* x_777; obj* x_778; obj* x_779; obj* x_780; 
x_776 = l_lean_elaborator_to__pexpr___main___closed__25;
x_777 = l_lean_elaborator_to__pexpr___main___closed__26;
x_778 = l_lean_kvmap_set__name(x_770, x_776, x_777);
x_779 = lean_expr_mk_mdata(x_778, x_775);
if (lean::is_scalar(x_762)) {
 x_780 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_780 = x_762;
}
lean::cnstr_set(x_780, 0, x_779);
lean::cnstr_set(x_780, 1, x_760);
x_15 = x_780;
goto lbl_16;
}
else
{
obj* x_781; obj* x_783; obj* x_784; obj* x_787; obj* x_788; obj* x_789; obj* x_790; obj* x_792; obj* x_793; obj* x_794; obj* x_795; 
x_781 = lean::cnstr_get(x_771, 0);
if (lean::is_exclusive(x_771)) {
 x_783 = x_771;
} else {
 lean::inc(x_781);
 lean::dec(x_771);
 x_783 = lean::box(0);
}
x_784 = lean::cnstr_get(x_781, 0);
lean::inc(x_784);
lean::dec(x_781);
x_787 = l_lean_elaborator_mangle__ident(x_784);
if (lean::is_scalar(x_783)) {
 x_788 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_788 = x_783;
}
lean::cnstr_set(x_788, 0, x_787);
x_789 = lean::box(0);
x_790 = l_option_get__or__else___main___rarg(x_788, x_789);
lean::dec(x_788);
x_792 = l_lean_elaborator_to__pexpr___main___closed__25;
x_793 = l_lean_kvmap_set__name(x_770, x_792, x_790);
x_794 = lean_expr_mk_mdata(x_793, x_775);
if (lean::is_scalar(x_762)) {
 x_795 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_795 = x_762;
}
lean::cnstr_set(x_795, 0, x_794);
lean::cnstr_set(x_795, 1, x_760);
x_15 = x_795;
goto lbl_16;
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
obj* x_798; 
lean::inc(x_2);
lean::inc(x_10);
x_798 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_798) == 0)
{
obj* x_803; obj* x_805; obj* x_806; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_2);
x_803 = lean::cnstr_get(x_798, 0);
if (lean::is_exclusive(x_798)) {
 x_805 = x_798;
} else {
 lean::inc(x_803);
 lean::dec(x_798);
 x_805 = lean::box(0);
}
if (lean::is_scalar(x_805)) {
 x_806 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_806 = x_805;
}
lean::cnstr_set(x_806, 0, x_803);
return x_806;
}
else
{
obj* x_807; obj* x_810; obj* x_812; obj* x_814; obj* x_815; 
x_807 = lean::cnstr_get(x_798, 0);
lean::inc(x_807);
lean::dec(x_798);
x_810 = lean::cnstr_get(x_807, 0);
x_812 = lean::cnstr_get(x_807, 1);
if (lean::is_exclusive(x_807)) {
 lean::cnstr_set(x_807, 0, lean::box(0));
 lean::cnstr_set(x_807, 1, lean::box(0));
 x_814 = x_807;
} else {
 lean::inc(x_810);
 lean::inc(x_812);
 lean::dec(x_807);
 x_814 = lean::box(0);
}
x_815 = l_list_reverse___rarg(x_810);
if (lean::obj_tag(x_815) == 0)
{
obj* x_819; obj* x_820; obj* x_822; 
lean::dec(x_10);
lean::dec(x_814);
lean::inc(x_0);
x_819 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_819, 0, x_0);
x_820 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_2);
x_822 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_819, x_820, x_1, x_2, x_812);
lean::dec(x_812);
lean::dec(x_819);
if (lean::obj_tag(x_822) == 0)
{
obj* x_828; obj* x_830; obj* x_831; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_828 = lean::cnstr_get(x_822, 0);
if (lean::is_exclusive(x_822)) {
 x_830 = x_822;
} else {
 lean::inc(x_828);
 lean::dec(x_822);
 x_830 = lean::box(0);
}
if (lean::is_scalar(x_830)) {
 x_831 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_831 = x_830;
}
lean::cnstr_set(x_831, 0, x_828);
return x_831;
}
else
{
obj* x_832; 
x_832 = lean::cnstr_get(x_822, 0);
lean::inc(x_832);
lean::dec(x_822);
x_15 = x_832;
goto lbl_16;
}
}
else
{
obj* x_835; obj* x_837; obj* x_840; obj* x_841; obj* x_842; obj* x_844; obj* x_845; obj* x_846; obj* x_847; obj* x_849; obj* x_850; 
x_835 = lean::cnstr_get(x_815, 0);
lean::inc(x_835);
x_837 = lean::cnstr_get(x_815, 1);
lean::inc(x_837);
lean::dec(x_815);
x_840 = lean::box(0);
x_841 = lean::mk_nat_obj(0u);
x_842 = l_list_length__aux___main___rarg(x_10, x_841);
lean::dec(x_10);
x_844 = l_lean_elaborator_to__pexpr___main___closed__29;
x_845 = l_lean_kvmap_set__nat(x_840, x_844, x_842);
x_846 = l_list_reverse___rarg(x_837);
x_847 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__20(x_835, x_846);
lean::dec(x_835);
x_849 = lean_expr_mk_mdata(x_845, x_847);
if (lean::is_scalar(x_814)) {
 x_850 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_850 = x_814;
}
lean::cnstr_set(x_850, 0, x_849);
lean::cnstr_set(x_850, 1, x_812);
x_15 = x_850;
goto lbl_16;
}
}
}
}
else
{
obj* x_853; obj* x_854; obj* x_858; obj* x_859; obj* x_860; obj* x_861; obj* x_863; obj* x_864; 
lean::dec(x_8);
lean::dec(x_10);
x_853 = l_lean_parser_string__lit_has__view;
x_854 = lean::cnstr_get(x_853, 0);
lean::inc(x_854);
lean::dec(x_853);
lean::inc(x_0);
x_858 = lean::apply_1(x_854, x_0);
x_859 = l_lean_parser_string__lit_view_value(x_858);
x_860 = l_lean_elaborator_to__pexpr___main___closed__30;
x_861 = l_option_get__or__else___main___rarg(x_859, x_860);
lean::dec(x_859);
x_863 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_863, 0, x_861);
x_864 = lean_expr_mk_lit(x_863);
if (x_20 == 0)
{
obj* x_865; 
x_865 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_865) == 0)
{
obj* x_868; obj* x_869; 
lean::dec(x_2);
x_868 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_868, 0, x_864);
lean::cnstr_set(x_868, 1, x_3);
x_869 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_869, 0, x_868);
return x_869;
}
else
{
obj* x_870; obj* x_873; obj* x_876; obj* x_879; obj* x_880; obj* x_881; obj* x_883; obj* x_884; obj* x_885; obj* x_888; obj* x_889; obj* x_890; obj* x_891; obj* x_892; 
x_870 = lean::cnstr_get(x_865, 0);
lean::inc(x_870);
lean::dec(x_865);
x_873 = lean::cnstr_get(x_2, 0);
lean::inc(x_873);
lean::dec(x_2);
x_876 = lean::cnstr_get(x_873, 2);
lean::inc(x_876);
lean::dec(x_873);
x_879 = l_lean_file__map_to__position(x_876, x_870);
x_880 = lean::box(0);
x_881 = lean::cnstr_get(x_879, 1);
lean::inc(x_881);
x_883 = l_lean_elaborator_to__pexpr___main___closed__3;
x_884 = l_lean_kvmap_set__nat(x_880, x_883, x_881);
x_885 = lean::cnstr_get(x_879, 0);
lean::inc(x_885);
lean::dec(x_879);
x_888 = l_lean_elaborator_to__pexpr___main___closed__4;
x_889 = l_lean_kvmap_set__nat(x_884, x_888, x_885);
x_890 = lean_expr_mk_mdata(x_889, x_864);
x_891 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_891, 0, x_890);
lean::cnstr_set(x_891, 1, x_3);
x_892 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_892, 0, x_891);
return x_892;
}
}
else
{
obj* x_895; obj* x_896; 
lean::dec(x_0);
lean::dec(x_2);
x_895 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_895, 0, x_864);
lean::cnstr_set(x_895, 1, x_3);
x_896 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_896, 0, x_895);
return x_896;
}
}
}
else
{
obj* x_899; obj* x_900; obj* x_904; obj* x_905; obj* x_906; obj* x_907; 
lean::dec(x_8);
lean::dec(x_10);
x_899 = l_lean_parser_number_has__view;
x_900 = lean::cnstr_get(x_899, 0);
lean::inc(x_900);
lean::dec(x_899);
lean::inc(x_0);
x_904 = lean::apply_1(x_900, x_0);
x_905 = l_lean_parser_number_view_to__nat___main(x_904);
x_906 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_906, 0, x_905);
x_907 = lean_expr_mk_lit(x_906);
if (x_20 == 0)
{
obj* x_908; 
x_908 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_908) == 0)
{
obj* x_911; obj* x_912; 
lean::dec(x_2);
x_911 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_911, 0, x_907);
lean::cnstr_set(x_911, 1, x_3);
x_912 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_912, 0, x_911);
return x_912;
}
else
{
obj* x_913; obj* x_916; obj* x_919; obj* x_922; obj* x_923; obj* x_924; obj* x_926; obj* x_927; obj* x_928; obj* x_931; obj* x_932; obj* x_933; obj* x_934; obj* x_935; 
x_913 = lean::cnstr_get(x_908, 0);
lean::inc(x_913);
lean::dec(x_908);
x_916 = lean::cnstr_get(x_2, 0);
lean::inc(x_916);
lean::dec(x_2);
x_919 = lean::cnstr_get(x_916, 2);
lean::inc(x_919);
lean::dec(x_916);
x_922 = l_lean_file__map_to__position(x_919, x_913);
x_923 = lean::box(0);
x_924 = lean::cnstr_get(x_922, 1);
lean::inc(x_924);
x_926 = l_lean_elaborator_to__pexpr___main___closed__3;
x_927 = l_lean_kvmap_set__nat(x_923, x_926, x_924);
x_928 = lean::cnstr_get(x_922, 0);
lean::inc(x_928);
lean::dec(x_922);
x_931 = l_lean_elaborator_to__pexpr___main___closed__4;
x_932 = l_lean_kvmap_set__nat(x_927, x_931, x_928);
x_933 = lean_expr_mk_mdata(x_932, x_907);
x_934 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_934, 0, x_933);
lean::cnstr_set(x_934, 1, x_3);
x_935 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_935, 0, x_934);
return x_935;
}
}
else
{
obj* x_938; obj* x_939; 
lean::dec(x_0);
lean::dec(x_2);
x_938 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_938, 0, x_907);
lean::cnstr_set(x_938, 1, x_3);
x_939 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_939, 0, x_938);
return x_939;
}
}
}
else
{
obj* x_941; obj* x_942; obj* x_946; obj* x_947; obj* x_951; 
lean::dec(x_10);
x_941 = l_lean_parser_term_borrowed_has__view;
x_942 = lean::cnstr_get(x_941, 0);
lean::inc(x_942);
lean::dec(x_941);
lean::inc(x_0);
x_946 = lean::apply_1(x_942, x_0);
x_947 = lean::cnstr_get(x_946, 1);
lean::inc(x_947);
lean::dec(x_946);
lean::inc(x_2);
x_951 = l_lean_elaborator_to__pexpr___main(x_947, x_1, x_2, x_3);
if (lean::obj_tag(x_951) == 0)
{
obj* x_955; obj* x_957; obj* x_958; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_955 = lean::cnstr_get(x_951, 0);
if (lean::is_exclusive(x_951)) {
 x_957 = x_951;
} else {
 lean::inc(x_955);
 lean::dec(x_951);
 x_957 = lean::box(0);
}
if (lean::is_scalar(x_957)) {
 x_958 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_958 = x_957;
}
lean::cnstr_set(x_958, 0, x_955);
return x_958;
}
else
{
obj* x_959; obj* x_962; obj* x_964; obj* x_966; obj* x_967; obj* x_968; obj* x_969; 
x_959 = lean::cnstr_get(x_951, 0);
lean::inc(x_959);
lean::dec(x_951);
x_962 = lean::cnstr_get(x_959, 0);
x_964 = lean::cnstr_get(x_959, 1);
if (lean::is_exclusive(x_959)) {
 x_966 = x_959;
} else {
 lean::inc(x_962);
 lean::inc(x_964);
 lean::dec(x_959);
 x_966 = lean::box(0);
}
x_967 = l_lean_elaborator_to__pexpr___main___closed__31;
x_968 = l_lean_elaborator_expr_mk__annotation(x_967, x_962);
if (lean::is_scalar(x_966)) {
 x_969 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_969 = x_966;
}
lean::cnstr_set(x_969, 0, x_968);
lean::cnstr_set(x_969, 1, x_964);
x_15 = x_969;
goto lbl_16;
}
}
}
else
{
obj* x_971; obj* x_972; obj* x_976; obj* x_977; obj* x_981; 
lean::dec(x_10);
x_971 = l_lean_parser_term_inaccessible_has__view;
x_972 = lean::cnstr_get(x_971, 0);
lean::inc(x_972);
lean::dec(x_971);
lean::inc(x_0);
x_976 = lean::apply_1(x_972, x_0);
x_977 = lean::cnstr_get(x_976, 1);
lean::inc(x_977);
lean::dec(x_976);
lean::inc(x_2);
x_981 = l_lean_elaborator_to__pexpr___main(x_977, x_1, x_2, x_3);
if (lean::obj_tag(x_981) == 0)
{
obj* x_985; obj* x_987; obj* x_988; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_985 = lean::cnstr_get(x_981, 0);
if (lean::is_exclusive(x_981)) {
 x_987 = x_981;
} else {
 lean::inc(x_985);
 lean::dec(x_981);
 x_987 = lean::box(0);
}
if (lean::is_scalar(x_987)) {
 x_988 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_988 = x_987;
}
lean::cnstr_set(x_988, 0, x_985);
return x_988;
}
else
{
obj* x_989; obj* x_992; obj* x_994; obj* x_996; obj* x_997; obj* x_998; obj* x_999; 
x_989 = lean::cnstr_get(x_981, 0);
lean::inc(x_989);
lean::dec(x_981);
x_992 = lean::cnstr_get(x_989, 0);
x_994 = lean::cnstr_get(x_989, 1);
if (lean::is_exclusive(x_989)) {
 x_996 = x_989;
} else {
 lean::inc(x_992);
 lean::inc(x_994);
 lean::dec(x_989);
 x_996 = lean::box(0);
}
x_997 = l_lean_elaborator_to__pexpr___main___closed__32;
x_998 = l_lean_elaborator_expr_mk__annotation(x_997, x_992);
if (lean::is_scalar(x_996)) {
 x_999 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_999 = x_996;
}
lean::cnstr_set(x_999, 0, x_998);
lean::cnstr_set(x_999, 1, x_994);
x_15 = x_999;
goto lbl_16;
}
}
}
else
{
obj* x_1001; obj* x_1002; obj* x_1006; obj* x_1007; obj* x_1009; obj* x_1010; obj* x_1013; obj* x_1016; 
lean::dec(x_10);
x_1001 = l_lean_parser_term_explicit_has__view;
x_1002 = lean::cnstr_get(x_1001, 0);
lean::inc(x_1002);
lean::dec(x_1001);
lean::inc(x_0);
x_1006 = lean::apply_1(x_1002, x_0);
x_1007 = lean::cnstr_get(x_1006, 0);
lean::inc(x_1007);
x_1009 = l_lean_parser_ident__univs_has__view;
x_1010 = lean::cnstr_get(x_1009, 1);
lean::inc(x_1010);
lean::dec(x_1009);
x_1013 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1013);
lean::dec(x_1006);
x_1016 = lean::apply_1(x_1010, x_1013);
if (lean::obj_tag(x_1007) == 0)
{
obj* x_1019; 
lean::dec(x_1007);
lean::inc(x_2);
x_1019 = l_lean_elaborator_to__pexpr___main(x_1016, x_1, x_2, x_3);
if (lean::obj_tag(x_1019) == 0)
{
obj* x_1023; obj* x_1025; obj* x_1026; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1023 = lean::cnstr_get(x_1019, 0);
if (lean::is_exclusive(x_1019)) {
 x_1025 = x_1019;
} else {
 lean::inc(x_1023);
 lean::dec(x_1019);
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
obj* x_1027; obj* x_1030; obj* x_1032; obj* x_1034; obj* x_1035; obj* x_1036; obj* x_1037; 
x_1027 = lean::cnstr_get(x_1019, 0);
lean::inc(x_1027);
lean::dec(x_1019);
x_1030 = lean::cnstr_get(x_1027, 0);
x_1032 = lean::cnstr_get(x_1027, 1);
if (lean::is_exclusive(x_1027)) {
 x_1034 = x_1027;
} else {
 lean::inc(x_1030);
 lean::inc(x_1032);
 lean::dec(x_1027);
 x_1034 = lean::box(0);
}
x_1035 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
x_1036 = l_lean_elaborator_expr_mk__annotation(x_1035, x_1030);
if (lean::is_scalar(x_1034)) {
 x_1037 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1037 = x_1034;
}
lean::cnstr_set(x_1037, 0, x_1036);
lean::cnstr_set(x_1037, 1, x_1032);
x_15 = x_1037;
goto lbl_16;
}
}
else
{
obj* x_1040; 
lean::dec(x_1007);
lean::inc(x_2);
x_1040 = l_lean_elaborator_to__pexpr___main(x_1016, x_1, x_2, x_3);
if (lean::obj_tag(x_1040) == 0)
{
obj* x_1044; obj* x_1046; obj* x_1047; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1044 = lean::cnstr_get(x_1040, 0);
if (lean::is_exclusive(x_1040)) {
 x_1046 = x_1040;
} else {
 lean::inc(x_1044);
 lean::dec(x_1040);
 x_1046 = lean::box(0);
}
if (lean::is_scalar(x_1046)) {
 x_1047 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1047 = x_1046;
}
lean::cnstr_set(x_1047, 0, x_1044);
return x_1047;
}
else
{
obj* x_1048; obj* x_1051; obj* x_1053; obj* x_1055; obj* x_1056; obj* x_1057; obj* x_1058; 
x_1048 = lean::cnstr_get(x_1040, 0);
lean::inc(x_1048);
lean::dec(x_1040);
x_1051 = lean::cnstr_get(x_1048, 0);
x_1053 = lean::cnstr_get(x_1048, 1);
if (lean::is_exclusive(x_1048)) {
 x_1055 = x_1048;
} else {
 lean::inc(x_1051);
 lean::inc(x_1053);
 lean::dec(x_1048);
 x_1055 = lean::box(0);
}
x_1056 = l_lean_elaborator_to__pexpr___main___closed__33;
x_1057 = l_lean_elaborator_expr_mk__annotation(x_1056, x_1051);
if (lean::is_scalar(x_1055)) {
 x_1058 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1058 = x_1055;
}
lean::cnstr_set(x_1058, 0, x_1057);
lean::cnstr_set(x_1058, 1, x_1053);
x_15 = x_1058;
goto lbl_16;
}
}
}
}
else
{
obj* x_1060; obj* x_1061; obj* x_1065; obj* x_1066; 
lean::dec(x_10);
x_1060 = l_lean_parser_term_projection_has__view;
x_1061 = lean::cnstr_get(x_1060, 0);
lean::inc(x_1061);
lean::dec(x_1060);
lean::inc(x_0);
x_1065 = lean::apply_1(x_1061, x_0);
x_1066 = lean::cnstr_get(x_1065, 2);
lean::inc(x_1066);
if (lean::obj_tag(x_1066) == 0)
{
obj* x_1068; obj* x_1071; obj* x_1075; 
x_1068 = lean::cnstr_get(x_1065, 0);
lean::inc(x_1068);
lean::dec(x_1065);
x_1071 = lean::cnstr_get(x_1066, 0);
lean::inc(x_1071);
lean::dec(x_1066);
lean::inc(x_2);
x_1075 = l_lean_elaborator_to__pexpr___main(x_1068, x_1, x_2, x_3);
if (lean::obj_tag(x_1075) == 0)
{
obj* x_1080; obj* x_1082; obj* x_1083; 
lean::dec(x_1071);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1080 = lean::cnstr_get(x_1075, 0);
if (lean::is_exclusive(x_1075)) {
 x_1082 = x_1075;
} else {
 lean::inc(x_1080);
 lean::dec(x_1075);
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
obj* x_1084; obj* x_1087; obj* x_1089; obj* x_1091; obj* x_1092; obj* x_1095; obj* x_1096; obj* x_1097; obj* x_1098; obj* x_1099; obj* x_1100; 
x_1084 = lean::cnstr_get(x_1075, 0);
lean::inc(x_1084);
lean::dec(x_1075);
x_1087 = lean::cnstr_get(x_1084, 0);
x_1089 = lean::cnstr_get(x_1084, 1);
if (lean::is_exclusive(x_1084)) {
 x_1091 = x_1084;
} else {
 lean::inc(x_1087);
 lean::inc(x_1089);
 lean::dec(x_1084);
 x_1091 = lean::box(0);
}
x_1092 = lean::cnstr_get(x_1071, 2);
lean::inc(x_1092);
lean::dec(x_1071);
x_1095 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1095, 0, x_1092);
x_1096 = lean::box(0);
x_1097 = l_lean_elaborator_to__pexpr___main___closed__34;
x_1098 = l_lean_kvmap_insert__core___main(x_1096, x_1097, x_1095);
x_1099 = lean_expr_mk_mdata(x_1098, x_1087);
if (lean::is_scalar(x_1091)) {
 x_1100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1100 = x_1091;
}
lean::cnstr_set(x_1100, 0, x_1099);
lean::cnstr_set(x_1100, 1, x_1089);
x_15 = x_1100;
goto lbl_16;
}
}
else
{
obj* x_1101; obj* x_1104; obj* x_1108; 
x_1101 = lean::cnstr_get(x_1065, 0);
lean::inc(x_1101);
lean::dec(x_1065);
x_1104 = lean::cnstr_get(x_1066, 0);
lean::inc(x_1104);
lean::dec(x_1066);
lean::inc(x_2);
x_1108 = l_lean_elaborator_to__pexpr___main(x_1101, x_1, x_2, x_3);
if (lean::obj_tag(x_1108) == 0)
{
obj* x_1113; obj* x_1115; obj* x_1116; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1104);
x_1113 = lean::cnstr_get(x_1108, 0);
if (lean::is_exclusive(x_1108)) {
 x_1115 = x_1108;
} else {
 lean::inc(x_1113);
 lean::dec(x_1108);
 x_1115 = lean::box(0);
}
if (lean::is_scalar(x_1115)) {
 x_1116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1116 = x_1115;
}
lean::cnstr_set(x_1116, 0, x_1113);
return x_1116;
}
else
{
obj* x_1117; obj* x_1120; obj* x_1122; obj* x_1124; obj* x_1125; obj* x_1126; obj* x_1127; obj* x_1128; obj* x_1129; obj* x_1130; obj* x_1131; 
x_1117 = lean::cnstr_get(x_1108, 0);
lean::inc(x_1117);
lean::dec(x_1108);
x_1120 = lean::cnstr_get(x_1117, 0);
x_1122 = lean::cnstr_get(x_1117, 1);
if (lean::is_exclusive(x_1117)) {
 x_1124 = x_1117;
} else {
 lean::inc(x_1120);
 lean::inc(x_1122);
 lean::dec(x_1117);
 x_1124 = lean::box(0);
}
x_1125 = l_lean_parser_number_view_to__nat___main(x_1104);
x_1126 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1126, 0, x_1125);
x_1127 = lean::box(0);
x_1128 = l_lean_elaborator_to__pexpr___main___closed__34;
x_1129 = l_lean_kvmap_insert__core___main(x_1127, x_1128, x_1126);
x_1130 = lean_expr_mk_mdata(x_1129, x_1120);
if (lean::is_scalar(x_1124)) {
 x_1131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1131 = x_1124;
}
lean::cnstr_set(x_1131, 0, x_1130);
lean::cnstr_set(x_1131, 1, x_1122);
x_15 = x_1131;
goto lbl_16;
}
}
}
}
else
{
obj* x_1133; obj* x_1134; obj* x_1138; obj* x_1139; 
lean::dec(x_10);
x_1133 = l_lean_parser_term_let_has__view;
x_1134 = lean::cnstr_get(x_1133, 0);
lean::inc(x_1134);
lean::dec(x_1133);
lean::inc(x_0);
x_1138 = lean::apply_1(x_1134, x_0);
x_1139 = lean::cnstr_get(x_1138, 1);
lean::inc(x_1139);
if (lean::obj_tag(x_1139) == 0)
{
obj* x_1141; obj* x_1144; 
x_1141 = lean::cnstr_get(x_1139, 0);
lean::inc(x_1141);
lean::dec(x_1139);
x_1144 = lean::cnstr_get(x_1141, 1);
lean::inc(x_1144);
if (lean::obj_tag(x_1144) == 0)
{
obj* x_1146; 
x_1146 = lean::cnstr_get(x_1141, 2);
lean::inc(x_1146);
if (lean::obj_tag(x_1146) == 0)
{
obj* x_1151; obj* x_1152; obj* x_1154; 
lean::dec(x_1138);
lean::dec(x_1141);
lean::inc(x_0);
x_1151 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1151, 0, x_0);
x_1152 = l_lean_elaborator_to__pexpr___main___closed__35;
lean::inc(x_2);
x_1154 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_1151, x_1152, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1151);
if (lean::obj_tag(x_1154) == 0)
{
obj* x_1160; obj* x_1162; obj* x_1163; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1160 = lean::cnstr_get(x_1154, 0);
if (lean::is_exclusive(x_1154)) {
 x_1162 = x_1154;
} else {
 lean::inc(x_1160);
 lean::dec(x_1154);
 x_1162 = lean::box(0);
}
if (lean::is_scalar(x_1162)) {
 x_1163 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1163 = x_1162;
}
lean::cnstr_set(x_1163, 0, x_1160);
return x_1163;
}
else
{
obj* x_1164; 
x_1164 = lean::cnstr_get(x_1154, 0);
lean::inc(x_1164);
lean::dec(x_1154);
x_15 = x_1164;
goto lbl_16;
}
}
else
{
obj* x_1167; obj* x_1170; obj* x_1173; obj* x_1177; 
x_1167 = lean::cnstr_get(x_1141, 0);
lean::inc(x_1167);
lean::dec(x_1141);
x_1170 = lean::cnstr_get(x_1146, 0);
lean::inc(x_1170);
lean::dec(x_1146);
x_1173 = lean::cnstr_get(x_1170, 1);
lean::inc(x_1173);
lean::dec(x_1170);
lean::inc(x_2);
x_1177 = l_lean_elaborator_to__pexpr___main(x_1173, x_1, x_2, x_3);
if (lean::obj_tag(x_1177) == 0)
{
obj* x_1183; obj* x_1185; obj* x_1186; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1138);
lean::dec(x_1167);
x_1183 = lean::cnstr_get(x_1177, 0);
if (lean::is_exclusive(x_1177)) {
 x_1185 = x_1177;
} else {
 lean::inc(x_1183);
 lean::dec(x_1177);
 x_1185 = lean::box(0);
}
if (lean::is_scalar(x_1185)) {
 x_1186 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1186 = x_1185;
}
lean::cnstr_set(x_1186, 0, x_1183);
return x_1186;
}
else
{
obj* x_1187; obj* x_1190; obj* x_1192; obj* x_1195; obj* x_1198; 
x_1187 = lean::cnstr_get(x_1177, 0);
lean::inc(x_1187);
lean::dec(x_1177);
x_1190 = lean::cnstr_get(x_1187, 0);
lean::inc(x_1190);
x_1192 = lean::cnstr_get(x_1187, 1);
lean::inc(x_1192);
lean::dec(x_1187);
x_1195 = lean::cnstr_get(x_1138, 3);
lean::inc(x_1195);
lean::inc(x_2);
x_1198 = l_lean_elaborator_to__pexpr___main(x_1195, x_1, x_2, x_1192);
if (lean::obj_tag(x_1198) == 0)
{
obj* x_1205; obj* x_1207; obj* x_1208; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1138);
lean::dec(x_1167);
lean::dec(x_1190);
x_1205 = lean::cnstr_get(x_1198, 0);
if (lean::is_exclusive(x_1198)) {
 x_1207 = x_1198;
} else {
 lean::inc(x_1205);
 lean::dec(x_1198);
 x_1207 = lean::box(0);
}
if (lean::is_scalar(x_1207)) {
 x_1208 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1208 = x_1207;
}
lean::cnstr_set(x_1208, 0, x_1205);
return x_1208;
}
else
{
obj* x_1209; obj* x_1212; obj* x_1214; obj* x_1217; obj* x_1221; 
x_1209 = lean::cnstr_get(x_1198, 0);
lean::inc(x_1209);
lean::dec(x_1198);
x_1212 = lean::cnstr_get(x_1209, 0);
lean::inc(x_1212);
x_1214 = lean::cnstr_get(x_1209, 1);
lean::inc(x_1214);
lean::dec(x_1209);
x_1217 = lean::cnstr_get(x_1138, 5);
lean::inc(x_1217);
lean::dec(x_1138);
lean::inc(x_2);
x_1221 = l_lean_elaborator_to__pexpr___main(x_1217, x_1, x_2, x_1214);
if (lean::obj_tag(x_1221) == 0)
{
obj* x_1228; obj* x_1230; obj* x_1231; 
lean::dec(x_1212);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1167);
lean::dec(x_1190);
x_1228 = lean::cnstr_get(x_1221, 0);
if (lean::is_exclusive(x_1221)) {
 x_1230 = x_1221;
} else {
 lean::inc(x_1228);
 lean::dec(x_1221);
 x_1230 = lean::box(0);
}
if (lean::is_scalar(x_1230)) {
 x_1231 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1231 = x_1230;
}
lean::cnstr_set(x_1231, 0, x_1228);
return x_1231;
}
else
{
obj* x_1232; obj* x_1235; obj* x_1237; obj* x_1239; obj* x_1240; obj* x_1241; obj* x_1242; 
x_1232 = lean::cnstr_get(x_1221, 0);
lean::inc(x_1232);
lean::dec(x_1221);
x_1235 = lean::cnstr_get(x_1232, 0);
x_1237 = lean::cnstr_get(x_1232, 1);
if (lean::is_exclusive(x_1232)) {
 x_1239 = x_1232;
} else {
 lean::inc(x_1235);
 lean::inc(x_1237);
 lean::dec(x_1232);
 x_1239 = lean::box(0);
}
x_1240 = l_lean_elaborator_mangle__ident(x_1167);
x_1241 = lean_expr_mk_let(x_1240, x_1190, x_1212, x_1235);
if (lean::is_scalar(x_1239)) {
 x_1242 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1242 = x_1239;
}
lean::cnstr_set(x_1242, 0, x_1241);
lean::cnstr_set(x_1242, 1, x_1237);
x_15 = x_1242;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1247; obj* x_1248; obj* x_1250; 
lean::dec(x_1138);
lean::dec(x_1141);
lean::dec(x_1144);
lean::inc(x_0);
x_1247 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1247, 0, x_0);
x_1248 = l_lean_elaborator_to__pexpr___main___closed__35;
lean::inc(x_2);
x_1250 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_1247, x_1248, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1247);
if (lean::obj_tag(x_1250) == 0)
{
obj* x_1256; obj* x_1258; obj* x_1259; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1256 = lean::cnstr_get(x_1250, 0);
if (lean::is_exclusive(x_1250)) {
 x_1258 = x_1250;
} else {
 lean::inc(x_1256);
 lean::dec(x_1250);
 x_1258 = lean::box(0);
}
if (lean::is_scalar(x_1258)) {
 x_1259 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1259 = x_1258;
}
lean::cnstr_set(x_1259, 0, x_1256);
return x_1259;
}
else
{
obj* x_1260; 
x_1260 = lean::cnstr_get(x_1250, 0);
lean::inc(x_1260);
lean::dec(x_1250);
x_15 = x_1260;
goto lbl_16;
}
}
}
else
{
obj* x_1266; obj* x_1267; obj* x_1269; 
lean::dec(x_1138);
lean::dec(x_1139);
lean::inc(x_0);
x_1266 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1266, 0, x_0);
x_1267 = l_lean_elaborator_to__pexpr___main___closed__35;
lean::inc(x_2);
x_1269 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_1266, x_1267, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1266);
if (lean::obj_tag(x_1269) == 0)
{
obj* x_1275; obj* x_1277; obj* x_1278; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1275 = lean::cnstr_get(x_1269, 0);
if (lean::is_exclusive(x_1269)) {
 x_1277 = x_1269;
} else {
 lean::inc(x_1275);
 lean::dec(x_1269);
 x_1277 = lean::box(0);
}
if (lean::is_scalar(x_1277)) {
 x_1278 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1278 = x_1277;
}
lean::cnstr_set(x_1278, 0, x_1275);
return x_1278;
}
else
{
obj* x_1279; 
x_1279 = lean::cnstr_get(x_1269, 0);
lean::inc(x_1279);
lean::dec(x_1269);
x_15 = x_1279;
goto lbl_16;
}
}
}
}
else
{
obj* x_1283; obj* x_1284; obj* x_1288; obj* x_1289; obj* x_1292; 
lean::dec(x_10);
x_1283 = l_lean_parser_term_show_has__view;
x_1284 = lean::cnstr_get(x_1283, 0);
lean::inc(x_1284);
lean::dec(x_1283);
lean::inc(x_0);
x_1288 = lean::apply_1(x_1284, x_0);
x_1289 = lean::cnstr_get(x_1288, 1);
lean::inc(x_1289);
lean::inc(x_2);
x_1292 = l_lean_elaborator_to__pexpr___main(x_1289, x_1, x_2, x_3);
if (lean::obj_tag(x_1292) == 0)
{
obj* x_1297; obj* x_1299; obj* x_1300; 
lean::dec(x_1288);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1297 = lean::cnstr_get(x_1292, 0);
if (lean::is_exclusive(x_1292)) {
 x_1299 = x_1292;
} else {
 lean::inc(x_1297);
 lean::dec(x_1292);
 x_1299 = lean::box(0);
}
if (lean::is_scalar(x_1299)) {
 x_1300 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1300 = x_1299;
}
lean::cnstr_set(x_1300, 0, x_1297);
return x_1300;
}
else
{
obj* x_1301; obj* x_1304; obj* x_1306; obj* x_1309; obj* x_1312; obj* x_1316; 
x_1301 = lean::cnstr_get(x_1292, 0);
lean::inc(x_1301);
lean::dec(x_1292);
x_1304 = lean::cnstr_get(x_1301, 0);
lean::inc(x_1304);
x_1306 = lean::cnstr_get(x_1301, 1);
lean::inc(x_1306);
lean::dec(x_1301);
x_1309 = lean::cnstr_get(x_1288, 3);
lean::inc(x_1309);
lean::dec(x_1288);
x_1312 = lean::cnstr_get(x_1309, 1);
lean::inc(x_1312);
lean::dec(x_1309);
lean::inc(x_2);
x_1316 = l_lean_elaborator_to__pexpr___main(x_1312, x_1, x_2, x_1306);
if (lean::obj_tag(x_1316) == 0)
{
obj* x_1321; obj* x_1323; obj* x_1324; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1304);
x_1321 = lean::cnstr_get(x_1316, 0);
if (lean::is_exclusive(x_1316)) {
 x_1323 = x_1316;
} else {
 lean::inc(x_1321);
 lean::dec(x_1316);
 x_1323 = lean::box(0);
}
if (lean::is_scalar(x_1323)) {
 x_1324 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1324 = x_1323;
}
lean::cnstr_set(x_1324, 0, x_1321);
return x_1324;
}
else
{
obj* x_1325; obj* x_1328; obj* x_1330; obj* x_1332; obj* x_1333; uint8 x_1334; obj* x_1335; obj* x_1336; obj* x_1337; obj* x_1338; obj* x_1339; obj* x_1340; 
x_1325 = lean::cnstr_get(x_1316, 0);
lean::inc(x_1325);
lean::dec(x_1316);
x_1328 = lean::cnstr_get(x_1325, 0);
x_1330 = lean::cnstr_get(x_1325, 1);
if (lean::is_exclusive(x_1325)) {
 x_1332 = x_1325;
} else {
 lean::inc(x_1328);
 lean::inc(x_1330);
 lean::dec(x_1325);
 x_1332 = lean::box(0);
}
x_1333 = l_lean_elaborator_to__pexpr___main___closed__36;
x_1334 = 0;
x_1335 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1336 = lean_expr_mk_lambda(x_1333, x_1334, x_1304, x_1335);
x_1337 = lean_expr_mk_app(x_1336, x_1328);
x_1338 = l_lean_elaborator_to__pexpr___main___closed__38;
x_1339 = l_lean_elaborator_expr_mk__annotation(x_1338, x_1337);
if (lean::is_scalar(x_1332)) {
 x_1340 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1340 = x_1332;
}
lean::cnstr_set(x_1340, 0, x_1339);
lean::cnstr_set(x_1340, 1, x_1330);
x_15 = x_1340;
goto lbl_16;
}
}
}
}
else
{
obj* x_1342; obj* x_1343; obj* x_1347; obj* x_1348; obj* x_1350; 
lean::dec(x_10);
x_1342 = l_lean_parser_term_have_has__view;
x_1343 = lean::cnstr_get(x_1342, 0);
lean::inc(x_1343);
lean::dec(x_1342);
lean::inc(x_0);
x_1347 = lean::apply_1(x_1343, x_0);
x_1350 = lean::cnstr_get(x_1347, 1);
lean::inc(x_1350);
if (lean::obj_tag(x_1350) == 0)
{
obj* x_1352; obj* x_1354; obj* x_1357; 
x_1352 = lean::cnstr_get(x_1347, 2);
lean::inc(x_1352);
x_1354 = lean::cnstr_get(x_1347, 5);
lean::inc(x_1354);
lean::inc(x_2);
x_1357 = l_lean_elaborator_to__pexpr___main(x_1352, x_1, x_2, x_3);
if (lean::obj_tag(x_1357) == 0)
{
obj* x_1363; obj* x_1365; obj* x_1366; 
lean::dec(x_1347);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1354);
x_1363 = lean::cnstr_get(x_1357, 0);
if (lean::is_exclusive(x_1357)) {
 x_1365 = x_1357;
} else {
 lean::inc(x_1363);
 lean::dec(x_1357);
 x_1365 = lean::box(0);
}
if (lean::is_scalar(x_1365)) {
 x_1366 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1366 = x_1365;
}
lean::cnstr_set(x_1366, 0, x_1363);
return x_1366;
}
else
{
obj* x_1367; obj* x_1370; obj* x_1372; obj* x_1376; 
x_1367 = lean::cnstr_get(x_1357, 0);
lean::inc(x_1367);
lean::dec(x_1357);
x_1370 = lean::cnstr_get(x_1367, 0);
lean::inc(x_1370);
x_1372 = lean::cnstr_get(x_1367, 1);
lean::inc(x_1372);
lean::dec(x_1367);
lean::inc(x_2);
x_1376 = l_lean_elaborator_to__pexpr___main(x_1354, x_1, x_2, x_1372);
if (lean::obj_tag(x_1376) == 0)
{
obj* x_1382; obj* x_1384; obj* x_1385; 
lean::dec(x_1347);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1370);
x_1382 = lean::cnstr_get(x_1376, 0);
if (lean::is_exclusive(x_1376)) {
 x_1384 = x_1376;
} else {
 lean::inc(x_1382);
 lean::dec(x_1376);
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
obj* x_1386; obj* x_1389; obj* x_1391; obj* x_1393; obj* x_1394; uint8 x_1395; obj* x_1396; obj* x_1397; 
x_1386 = lean::cnstr_get(x_1376, 0);
lean::inc(x_1386);
lean::dec(x_1376);
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
x_1394 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1395 = 0;
x_1396 = lean_expr_mk_lambda(x_1394, x_1395, x_1370, x_1389);
if (lean::is_scalar(x_1393)) {
 x_1397 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1397 = x_1393;
}
lean::cnstr_set(x_1397, 0, x_1396);
lean::cnstr_set(x_1397, 1, x_1391);
x_1348 = x_1397;
goto lbl_1349;
}
}
}
else
{
obj* x_1398; obj* x_1400; obj* x_1402; obj* x_1404; obj* x_1406; 
x_1398 = lean::cnstr_get(x_1347, 2);
lean::inc(x_1398);
x_1400 = lean::cnstr_get(x_1347, 5);
lean::inc(x_1400);
x_1402 = lean::cnstr_get(x_1350, 0);
if (lean::is_exclusive(x_1350)) {
 lean::cnstr_set(x_1350, 0, lean::box(0));
 x_1404 = x_1350;
} else {
 lean::inc(x_1402);
 lean::dec(x_1350);
 x_1404 = lean::box(0);
}
lean::inc(x_2);
x_1406 = l_lean_elaborator_to__pexpr___main(x_1398, x_1, x_2, x_3);
if (lean::obj_tag(x_1406) == 0)
{
obj* x_1414; obj* x_1416; obj* x_1417; 
lean::dec(x_1347);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1404);
lean::dec(x_1400);
lean::dec(x_1402);
x_1414 = lean::cnstr_get(x_1406, 0);
if (lean::is_exclusive(x_1406)) {
 x_1416 = x_1406;
} else {
 lean::inc(x_1414);
 lean::dec(x_1406);
 x_1416 = lean::box(0);
}
if (lean::is_scalar(x_1416)) {
 x_1417 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1417 = x_1416;
}
lean::cnstr_set(x_1417, 0, x_1414);
return x_1417;
}
else
{
obj* x_1418; obj* x_1421; obj* x_1423; obj* x_1427; 
x_1418 = lean::cnstr_get(x_1406, 0);
lean::inc(x_1418);
lean::dec(x_1406);
x_1421 = lean::cnstr_get(x_1418, 0);
lean::inc(x_1421);
x_1423 = lean::cnstr_get(x_1418, 1);
lean::inc(x_1423);
lean::dec(x_1418);
lean::inc(x_2);
x_1427 = l_lean_elaborator_to__pexpr___main(x_1400, x_1, x_2, x_1423);
if (lean::obj_tag(x_1427) == 0)
{
obj* x_1435; obj* x_1437; obj* x_1438; 
lean::dec(x_1347);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1404);
lean::dec(x_1402);
lean::dec(x_1421);
x_1435 = lean::cnstr_get(x_1427, 0);
if (lean::is_exclusive(x_1427)) {
 x_1437 = x_1427;
} else {
 lean::inc(x_1435);
 lean::dec(x_1427);
 x_1437 = lean::box(0);
}
if (lean::is_scalar(x_1437)) {
 x_1438 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1438 = x_1437;
}
lean::cnstr_set(x_1438, 0, x_1435);
return x_1438;
}
else
{
obj* x_1439; obj* x_1442; obj* x_1444; obj* x_1446; obj* x_1447; obj* x_1450; obj* x_1451; obj* x_1452; obj* x_1453; uint8 x_1455; obj* x_1456; obj* x_1457; 
x_1439 = lean::cnstr_get(x_1427, 0);
lean::inc(x_1439);
lean::dec(x_1427);
x_1442 = lean::cnstr_get(x_1439, 0);
x_1444 = lean::cnstr_get(x_1439, 1);
if (lean::is_exclusive(x_1439)) {
 x_1446 = x_1439;
} else {
 lean::inc(x_1442);
 lean::inc(x_1444);
 lean::dec(x_1439);
 x_1446 = lean::box(0);
}
x_1447 = lean::cnstr_get(x_1402, 0);
lean::inc(x_1447);
lean::dec(x_1402);
x_1450 = l_lean_elaborator_mangle__ident(x_1447);
if (lean::is_scalar(x_1404)) {
 x_1451 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1451 = x_1404;
}
lean::cnstr_set(x_1451, 0, x_1450);
x_1452 = l_lean_elaborator_to__pexpr___main___closed__36;
x_1453 = l_option_get__or__else___main___rarg(x_1451, x_1452);
lean::dec(x_1451);
x_1455 = 0;
x_1456 = lean_expr_mk_lambda(x_1453, x_1455, x_1421, x_1442);
if (lean::is_scalar(x_1446)) {
 x_1457 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1457 = x_1446;
}
lean::cnstr_set(x_1457, 0, x_1456);
lean::cnstr_set(x_1457, 1, x_1444);
x_1348 = x_1457;
goto lbl_1349;
}
}
}
lbl_1349:
{
obj* x_1458; 
x_1458 = lean::cnstr_get(x_1347, 3);
lean::inc(x_1458);
lean::dec(x_1347);
if (lean::obj_tag(x_1458) == 0)
{
obj* x_1461; obj* x_1463; obj* x_1466; obj* x_1469; obj* x_1473; 
x_1461 = lean::cnstr_get(x_1348, 0);
lean::inc(x_1461);
x_1463 = lean::cnstr_get(x_1348, 1);
lean::inc(x_1463);
lean::dec(x_1348);
x_1466 = lean::cnstr_get(x_1458, 0);
lean::inc(x_1466);
lean::dec(x_1458);
x_1469 = lean::cnstr_get(x_1466, 1);
lean::inc(x_1469);
lean::dec(x_1466);
lean::inc(x_2);
x_1473 = l_lean_elaborator_to__pexpr___main(x_1469, x_1, x_2, x_1463);
if (lean::obj_tag(x_1473) == 0)
{
obj* x_1478; obj* x_1480; obj* x_1481; 
lean::dec(x_1461);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1478 = lean::cnstr_get(x_1473, 0);
if (lean::is_exclusive(x_1473)) {
 x_1480 = x_1473;
} else {
 lean::inc(x_1478);
 lean::dec(x_1473);
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
obj* x_1482; obj* x_1485; obj* x_1487; obj* x_1489; obj* x_1490; obj* x_1491; obj* x_1492; obj* x_1493; 
x_1482 = lean::cnstr_get(x_1473, 0);
lean::inc(x_1482);
lean::dec(x_1473);
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
x_1490 = l_lean_elaborator_to__pexpr___main___closed__39;
x_1491 = l_lean_elaborator_expr_mk__annotation(x_1490, x_1461);
x_1492 = lean_expr_mk_app(x_1491, x_1485);
if (lean::is_scalar(x_1489)) {
 x_1493 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1493 = x_1489;
}
lean::cnstr_set(x_1493, 0, x_1492);
lean::cnstr_set(x_1493, 1, x_1487);
x_15 = x_1493;
goto lbl_16;
}
}
else
{
obj* x_1494; obj* x_1496; obj* x_1499; obj* x_1502; obj* x_1505; obj* x_1509; 
x_1494 = lean::cnstr_get(x_1348, 0);
lean::inc(x_1494);
x_1496 = lean::cnstr_get(x_1348, 1);
lean::inc(x_1496);
lean::dec(x_1348);
x_1499 = lean::cnstr_get(x_1458, 0);
lean::inc(x_1499);
lean::dec(x_1458);
x_1502 = lean::cnstr_get(x_1499, 1);
lean::inc(x_1502);
lean::dec(x_1499);
x_1505 = lean::cnstr_get(x_1502, 1);
lean::inc(x_1505);
lean::dec(x_1502);
lean::inc(x_2);
x_1509 = l_lean_elaborator_to__pexpr___main(x_1505, x_1, x_2, x_1496);
if (lean::obj_tag(x_1509) == 0)
{
obj* x_1514; obj* x_1516; obj* x_1517; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1494);
x_1514 = lean::cnstr_get(x_1509, 0);
if (lean::is_exclusive(x_1509)) {
 x_1516 = x_1509;
} else {
 lean::inc(x_1514);
 lean::dec(x_1509);
 x_1516 = lean::box(0);
}
if (lean::is_scalar(x_1516)) {
 x_1517 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1517 = x_1516;
}
lean::cnstr_set(x_1517, 0, x_1514);
return x_1517;
}
else
{
obj* x_1518; obj* x_1521; obj* x_1523; obj* x_1525; obj* x_1526; obj* x_1527; obj* x_1528; obj* x_1529; 
x_1518 = lean::cnstr_get(x_1509, 0);
lean::inc(x_1518);
lean::dec(x_1509);
x_1521 = lean::cnstr_get(x_1518, 0);
x_1523 = lean::cnstr_get(x_1518, 1);
if (lean::is_exclusive(x_1518)) {
 x_1525 = x_1518;
} else {
 lean::inc(x_1521);
 lean::inc(x_1523);
 lean::dec(x_1518);
 x_1525 = lean::box(0);
}
x_1526 = l_lean_elaborator_to__pexpr___main___closed__39;
x_1527 = l_lean_elaborator_expr_mk__annotation(x_1526, x_1494);
x_1528 = lean_expr_mk_app(x_1527, x_1521);
if (lean::is_scalar(x_1525)) {
 x_1529 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1529 = x_1525;
}
lean::cnstr_set(x_1529, 0, x_1528);
lean::cnstr_set(x_1529, 1, x_1523);
x_15 = x_1529;
goto lbl_16;
}
}
}
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
if (x_20 == 0)
{
obj* x_1532; 
x_1532 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1532) == 0)
{
obj* x_1535; obj* x_1536; obj* x_1537; 
lean::dec(x_2);
x_1535 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1536 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1536, 0, x_1535);
lean::cnstr_set(x_1536, 1, x_3);
x_1537 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1537, 0, x_1536);
return x_1537;
}
else
{
obj* x_1538; obj* x_1541; obj* x_1544; obj* x_1547; obj* x_1548; obj* x_1549; obj* x_1551; obj* x_1552; obj* x_1553; obj* x_1556; obj* x_1557; obj* x_1558; obj* x_1559; obj* x_1560; obj* x_1561; 
x_1538 = lean::cnstr_get(x_1532, 0);
lean::inc(x_1538);
lean::dec(x_1532);
x_1541 = lean::cnstr_get(x_2, 0);
lean::inc(x_1541);
lean::dec(x_2);
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
x_1558 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1559 = lean_expr_mk_mdata(x_1557, x_1558);
x_1560 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1560, 0, x_1559);
lean::cnstr_set(x_1560, 1, x_3);
x_1561 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1561, 0, x_1560);
return x_1561;
}
}
else
{
obj* x_1564; obj* x_1565; obj* x_1566; 
lean::dec(x_0);
lean::dec(x_2);
x_1564 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1565 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1565, 0, x_1564);
lean::cnstr_set(x_1565, 1, x_3);
x_1566 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1566, 0, x_1565);
return x_1566;
}
}
}
else
{
obj* x_1568; obj* x_1569; obj* x_1573; obj* x_1574; obj* x_1577; obj* x_1578; obj* x_1579; obj* x_1581; 
lean::dec(x_10);
x_1568 = l_lean_parser_term_anonymous__constructor_has__view;
x_1569 = lean::cnstr_get(x_1568, 0);
lean::inc(x_1569);
lean::dec(x_1568);
lean::inc(x_0);
x_1573 = lean::apply_1(x_1569, x_0);
x_1574 = lean::cnstr_get(x_1573, 1);
lean::inc(x_1574);
lean::dec(x_1573);
x_1577 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_1574);
x_1578 = l_lean_expander_get__opt__type___main___closed__1;
x_1579 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_1578, x_1577);
lean::inc(x_2);
x_1581 = l_lean_elaborator_to__pexpr___main(x_1579, x_1, x_2, x_3);
if (lean::obj_tag(x_1581) == 0)
{
obj* x_1585; obj* x_1587; obj* x_1588; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1585 = lean::cnstr_get(x_1581, 0);
if (lean::is_exclusive(x_1581)) {
 x_1587 = x_1581;
} else {
 lean::inc(x_1585);
 lean::dec(x_1581);
 x_1587 = lean::box(0);
}
if (lean::is_scalar(x_1587)) {
 x_1588 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1588 = x_1587;
}
lean::cnstr_set(x_1588, 0, x_1585);
return x_1588;
}
else
{
obj* x_1589; obj* x_1592; obj* x_1594; obj* x_1596; obj* x_1597; obj* x_1598; obj* x_1599; 
x_1589 = lean::cnstr_get(x_1581, 0);
lean::inc(x_1589);
lean::dec(x_1581);
x_1592 = lean::cnstr_get(x_1589, 0);
x_1594 = lean::cnstr_get(x_1589, 1);
if (lean::is_exclusive(x_1589)) {
 x_1596 = x_1589;
} else {
 lean::inc(x_1592);
 lean::inc(x_1594);
 lean::dec(x_1589);
 x_1596 = lean::box(0);
}
x_1597 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1598 = l_lean_elaborator_expr_mk__annotation(x_1597, x_1592);
if (lean::is_scalar(x_1596)) {
 x_1599 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1599 = x_1596;
}
lean::cnstr_set(x_1599, 0, x_1598);
lean::cnstr_set(x_1599, 1, x_1594);
x_15 = x_1599;
goto lbl_16;
}
}
}
else
{
obj* x_1601; obj* x_1602; obj* x_1606; obj* x_1607; obj* x_1608; obj* x_1611; obj* x_1613; 
lean::dec(x_10);
x_1601 = l_lean_parser_term_sort__app_has__view;
x_1602 = lean::cnstr_get(x_1601, 0);
lean::inc(x_1602);
lean::dec(x_1601);
lean::inc(x_0);
x_1606 = lean::apply_1(x_1602, x_0);
x_1607 = l_lean_parser_term_sort_has__view;
x_1608 = lean::cnstr_get(x_1607, 0);
lean::inc(x_1608);
lean::dec(x_1607);
x_1611 = lean::cnstr_get(x_1606, 0);
lean::inc(x_1611);
x_1613 = lean::apply_1(x_1608, x_1611);
if (lean::obj_tag(x_1613) == 0)
{
obj* x_1615; obj* x_1619; 
lean::dec(x_1613);
x_1615 = lean::cnstr_get(x_1606, 1);
lean::inc(x_1615);
lean::dec(x_1606);
lean::inc(x_2);
x_1619 = l_lean_elaborator_to__level___main(x_1615, x_1, x_2, x_3);
if (lean::obj_tag(x_1619) == 0)
{
obj* x_1623; obj* x_1625; obj* x_1626; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1623 = lean::cnstr_get(x_1619, 0);
if (lean::is_exclusive(x_1619)) {
 x_1625 = x_1619;
} else {
 lean::inc(x_1623);
 lean::dec(x_1619);
 x_1625 = lean::box(0);
}
if (lean::is_scalar(x_1625)) {
 x_1626 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1626 = x_1625;
}
lean::cnstr_set(x_1626, 0, x_1623);
return x_1626;
}
else
{
obj* x_1627; obj* x_1630; obj* x_1632; obj* x_1634; obj* x_1635; obj* x_1636; 
x_1627 = lean::cnstr_get(x_1619, 0);
lean::inc(x_1627);
lean::dec(x_1619);
x_1630 = lean::cnstr_get(x_1627, 0);
x_1632 = lean::cnstr_get(x_1627, 1);
if (lean::is_exclusive(x_1627)) {
 x_1634 = x_1627;
} else {
 lean::inc(x_1630);
 lean::inc(x_1632);
 lean::dec(x_1627);
 x_1634 = lean::box(0);
}
x_1635 = lean_expr_mk_sort(x_1630);
if (lean::is_scalar(x_1634)) {
 x_1636 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1636 = x_1634;
}
lean::cnstr_set(x_1636, 0, x_1635);
lean::cnstr_set(x_1636, 1, x_1632);
x_15 = x_1636;
goto lbl_16;
}
}
else
{
obj* x_1638; obj* x_1642; 
lean::dec(x_1613);
x_1638 = lean::cnstr_get(x_1606, 1);
lean::inc(x_1638);
lean::dec(x_1606);
lean::inc(x_2);
x_1642 = l_lean_elaborator_to__level___main(x_1638, x_1, x_2, x_3);
if (lean::obj_tag(x_1642) == 0)
{
obj* x_1646; obj* x_1648; obj* x_1649; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1646 = lean::cnstr_get(x_1642, 0);
if (lean::is_exclusive(x_1642)) {
 x_1648 = x_1642;
} else {
 lean::inc(x_1646);
 lean::dec(x_1642);
 x_1648 = lean::box(0);
}
if (lean::is_scalar(x_1648)) {
 x_1649 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1649 = x_1648;
}
lean::cnstr_set(x_1649, 0, x_1646);
return x_1649;
}
else
{
obj* x_1650; obj* x_1653; obj* x_1655; obj* x_1657; obj* x_1658; obj* x_1659; obj* x_1660; 
x_1650 = lean::cnstr_get(x_1642, 0);
lean::inc(x_1650);
lean::dec(x_1642);
x_1653 = lean::cnstr_get(x_1650, 0);
x_1655 = lean::cnstr_get(x_1650, 1);
if (lean::is_exclusive(x_1650)) {
 x_1657 = x_1650;
} else {
 lean::inc(x_1653);
 lean::inc(x_1655);
 lean::dec(x_1650);
 x_1657 = lean::box(0);
}
x_1658 = level_mk_succ(x_1653);
x_1659 = lean_expr_mk_sort(x_1658);
if (lean::is_scalar(x_1657)) {
 x_1660 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1660 = x_1657;
}
lean::cnstr_set(x_1660, 0, x_1659);
lean::cnstr_set(x_1660, 1, x_1655);
x_15 = x_1660;
goto lbl_16;
}
}
}
}
else
{
obj* x_1663; obj* x_1664; obj* x_1668; 
lean::dec(x_8);
lean::dec(x_10);
x_1663 = l_lean_parser_term_sort_has__view;
x_1664 = lean::cnstr_get(x_1663, 0);
lean::inc(x_1664);
lean::dec(x_1663);
lean::inc(x_0);
x_1668 = lean::apply_1(x_1664, x_0);
if (lean::obj_tag(x_1668) == 0)
{
lean::dec(x_1668);
if (x_20 == 0)
{
obj* x_1670; 
x_1670 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1670) == 0)
{
obj* x_1673; obj* x_1674; obj* x_1675; 
lean::dec(x_2);
x_1673 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_1674 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1674, 0, x_1673);
lean::cnstr_set(x_1674, 1, x_3);
x_1675 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1675, 0, x_1674);
return x_1675;
}
else
{
obj* x_1676; obj* x_1679; obj* x_1682; obj* x_1685; obj* x_1686; obj* x_1687; obj* x_1689; obj* x_1690; obj* x_1691; obj* x_1694; obj* x_1695; obj* x_1696; obj* x_1697; obj* x_1698; obj* x_1699; 
x_1676 = lean::cnstr_get(x_1670, 0);
lean::inc(x_1676);
lean::dec(x_1670);
x_1679 = lean::cnstr_get(x_2, 0);
lean::inc(x_1679);
lean::dec(x_2);
x_1682 = lean::cnstr_get(x_1679, 2);
lean::inc(x_1682);
lean::dec(x_1679);
x_1685 = l_lean_file__map_to__position(x_1682, x_1676);
x_1686 = lean::box(0);
x_1687 = lean::cnstr_get(x_1685, 1);
lean::inc(x_1687);
x_1689 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1690 = l_lean_kvmap_set__nat(x_1686, x_1689, x_1687);
x_1691 = lean::cnstr_get(x_1685, 0);
lean::inc(x_1691);
lean::dec(x_1685);
x_1694 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1695 = l_lean_kvmap_set__nat(x_1690, x_1694, x_1691);
x_1696 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_1697 = lean_expr_mk_mdata(x_1695, x_1696);
x_1698 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1698, 0, x_1697);
lean::cnstr_set(x_1698, 1, x_3);
x_1699 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1699, 0, x_1698);
return x_1699;
}
}
else
{
obj* x_1702; obj* x_1703; obj* x_1704; 
lean::dec(x_0);
lean::dec(x_2);
x_1702 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
x_1703 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1703, 0, x_1702);
lean::cnstr_set(x_1703, 1, x_3);
x_1704 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1704, 0, x_1703);
return x_1704;
}
}
else
{
lean::dec(x_1668);
if (x_20 == 0)
{
obj* x_1706; 
x_1706 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1706) == 0)
{
obj* x_1709; obj* x_1710; obj* x_1711; 
lean::dec(x_2);
x_1709 = l_lean_elaborator_to__pexpr___main___closed__43;
x_1710 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1710, 0, x_1709);
lean::cnstr_set(x_1710, 1, x_3);
x_1711 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1711, 0, x_1710);
return x_1711;
}
else
{
obj* x_1712; obj* x_1715; obj* x_1718; obj* x_1721; obj* x_1722; obj* x_1723; obj* x_1725; obj* x_1726; obj* x_1727; obj* x_1730; obj* x_1731; obj* x_1732; obj* x_1733; obj* x_1734; obj* x_1735; 
x_1712 = lean::cnstr_get(x_1706, 0);
lean::inc(x_1712);
lean::dec(x_1706);
x_1715 = lean::cnstr_get(x_2, 0);
lean::inc(x_1715);
lean::dec(x_2);
x_1718 = lean::cnstr_get(x_1715, 2);
lean::inc(x_1718);
lean::dec(x_1715);
x_1721 = l_lean_file__map_to__position(x_1718, x_1712);
x_1722 = lean::box(0);
x_1723 = lean::cnstr_get(x_1721, 1);
lean::inc(x_1723);
x_1725 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1726 = l_lean_kvmap_set__nat(x_1722, x_1725, x_1723);
x_1727 = lean::cnstr_get(x_1721, 0);
lean::inc(x_1727);
lean::dec(x_1721);
x_1730 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1731 = l_lean_kvmap_set__nat(x_1726, x_1730, x_1727);
x_1732 = l_lean_elaborator_to__pexpr___main___closed__43;
x_1733 = lean_expr_mk_mdata(x_1731, x_1732);
x_1734 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1734, 0, x_1733);
lean::cnstr_set(x_1734, 1, x_3);
x_1735 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1735, 0, x_1734);
return x_1735;
}
}
else
{
obj* x_1738; obj* x_1739; obj* x_1740; 
lean::dec(x_0);
lean::dec(x_2);
x_1738 = l_lean_elaborator_to__pexpr___main___closed__43;
x_1739 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1739, 0, x_1738);
lean::cnstr_set(x_1739, 1, x_3);
x_1740 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1740, 0, x_1739);
return x_1740;
}
}
}
}
else
{
obj* x_1742; obj* x_1743; obj* x_1747; obj* x_1748; 
lean::dec(x_10);
x_1742 = l_lean_parser_term_pi_has__view;
x_1743 = lean::cnstr_get(x_1742, 0);
lean::inc(x_1743);
lean::dec(x_1742);
lean::inc(x_0);
x_1747 = lean::apply_1(x_1743, x_0);
x_1748 = lean::cnstr_get(x_1747, 1);
lean::inc(x_1748);
if (lean::obj_tag(x_1748) == 0)
{
obj* x_1753; obj* x_1754; obj* x_1756; 
lean::dec(x_1748);
lean::dec(x_1747);
lean::inc(x_0);
x_1753 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1753, 0, x_0);
x_1754 = l_lean_elaborator_to__pexpr___main___closed__44;
lean::inc(x_2);
x_1756 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_1753, x_1754, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1753);
if (lean::obj_tag(x_1756) == 0)
{
obj* x_1762; obj* x_1764; obj* x_1765; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1762 = lean::cnstr_get(x_1756, 0);
if (lean::is_exclusive(x_1756)) {
 x_1764 = x_1756;
} else {
 lean::inc(x_1762);
 lean::dec(x_1756);
 x_1764 = lean::box(0);
}
if (lean::is_scalar(x_1764)) {
 x_1765 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1765 = x_1764;
}
lean::cnstr_set(x_1765, 0, x_1762);
return x_1765;
}
else
{
obj* x_1766; 
x_1766 = lean::cnstr_get(x_1756, 0);
lean::inc(x_1766);
lean::dec(x_1756);
x_15 = x_1766;
goto lbl_16;
}
}
else
{
obj* x_1769; obj* x_1772; obj* x_1773; obj* x_1775; obj* x_1778; obj* x_1780; obj* x_1784; 
x_1769 = lean::cnstr_get(x_1748, 0);
lean::inc(x_1769);
lean::dec(x_1748);
x_1772 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1769);
x_1773 = lean::cnstr_get(x_1772, 1);
lean::inc(x_1773);
x_1775 = lean::cnstr_get(x_1772, 0);
lean::inc(x_1775);
lean::dec(x_1772);
x_1778 = lean::cnstr_get(x_1773, 0);
lean::inc(x_1778);
x_1780 = lean::cnstr_get(x_1773, 1);
lean::inc(x_1780);
lean::dec(x_1773);
lean::inc(x_2);
x_1784 = l_lean_elaborator_to__pexpr___main(x_1780, x_1, x_2, x_3);
if (lean::obj_tag(x_1784) == 0)
{
obj* x_1791; obj* x_1793; obj* x_1794; 
lean::dec(x_8);
lean::dec(x_1778);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1775);
lean::dec(x_1747);
x_1791 = lean::cnstr_get(x_1784, 0);
if (lean::is_exclusive(x_1784)) {
 x_1793 = x_1784;
} else {
 lean::inc(x_1791);
 lean::dec(x_1784);
 x_1793 = lean::box(0);
}
if (lean::is_scalar(x_1793)) {
 x_1794 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1794 = x_1793;
}
lean::cnstr_set(x_1794, 0, x_1791);
return x_1794;
}
else
{
obj* x_1795; obj* x_1798; obj* x_1800; obj* x_1803; obj* x_1807; 
x_1795 = lean::cnstr_get(x_1784, 0);
lean::inc(x_1795);
lean::dec(x_1784);
x_1798 = lean::cnstr_get(x_1795, 0);
lean::inc(x_1798);
x_1800 = lean::cnstr_get(x_1795, 1);
lean::inc(x_1800);
lean::dec(x_1795);
x_1803 = lean::cnstr_get(x_1747, 3);
lean::inc(x_1803);
lean::dec(x_1747);
lean::inc(x_2);
x_1807 = l_lean_elaborator_to__pexpr___main(x_1803, x_1, x_2, x_1800);
if (lean::obj_tag(x_1807) == 0)
{
obj* x_1814; obj* x_1816; obj* x_1817; 
lean::dec(x_8);
lean::dec(x_1778);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1775);
lean::dec(x_1798);
x_1814 = lean::cnstr_get(x_1807, 0);
if (lean::is_exclusive(x_1807)) {
 x_1816 = x_1807;
} else {
 lean::inc(x_1814);
 lean::dec(x_1807);
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
obj* x_1818; obj* x_1821; obj* x_1823; obj* x_1825; obj* x_1826; uint8 x_1827; obj* x_1828; obj* x_1829; 
x_1818 = lean::cnstr_get(x_1807, 0);
lean::inc(x_1818);
lean::dec(x_1807);
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
x_1826 = l_lean_elaborator_mangle__ident(x_1778);
x_1827 = lean::unbox(x_1775);
x_1828 = lean_expr_mk_pi(x_1826, x_1827, x_1798, x_1821);
if (lean::is_scalar(x_1825)) {
 x_1829 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1829 = x_1825;
}
lean::cnstr_set(x_1829, 0, x_1828);
lean::cnstr_set(x_1829, 1, x_1823);
x_15 = x_1829;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1831; obj* x_1832; obj* x_1836; obj* x_1837; 
lean::dec(x_10);
x_1831 = l_lean_parser_term_lambda_has__view;
x_1832 = lean::cnstr_get(x_1831, 0);
lean::inc(x_1832);
lean::dec(x_1831);
lean::inc(x_0);
x_1836 = lean::apply_1(x_1832, x_0);
x_1837 = lean::cnstr_get(x_1836, 1);
lean::inc(x_1837);
if (lean::obj_tag(x_1837) == 0)
{
obj* x_1842; obj* x_1843; obj* x_1845; 
lean::dec(x_1836);
lean::dec(x_1837);
lean::inc(x_0);
x_1842 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1842, 0, x_0);
x_1843 = l_lean_elaborator_to__pexpr___main___closed__45;
lean::inc(x_2);
x_1845 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_1842, x_1843, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1842);
if (lean::obj_tag(x_1845) == 0)
{
obj* x_1851; obj* x_1853; obj* x_1854; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1851 = lean::cnstr_get(x_1845, 0);
if (lean::is_exclusive(x_1845)) {
 x_1853 = x_1845;
} else {
 lean::inc(x_1851);
 lean::dec(x_1845);
 x_1853 = lean::box(0);
}
if (lean::is_scalar(x_1853)) {
 x_1854 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1854 = x_1853;
}
lean::cnstr_set(x_1854, 0, x_1851);
return x_1854;
}
else
{
obj* x_1855; 
x_1855 = lean::cnstr_get(x_1845, 0);
lean::inc(x_1855);
lean::dec(x_1845);
x_15 = x_1855;
goto lbl_16;
}
}
else
{
obj* x_1858; obj* x_1861; obj* x_1862; obj* x_1864; obj* x_1867; obj* x_1869; obj* x_1873; 
x_1858 = lean::cnstr_get(x_1837, 0);
lean::inc(x_1858);
lean::dec(x_1837);
x_1861 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1858);
x_1862 = lean::cnstr_get(x_1861, 1);
lean::inc(x_1862);
x_1864 = lean::cnstr_get(x_1861, 0);
lean::inc(x_1864);
lean::dec(x_1861);
x_1867 = lean::cnstr_get(x_1862, 0);
lean::inc(x_1867);
x_1869 = lean::cnstr_get(x_1862, 1);
lean::inc(x_1869);
lean::dec(x_1862);
lean::inc(x_2);
x_1873 = l_lean_elaborator_to__pexpr___main(x_1869, x_1, x_2, x_3);
if (lean::obj_tag(x_1873) == 0)
{
obj* x_1880; obj* x_1882; obj* x_1883; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1836);
lean::dec(x_1867);
lean::dec(x_1864);
x_1880 = lean::cnstr_get(x_1873, 0);
if (lean::is_exclusive(x_1873)) {
 x_1882 = x_1873;
} else {
 lean::inc(x_1880);
 lean::dec(x_1873);
 x_1882 = lean::box(0);
}
if (lean::is_scalar(x_1882)) {
 x_1883 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1883 = x_1882;
}
lean::cnstr_set(x_1883, 0, x_1880);
return x_1883;
}
else
{
obj* x_1884; obj* x_1887; obj* x_1889; obj* x_1892; obj* x_1896; 
x_1884 = lean::cnstr_get(x_1873, 0);
lean::inc(x_1884);
lean::dec(x_1873);
x_1887 = lean::cnstr_get(x_1884, 0);
lean::inc(x_1887);
x_1889 = lean::cnstr_get(x_1884, 1);
lean::inc(x_1889);
lean::dec(x_1884);
x_1892 = lean::cnstr_get(x_1836, 3);
lean::inc(x_1892);
lean::dec(x_1836);
lean::inc(x_2);
x_1896 = l_lean_elaborator_to__pexpr___main(x_1892, x_1, x_2, x_1889);
if (lean::obj_tag(x_1896) == 0)
{
obj* x_1903; obj* x_1905; obj* x_1906; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1867);
lean::dec(x_1864);
lean::dec(x_1887);
x_1903 = lean::cnstr_get(x_1896, 0);
if (lean::is_exclusive(x_1896)) {
 x_1905 = x_1896;
} else {
 lean::inc(x_1903);
 lean::dec(x_1896);
 x_1905 = lean::box(0);
}
if (lean::is_scalar(x_1905)) {
 x_1906 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1906 = x_1905;
}
lean::cnstr_set(x_1906, 0, x_1903);
return x_1906;
}
else
{
obj* x_1907; obj* x_1910; obj* x_1912; obj* x_1914; obj* x_1915; uint8 x_1916; obj* x_1917; obj* x_1918; 
x_1907 = lean::cnstr_get(x_1896, 0);
lean::inc(x_1907);
lean::dec(x_1896);
x_1910 = lean::cnstr_get(x_1907, 0);
x_1912 = lean::cnstr_get(x_1907, 1);
if (lean::is_exclusive(x_1907)) {
 x_1914 = x_1907;
} else {
 lean::inc(x_1910);
 lean::inc(x_1912);
 lean::dec(x_1907);
 x_1914 = lean::box(0);
}
x_1915 = l_lean_elaborator_mangle__ident(x_1867);
x_1916 = lean::unbox(x_1864);
x_1917 = lean_expr_mk_lambda(x_1915, x_1916, x_1887, x_1910);
if (lean::is_scalar(x_1914)) {
 x_1918 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1918 = x_1914;
}
lean::cnstr_set(x_1918, 0, x_1917);
lean::cnstr_set(x_1918, 1, x_1912);
x_15 = x_1918;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1920; obj* x_1921; obj* x_1925; obj* x_1926; obj* x_1929; 
lean::dec(x_10);
x_1920 = l_lean_parser_term_app_has__view;
x_1921 = lean::cnstr_get(x_1920, 0);
lean::inc(x_1921);
lean::dec(x_1920);
lean::inc(x_0);
x_1925 = lean::apply_1(x_1921, x_0);
x_1926 = lean::cnstr_get(x_1925, 0);
lean::inc(x_1926);
lean::inc(x_2);
x_1929 = l_lean_elaborator_to__pexpr___main(x_1926, x_1, x_2, x_3);
if (lean::obj_tag(x_1929) == 0)
{
obj* x_1934; obj* x_1936; obj* x_1937; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1925);
x_1934 = lean::cnstr_get(x_1929, 0);
if (lean::is_exclusive(x_1929)) {
 x_1936 = x_1929;
} else {
 lean::inc(x_1934);
 lean::dec(x_1929);
 x_1936 = lean::box(0);
}
if (lean::is_scalar(x_1936)) {
 x_1937 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1937 = x_1936;
}
lean::cnstr_set(x_1937, 0, x_1934);
return x_1937;
}
else
{
obj* x_1938; obj* x_1941; obj* x_1943; obj* x_1946; obj* x_1950; 
x_1938 = lean::cnstr_get(x_1929, 0);
lean::inc(x_1938);
lean::dec(x_1929);
x_1941 = lean::cnstr_get(x_1938, 0);
lean::inc(x_1941);
x_1943 = lean::cnstr_get(x_1938, 1);
lean::inc(x_1943);
lean::dec(x_1938);
x_1946 = lean::cnstr_get(x_1925, 1);
lean::inc(x_1946);
lean::dec(x_1925);
lean::inc(x_2);
x_1950 = l_lean_elaborator_to__pexpr___main(x_1946, x_1, x_2, x_1943);
if (lean::obj_tag(x_1950) == 0)
{
obj* x_1955; obj* x_1957; obj* x_1958; 
lean::dec(x_1941);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1955 = lean::cnstr_get(x_1950, 0);
if (lean::is_exclusive(x_1950)) {
 x_1957 = x_1950;
} else {
 lean::inc(x_1955);
 lean::dec(x_1950);
 x_1957 = lean::box(0);
}
if (lean::is_scalar(x_1957)) {
 x_1958 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1958 = x_1957;
}
lean::cnstr_set(x_1958, 0, x_1955);
return x_1958;
}
else
{
obj* x_1959; obj* x_1962; obj* x_1964; obj* x_1966; obj* x_1967; obj* x_1968; 
x_1959 = lean::cnstr_get(x_1950, 0);
lean::inc(x_1959);
lean::dec(x_1950);
x_1962 = lean::cnstr_get(x_1959, 0);
x_1964 = lean::cnstr_get(x_1959, 1);
if (lean::is_exclusive(x_1959)) {
 x_1966 = x_1959;
} else {
 lean::inc(x_1962);
 lean::inc(x_1964);
 lean::dec(x_1959);
 x_1966 = lean::box(0);
}
x_1967 = lean_expr_mk_app(x_1941, x_1962);
if (lean::is_scalar(x_1966)) {
 x_1968 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1968 = x_1966;
}
lean::cnstr_set(x_1968, 0, x_1967);
lean::cnstr_set(x_1968, 1, x_1964);
x_15 = x_1968;
goto lbl_16;
}
}
}
}
else
{
obj* x_1970; obj* x_1971; obj* x_1975; obj* x_1976; 
lean::dec(x_10);
x_1970 = l_lean_parser_ident__univs_has__view;
x_1971 = lean::cnstr_get(x_1970, 0);
lean::inc(x_1971);
lean::dec(x_1970);
lean::inc(x_0);
x_1975 = lean::apply_1(x_1971, x_0);
x_1976 = lean::cnstr_get(x_1975, 1);
lean::inc(x_1976);
if (lean::obj_tag(x_1976) == 0)
{
obj* x_1978; obj* x_1982; obj* x_1983; obj* x_1984; obj* x_1985; obj* x_1988; obj* x_1989; obj* x_1990; obj* x_1991; obj* x_1992; obj* x_1993; uint8 x_1994; 
x_1978 = lean::cnstr_get(x_1975, 0);
lean::inc(x_1978);
lean::dec(x_1975);
lean::inc(x_1978);
x_1982 = l_lean_elaborator_mangle__ident(x_1978);
x_1983 = lean::box(0);
x_1984 = lean_expr_mk_const(x_1982, x_1983);
x_1985 = lean::cnstr_get(x_1978, 3);
lean::inc(x_1985);
lean::dec(x_1978);
x_1988 = lean::mk_nat_obj(0u);
x_1989 = l_list_enum__from___main___rarg(x_1988, x_1985);
x_1990 = l_lean_elaborator_to__pexpr___main___closed__46;
x_1991 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(x_1990, x_1989);
x_1992 = lean_expr_mk_mdata(x_1991, x_1984);
x_1993 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1994 = lean_name_dec_eq(x_8, x_1993);
lean::dec(x_8);
if (x_1994 == 0)
{
obj* x_1996; 
x_1996 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1996) == 0)
{
obj* x_1999; obj* x_2000; 
lean::dec(x_2);
x_1999 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1999, 0, x_1992);
lean::cnstr_set(x_1999, 1, x_3);
x_2000 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2000, 0, x_1999);
return x_2000;
}
else
{
obj* x_2001; obj* x_2004; obj* x_2007; obj* x_2010; obj* x_2011; obj* x_2013; obj* x_2014; obj* x_2015; obj* x_2018; obj* x_2019; obj* x_2020; obj* x_2021; obj* x_2022; 
x_2001 = lean::cnstr_get(x_1996, 0);
lean::inc(x_2001);
lean::dec(x_1996);
x_2004 = lean::cnstr_get(x_2, 0);
lean::inc(x_2004);
lean::dec(x_2);
x_2007 = lean::cnstr_get(x_2004, 2);
lean::inc(x_2007);
lean::dec(x_2004);
x_2010 = l_lean_file__map_to__position(x_2007, x_2001);
x_2011 = lean::cnstr_get(x_2010, 1);
lean::inc(x_2011);
x_2013 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2014 = l_lean_kvmap_set__nat(x_1983, x_2013, x_2011);
x_2015 = lean::cnstr_get(x_2010, 0);
lean::inc(x_2015);
lean::dec(x_2010);
x_2018 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2019 = l_lean_kvmap_set__nat(x_2014, x_2018, x_2015);
x_2020 = lean_expr_mk_mdata(x_2019, x_1992);
x_2021 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2021, 0, x_2020);
lean::cnstr_set(x_2021, 1, x_3);
x_2022 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2022, 0, x_2021);
return x_2022;
}
}
else
{
obj* x_2025; obj* x_2026; 
lean::dec(x_0);
lean::dec(x_2);
x_2025 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2025, 0, x_1992);
lean::cnstr_set(x_2025, 1, x_3);
x_2026 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2026, 0, x_2025);
return x_2026;
}
}
else
{
obj* x_2027; obj* x_2030; obj* x_2033; obj* x_2037; 
x_2027 = lean::cnstr_get(x_1975, 0);
lean::inc(x_2027);
lean::dec(x_1975);
x_2030 = lean::cnstr_get(x_1976, 0);
lean::inc(x_2030);
lean::dec(x_1976);
x_2033 = lean::cnstr_get(x_2030, 1);
lean::inc(x_2033);
lean::dec(x_2030);
lean::inc(x_2);
x_2037 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_2033, x_1, x_2, x_3);
if (lean::obj_tag(x_2037) == 0)
{
obj* x_2042; obj* x_2044; obj* x_2045; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2027);
x_2042 = lean::cnstr_get(x_2037, 0);
if (lean::is_exclusive(x_2037)) {
 x_2044 = x_2037;
} else {
 lean::inc(x_2042);
 lean::dec(x_2037);
 x_2044 = lean::box(0);
}
if (lean::is_scalar(x_2044)) {
 x_2045 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2045 = x_2044;
}
lean::cnstr_set(x_2045, 0, x_2042);
return x_2045;
}
else
{
obj* x_2046; obj* x_2049; obj* x_2051; obj* x_2053; obj* x_2055; obj* x_2056; obj* x_2057; obj* x_2060; obj* x_2061; obj* x_2062; obj* x_2063; obj* x_2064; obj* x_2065; 
x_2046 = lean::cnstr_get(x_2037, 0);
lean::inc(x_2046);
lean::dec(x_2037);
x_2049 = lean::cnstr_get(x_2046, 0);
x_2051 = lean::cnstr_get(x_2046, 1);
if (lean::is_exclusive(x_2046)) {
 x_2053 = x_2046;
} else {
 lean::inc(x_2049);
 lean::inc(x_2051);
 lean::dec(x_2046);
 x_2053 = lean::box(0);
}
lean::inc(x_2027);
x_2055 = l_lean_elaborator_mangle__ident(x_2027);
x_2056 = lean_expr_mk_const(x_2055, x_2049);
x_2057 = lean::cnstr_get(x_2027, 3);
lean::inc(x_2057);
lean::dec(x_2027);
x_2060 = lean::mk_nat_obj(0u);
x_2061 = l_list_enum__from___main___rarg(x_2060, x_2057);
x_2062 = l_lean_elaborator_to__pexpr___main___closed__46;
x_2063 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(x_2062, x_2061);
x_2064 = lean_expr_mk_mdata(x_2063, x_2056);
if (lean::is_scalar(x_2053)) {
 x_2065 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2065 = x_2053;
}
lean::cnstr_set(x_2065, 0, x_2064);
lean::cnstr_set(x_2065, 1, x_2051);
x_15 = x_2065;
goto lbl_16;
}
}
}
lbl_14:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_2069; obj* x_2071; obj* x_2072; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2069 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_2071 = x_13;
} else {
 lean::inc(x_2069);
 lean::dec(x_13);
 x_2071 = lean::box(0);
}
if (lean::is_scalar(x_2071)) {
 x_2072 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2072 = x_2071;
}
lean::cnstr_set(x_2072, 0, x_2069);
return x_2072;
}
else
{
obj* x_2073; obj* x_2075; obj* x_2076; obj* x_2078; obj* x_2080; obj* x_2081; uint8 x_2082; 
x_2073 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_2075 = x_13;
} else {
 lean::inc(x_2073);
 lean::dec(x_13);
 x_2075 = lean::box(0);
}
x_2076 = lean::cnstr_get(x_2073, 0);
x_2078 = lean::cnstr_get(x_2073, 1);
if (lean::is_exclusive(x_2073)) {
 lean::cnstr_set(x_2073, 0, lean::box(0));
 lean::cnstr_set(x_2073, 1, lean::box(0));
 x_2080 = x_2073;
} else {
 lean::inc(x_2076);
 lean::inc(x_2078);
 lean::dec(x_2073);
 x_2080 = lean::box(0);
}
x_2081 = l_lean_elaborator_to__pexpr___main___closed__2;
x_2082 = lean_name_dec_eq(x_8, x_2081);
lean::dec(x_8);
if (x_2082 == 0)
{
obj* x_2084; 
x_2084 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2084) == 0)
{
obj* x_2087; obj* x_2088; 
lean::dec(x_2);
if (lean::is_scalar(x_2080)) {
 x_2087 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2087 = x_2080;
}
lean::cnstr_set(x_2087, 0, x_2076);
lean::cnstr_set(x_2087, 1, x_2078);
if (lean::is_scalar(x_2075)) {
 x_2088 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2088 = x_2075;
}
lean::cnstr_set(x_2088, 0, x_2087);
return x_2088;
}
else
{
obj* x_2089; obj* x_2092; obj* x_2095; obj* x_2098; obj* x_2099; obj* x_2100; obj* x_2102; obj* x_2103; obj* x_2104; obj* x_2107; obj* x_2108; obj* x_2109; obj* x_2110; obj* x_2111; 
x_2089 = lean::cnstr_get(x_2084, 0);
lean::inc(x_2089);
lean::dec(x_2084);
x_2092 = lean::cnstr_get(x_2, 0);
lean::inc(x_2092);
lean::dec(x_2);
x_2095 = lean::cnstr_get(x_2092, 2);
lean::inc(x_2095);
lean::dec(x_2092);
x_2098 = l_lean_file__map_to__position(x_2095, x_2089);
x_2099 = lean::box(0);
x_2100 = lean::cnstr_get(x_2098, 1);
lean::inc(x_2100);
x_2102 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2103 = l_lean_kvmap_set__nat(x_2099, x_2102, x_2100);
x_2104 = lean::cnstr_get(x_2098, 0);
lean::inc(x_2104);
lean::dec(x_2098);
x_2107 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2108 = l_lean_kvmap_set__nat(x_2103, x_2107, x_2104);
x_2109 = lean_expr_mk_mdata(x_2108, x_2076);
if (lean::is_scalar(x_2080)) {
 x_2110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2110 = x_2080;
}
lean::cnstr_set(x_2110, 0, x_2109);
lean::cnstr_set(x_2110, 1, x_2078);
if (lean::is_scalar(x_2075)) {
 x_2111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2111 = x_2075;
}
lean::cnstr_set(x_2111, 0, x_2110);
return x_2111;
}
}
else
{
obj* x_2114; obj* x_2115; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2080)) {
 x_2114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2114 = x_2080;
}
lean::cnstr_set(x_2114, 0, x_2076);
lean::cnstr_set(x_2114, 1, x_2078);
if (lean::is_scalar(x_2075)) {
 x_2115 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2115 = x_2075;
}
lean::cnstr_set(x_2115, 0, x_2114);
return x_2115;
}
}
}
lbl_16:
{
obj* x_2116; obj* x_2118; obj* x_2120; obj* x_2121; uint8 x_2122; 
x_2116 = lean::cnstr_get(x_15, 0);
x_2118 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_2120 = x_15;
} else {
 lean::inc(x_2116);
 lean::inc(x_2118);
 lean::dec(x_15);
 x_2120 = lean::box(0);
}
x_2121 = l_lean_elaborator_to__pexpr___main___closed__2;
x_2122 = lean_name_dec_eq(x_8, x_2121);
lean::dec(x_8);
if (x_2122 == 0)
{
obj* x_2124; 
x_2124 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2124) == 0)
{
obj* x_2127; obj* x_2128; 
lean::dec(x_2);
if (lean::is_scalar(x_2120)) {
 x_2127 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2127 = x_2120;
}
lean::cnstr_set(x_2127, 0, x_2116);
lean::cnstr_set(x_2127, 1, x_2118);
x_2128 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2128, 0, x_2127);
return x_2128;
}
else
{
obj* x_2129; obj* x_2132; obj* x_2135; obj* x_2138; obj* x_2139; obj* x_2140; obj* x_2142; obj* x_2143; obj* x_2144; obj* x_2147; obj* x_2148; obj* x_2149; obj* x_2150; obj* x_2151; 
x_2129 = lean::cnstr_get(x_2124, 0);
lean::inc(x_2129);
lean::dec(x_2124);
x_2132 = lean::cnstr_get(x_2, 0);
lean::inc(x_2132);
lean::dec(x_2);
x_2135 = lean::cnstr_get(x_2132, 2);
lean::inc(x_2135);
lean::dec(x_2132);
x_2138 = l_lean_file__map_to__position(x_2135, x_2129);
x_2139 = lean::box(0);
x_2140 = lean::cnstr_get(x_2138, 1);
lean::inc(x_2140);
x_2142 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2143 = l_lean_kvmap_set__nat(x_2139, x_2142, x_2140);
x_2144 = lean::cnstr_get(x_2138, 0);
lean::inc(x_2144);
lean::dec(x_2138);
x_2147 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2148 = l_lean_kvmap_set__nat(x_2143, x_2147, x_2144);
x_2149 = lean_expr_mk_mdata(x_2148, x_2116);
if (lean::is_scalar(x_2120)) {
 x_2150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2150 = x_2120;
}
lean::cnstr_set(x_2150, 0, x_2149);
lean::cnstr_set(x_2150, 1, x_2118);
x_2151 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2151, 0, x_2150);
return x_2151;
}
}
else
{
obj* x_2154; obj* x_2155; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2120)) {
 x_2154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2154 = x_2120;
}
lean::cnstr_set(x_2154, 0, x_2116);
lean::cnstr_set(x_2154, 1, x_2118);
x_2155 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2155, 0, x_2154);
return x_2155;
}
}
}
default:
{
obj* x_2156; 
x_2156 = lean::box(0);
x_4 = x_2156;
goto lbl_5;
}
}
lbl_5:
{
obj* x_2159; obj* x_2160; obj* x_2161; obj* x_2162; obj* x_2163; obj* x_2164; obj* x_2166; 
lean::dec(x_4);
lean::inc(x_0);
x_2159 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2159, 0, x_0);
x_2160 = l_lean_parser_syntax_to__format___main(x_0);
x_2161 = lean::mk_nat_obj(80u);
x_2162 = l_lean_format_pretty(x_2160, x_2161);
x_2163 = l_lean_elaborator_to__pexpr___main___closed__1;
x_2164 = lean::string_append(x_2163, x_2162);
lean::dec(x_2162);
x_2166 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_2159, x_2164, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2159);
return x_2166;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__20___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__20(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_to__pexpr___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_to__pexpr___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_to__pexpr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_to__pexpr___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_to__pexpr___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_to__pexpr(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_get__namespace(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_current__scope(x_0, x_1, x_2);
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; 
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
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 6);
lean::inc(x_13);
lean::dec(x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_18 = x_8;
} else {
 lean::inc(x_16);
 lean::dec(x_8);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
if (lean::is_scalar(x_10)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_10;
}
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_24 = x_8;
} else {
 lean::inc(x_22);
 lean::dec(x_8);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
lean::dec(x_13);
if (lean::is_scalar(x_24)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_24;
}
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_22);
if (lean::is_scalar(x_10)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_10;
}
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
}
}
}
obj* l_lean_elaborator_get__namespace___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_get__namespace(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___rarg), 3, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___rarg), 3, 0);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___rarg), 3, 0);
return x_2;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_16 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___rarg(x_9, x_1, x_15);
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
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
return x_2;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_14; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_14 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2___rarg(x_2, x_9, x_11);
x_1 = x_0;
x_2 = x_14;
x_3 = x_6;
goto _start;
}
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
return x_0;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
x_3 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8(x_1, lean::box(0), x_2, x_0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___rarg), 3, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___rarg), 3, 0);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12___rarg), 3, 0);
return x_2;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_16 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12___rarg(x_9, x_1, x_15);
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
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__15(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
return x_2;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_14; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_14 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10___rarg(x_2, x_9, x_11);
x_1 = x_0;
x_2 = x_14;
x_3 = x_6;
goto _start;
}
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
return x_0;
}
}
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9___closed__1;
x_3 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16(x_1, lean::box(0), x_2, x_0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___rarg), 3, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___rarg), 3, 0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19___rarg), 3, 0);
return x_1;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18___rarg), 3, 0);
return x_2;
}
}
obj* l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__17(obj* x_0) {
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
x_7 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__17(x_4);
x_8 = lean::box(0);
x_9 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19___rarg(x_7, x_2, x_8);
return x_9;
}
}
}
obj* l_lean_elaborator_old__elab__command___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1(x_8);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
x_13 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9(x_11);
x_14 = lean::cnstr_get(x_0, 4);
lean::inc(x_14);
x_16 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__17(x_14);
x_17 = lean::cnstr_get(x_1, 6);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 7);
lean::inc(x_19);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_0, 5);
lean::inc(x_22);
lean::dec(x_0);
x_25 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_10);
lean::cnstr_set(x_25, 4, x_13);
lean::cnstr_set(x_25, 5, x_16);
lean::cnstr_set(x_25, 6, x_17);
lean::cnstr_set(x_25, 7, x_19);
lean::cnstr_set(x_25, 8, x_22);
return x_25;
}
}
obj* l_lean_elaborator_old__elab__command(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_9 = l_lean_elaborator_current__scope(x_2, x_3, x_4);
switch (lean::obj_tag(x_1)) {
case 10:
{
obj* x_12; obj* x_14; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_33; 
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_5, 2);
lean::inc(x_17);
x_19 = l_lean_parser_syntax_get__pos(x_0);
x_20 = lean::mk_nat_obj(0u);
x_21 = l_option_get__or__else___main___rarg(x_19, x_20);
lean::dec(x_19);
x_23 = l_lean_file__map_to__position(x_17, x_21);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
x_26 = l_lean_elaborator_to__pexpr___main___closed__3;
x_27 = l_lean_kvmap_set__nat(x_12, x_26, x_24);
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
lean::dec(x_23);
x_31 = l_lean_elaborator_to__pexpr___main___closed__4;
x_32 = l_lean_kvmap_set__nat(x_27, x_31, x_28);
x_33 = lean_expr_mk_mdata(x_32, x_14);
x_10 = x_33;
goto lbl_11;
}
default:
{
x_10 = x_1;
goto lbl_11;
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_10);
x_38 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_40 = x_9;
} else {
 lean::inc(x_38);
 lean::dec(x_9);
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
obj* x_42; obj* x_45; obj* x_47; obj* x_51; 
x_42 = lean::cnstr_get(x_9, 0);
lean::inc(x_42);
lean::dec(x_9);
x_45 = lean::cnstr_get(x_42, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
lean::dec(x_42);
lean::inc(x_3);
x_51 = l_lean_elaborator_get__namespace(x_2, x_3, x_47);
if (lean::obj_tag(x_51) == 0)
{
obj* x_57; obj* x_59; obj* x_60; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_10);
lean::dec(x_45);
x_57 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_59 = x_51;
} else {
 lean::inc(x_57);
 lean::dec(x_51);
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
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_69; obj* x_72; obj* x_74; obj* x_76; obj* x_78; obj* x_81; obj* x_82; obj* x_84; obj* x_87; obj* x_88; obj* x_90; obj* x_91; obj* x_94; obj* x_97; obj* x_98; obj* x_101; 
x_61 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 x_63 = x_51;
} else {
 lean::inc(x_61);
 lean::dec(x_51);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
lean::dec(x_61);
x_69 = lean::cnstr_get(x_5, 0);
lean::inc(x_69);
lean::dec(x_5);
x_72 = lean::cnstr_get(x_4, 8);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_4, 9);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_45, 3);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_76, 0);
lean::inc(x_78);
lean::dec(x_76);
x_81 = l_list_reverse___rarg(x_78);
x_82 = lean::cnstr_get(x_45, 4);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_82, 0);
lean::inc(x_84);
lean::dec(x_82);
x_87 = l_list_reverse___rarg(x_84);
x_88 = lean::cnstr_get(x_45, 5);
lean::inc(x_88);
x_90 = l_rbtree_to__list___rarg(x_88);
x_91 = lean::cnstr_get(x_45, 8);
lean::inc(x_91);
lean::dec(x_45);
x_94 = lean::cnstr_get(x_4, 10);
lean::inc(x_94);
lean::dec(x_4);
x_97 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_97, 0, x_72);
lean::cnstr_set(x_97, 1, x_74);
lean::cnstr_set(x_97, 2, x_81);
lean::cnstr_set(x_97, 3, x_87);
lean::cnstr_set(x_97, 4, x_90);
lean::cnstr_set(x_97, 5, x_91);
lean::cnstr_set(x_97, 6, x_94);
lean::cnstr_set(x_97, 7, x_64);
x_98 = lean_elaborator_elaborate_command(x_69, x_10, x_97);
lean::dec(x_97);
lean::dec(x_69);
x_101 = lean::cnstr_get(x_98, 0);
lean::inc(x_101);
if (lean::obj_tag(x_101) == 0)
{
obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_3);
x_104 = lean::cnstr_get(x_98, 1);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_106 = x_98;
} else {
 lean::inc(x_104);
 lean::dec(x_98);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_66, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_66, 1);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_66, 2);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_66, 3);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_66, 4);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_66, 5);
lean::inc(x_117);
x_119 = l_list_append___rarg(x_104, x_117);
x_120 = lean::cnstr_get(x_66, 6);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_66, 7);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_66, 8);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_66, 9);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_66, 10);
lean::inc(x_128);
lean::dec(x_66);
x_131 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_131, 0, x_107);
lean::cnstr_set(x_131, 1, x_109);
lean::cnstr_set(x_131, 2, x_111);
lean::cnstr_set(x_131, 3, x_113);
lean::cnstr_set(x_131, 4, x_115);
lean::cnstr_set(x_131, 5, x_119);
lean::cnstr_set(x_131, 6, x_120);
lean::cnstr_set(x_131, 7, x_122);
lean::cnstr_set(x_131, 8, x_124);
lean::cnstr_set(x_131, 9, x_126);
lean::cnstr_set(x_131, 10, x_128);
x_132 = lean::box(0);
if (lean::is_scalar(x_106)) {
 x_133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_133 = x_106;
}
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_131);
if (lean::is_scalar(x_63)) {
 x_134 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_134 = x_63;
}
lean::cnstr_set(x_134, 0, x_133);
return x_134;
}
else
{
obj* x_136; obj* x_139; obj* x_143; obj* x_144; 
lean::dec(x_63);
x_136 = lean::cnstr_get(x_98, 1);
lean::inc(x_136);
lean::dec(x_98);
x_139 = lean::cnstr_get(x_101, 0);
lean::inc(x_139);
lean::dec(x_101);
lean::inc(x_139);
x_143 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_old__elab__command___lambda__1), 2, 1);
lean::closure_set(x_143, 0, x_139);
x_144 = l_lean_elaborator_modify__current__scope(x_143, x_2, x_3, x_66);
if (lean::obj_tag(x_144) == 0)
{
obj* x_147; obj* x_149; obj* x_150; 
lean::dec(x_139);
lean::dec(x_136);
x_147 = lean::cnstr_get(x_144, 0);
if (lean::is_exclusive(x_144)) {
 x_149 = x_144;
} else {
 lean::inc(x_147);
 lean::dec(x_144);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_147);
return x_150;
}
else
{
obj* x_151; obj* x_153; obj* x_154; obj* x_156; obj* x_157; obj* x_159; obj* x_161; obj* x_163; obj* x_165; obj* x_167; obj* x_169; obj* x_171; obj* x_174; obj* x_176; obj* x_178; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
x_151 = lean::cnstr_get(x_144, 0);
if (lean::is_exclusive(x_144)) {
 x_153 = x_144;
} else {
 lean::inc(x_151);
 lean::dec(x_144);
 x_153 = lean::box(0);
}
x_154 = lean::cnstr_get(x_151, 1);
if (lean::is_exclusive(x_151)) {
 lean::cnstr_release(x_151, 0);
 x_156 = x_151;
} else {
 lean::inc(x_154);
 lean::dec(x_151);
 x_156 = lean::box(0);
}
x_157 = lean::cnstr_get(x_154, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_154, 1);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_154, 2);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_154, 3);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_154, 4);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_154, 5);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_154, 6);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_154, 7);
lean::inc(x_171);
lean::dec(x_154);
x_174 = lean::cnstr_get(x_139, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_139, 1);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_139, 6);
lean::inc(x_178);
lean::dec(x_139);
x_181 = l_list_append___rarg(x_136, x_167);
x_182 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_182, 0, x_157);
lean::cnstr_set(x_182, 1, x_159);
lean::cnstr_set(x_182, 2, x_161);
lean::cnstr_set(x_182, 3, x_163);
lean::cnstr_set(x_182, 4, x_165);
lean::cnstr_set(x_182, 5, x_181);
lean::cnstr_set(x_182, 6, x_169);
lean::cnstr_set(x_182, 7, x_171);
lean::cnstr_set(x_182, 8, x_174);
lean::cnstr_set(x_182, 9, x_176);
lean::cnstr_set(x_182, 10, x_178);
x_183 = lean::box(0);
if (lean::is_scalar(x_156)) {
 x_184 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_184 = x_156;
}
lean::cnstr_set(x_184, 0, x_183);
lean::cnstr_set(x_184, 1, x_182);
if (lean::is_scalar(x_153)) {
 x_185 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_185 = x_153;
}
lean::cnstr_set(x_185, 0, x_184);
return x_185;
}
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__7(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__15___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__15(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_old__elab__command___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_elaborator_old__elab__command(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
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
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_lean_elaborator_to__pexpr___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
x_30 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
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
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::inc(x_2);
x_19 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_16, x_1, x_2, x_3);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_10);
lean::dec(x_12);
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
x_36 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(x_10, x_1, x_2, x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_31);
x_40 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_42 = x_36;
} else {
 lean::inc(x_40);
 lean::dec(x_36);
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
obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_55; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_44 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_46 = x_36;
} else {
 lean::inc(x_44);
 lean::dec(x_36);
 x_46 = lean::box(0);
}
x_47 = lean::cnstr_get(x_44, 0);
x_49 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_51 = x_44;
} else {
 lean::inc(x_47);
 lean::inc(x_49);
 lean::dec(x_44);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_13, 0);
lean::inc(x_52);
lean::dec(x_13);
x_55 = lean::cnstr_get(x_52, 2);
lean::inc(x_55);
lean::dec(x_52);
x_58 = l_lean_expr_mk__capp(x_55, x_31);
if (lean::is_scalar(x_12)) {
 x_59 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_59 = x_12;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_47);
if (lean::is_scalar(x_51)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_51;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_49);
if (lean::is_scalar(x_46)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_46;
}
lean::cnstr_set(x_61, 0, x_60);
return x_61;
}
}
}
}
}
obj* l_lean_elaborator_attrs__to__pexpr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(x_0, x_1, x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
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
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
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
x_17 = l_lean_elaborator_mk__eqns___closed__1;
x_18 = l_lean_expr_mk__capp(x_17, x_12);
if (lean::is_scalar(x_16)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_16;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_14);
if (lean::is_scalar(x_11)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_11;
}
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_attrs__to__pexpr___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_attrs__to__pexpr(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_lean_elaborator_decl__modifiers__to__pexpr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; uint8 x_11; obj* x_13; uint8 x_15; obj* x_17; obj* x_20; 
x_4 = lean::box(0);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
x_11 = l_option_is__some___main___rarg(x_9);
lean::dec(x_9);
x_13 = lean::cnstr_get(x_0, 4);
lean::inc(x_13);
x_15 = l_option_is__some___main___rarg(x_13);
lean::dec(x_13);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
x_20 = x_4;
goto lbl_21;
}
else
{
obj* x_22; 
x_22 = lean::cnstr_get(x_7, 0);
lean::inc(x_22);
lean::dec(x_7);
if (lean::obj_tag(x_22) == 0)
{
obj* x_26; 
lean::dec(x_22);
x_26 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
x_20 = x_26;
goto lbl_21;
}
else
{
obj* x_28; 
lean::dec(x_22);
x_28 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
x_20 = x_28;
goto lbl_21;
}
}
}
else
{
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_5, 0);
lean::inc(x_29);
lean::dec(x_5);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_32) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
x_20 = x_4;
goto lbl_21;
}
else
{
obj* x_35; 
x_35 = lean::cnstr_get(x_7, 0);
lean::inc(x_35);
lean::dec(x_7);
if (lean::obj_tag(x_35) == 0)
{
obj* x_39; 
lean::dec(x_35);
x_39 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
x_20 = x_39;
goto lbl_21;
}
else
{
obj* x_41; 
lean::dec(x_35);
x_41 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
x_20 = x_41;
goto lbl_21;
}
}
}
else
{
obj* x_42; obj* x_45; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_32, 0);
lean::inc(x_42);
lean::dec(x_32);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
x_48 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
x_49 = l_lean_kvmap_set__string(x_4, x_48, x_45);
if (lean::obj_tag(x_7) == 0)
{
x_20 = x_49;
goto lbl_21;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_7, 0);
lean::inc(x_50);
lean::dec(x_7);
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; uint8 x_55; obj* x_56; 
lean::dec(x_50);
x_54 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
x_55 = 1;
x_56 = l_lean_kvmap_set__bool(x_49, x_54, x_55);
x_20 = x_56;
goto lbl_21;
}
else
{
obj* x_58; uint8 x_59; obj* x_60; 
lean::dec(x_50);
x_58 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
x_59 = 1;
x_60 = l_lean_kvmap_set__bool(x_49, x_58, x_59);
x_20 = x_60;
goto lbl_21;
}
}
}
}
lbl_21:
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_61 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
x_62 = l_lean_kvmap_set__bool(x_20, x_61, x_11);
x_63 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
x_64 = l_lean_kvmap_set__bool(x_62, x_63, x_15);
if (lean::obj_tag(x_17) == 0)
{
obj* x_65; 
x_65 = l_lean_elaborator_attrs__to__pexpr(x_4, x_1, x_2, x_3);
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
x_82 = lean::cnstr_get(x_17, 0);
lean::inc(x_82);
lean::dec(x_17);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
x_88 = l_lean_elaborator_attrs__to__pexpr(x_85, x_1, x_2, x_3);
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
obj* l_lean_elaborator_decl__modifiers__to__pexpr___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_decl__modifiers__to__pexpr(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_lean_elaborator_locally(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_2);
x_5 = l_lean_elaborator_current__scope(x_1, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_11 = x_5;
} else {
 lean::inc(x_9);
 lean::dec(x_5);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_18; obj* x_23; 
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
lean::dec(x_5);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::dec(x_13);
lean::inc(x_2);
lean::inc(x_1);
x_23 = lean::apply_3(x_0, x_1, x_2, x_18);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_29 = x_23;
} else {
 lean::inc(x_27);
 lean::dec(x_23);
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
obj* x_31; obj* x_34; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_23, 0);
lean::inc(x_31);
lean::dec(x_23);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad___rarg___lambda__8___boxed), 2, 1);
lean::closure_set(x_37, 0, x_16);
x_38 = l_lean_elaborator_modify__current__scope(x_37, x_1, x_2, x_34);
lean::dec(x_1);
return x_38;
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_19; obj* x_21; obj* x_25; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_8);
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_14, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 1);
lean::inc(x_21);
lean::dec(x_14);
lean::inc(x_2);
x_25 = l_lean_elaborator_to__pexpr___main(x_21, x_1, x_2, x_3);
if (lean::obj_tag(x_25) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_16);
lean::dec(x_19);
x_31 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_33 = x_25;
} else {
 lean::inc(x_31);
 lean::dec(x_25);
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
x_35 = lean::cnstr_get(x_25, 0);
lean::inc(x_35);
lean::dec(x_25);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
x_43 = l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(x_10, x_1, x_2, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_12);
lean::dec(x_38);
lean::dec(x_16);
lean::dec(x_19);
x_48 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_48);
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
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; uint8 x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_52 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_54 = x_43;
} else {
 lean::inc(x_52);
 lean::dec(x_43);
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
x_60 = l_lean_elaborator_mangle__ident(x_19);
x_61 = lean::unbox(x_16);
lean::inc(x_60);
x_63 = lean_expr_local(x_60, x_60, x_38, x_61);
if (lean::is_scalar(x_12)) {
 x_64 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_64 = x_12;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_55);
if (lean::is_scalar(x_59)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_59;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_57);
if (lean::is_scalar(x_54)) {
 x_66 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_66 = x_54;
}
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
}
}
}
}
obj* l_lean_elaborator_simple__binders__to__pexpr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(x_0, x_1, x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
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
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
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
x_17 = l_lean_elaborator_mk__eqns___closed__1;
x_18 = l_lean_expr_mk__capp(x_17, x_12);
if (lean::is_scalar(x_16)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_16;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_14);
if (lean::is_scalar(x_11)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_11;
}
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_simple__binders__to__pexpr___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_simple__binders__to__pexpr(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_lean_elaborator_to__pexpr___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
x_30 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
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
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_5);
lean::dec(x_2);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_20; 
x_12 = lean::cnstr_get(x_3, 0);
x_14 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_16 = x_3;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_3);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::inc(x_5);
x_20 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_17, x_4, x_5, x_6);
if (lean::obj_tag(x_20) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_5);
lean::dec(x_12);
lean::dec(x_14);
lean::dec(x_2);
lean::dec(x_16);
x_26 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_28 = x_20;
} else {
 lean::inc(x_26);
 lean::dec(x_20);
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
obj* x_30; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_42; 
x_30 = lean::cnstr_get(x_20, 0);
lean::inc(x_30);
lean::dec(x_20);
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
x_38 = lean::cnstr_get(x_12, 3);
lean::inc(x_38);
lean::dec(x_12);
lean::inc(x_5);
x_42 = l_lean_elaborator_to__pexpr___main(x_38, x_4, x_5, x_35);
if (lean::obj_tag(x_42) == 0)
{
obj* x_49; obj* x_51; obj* x_52; 
lean::dec(x_5);
lean::dec(x_14);
lean::dec(x_2);
lean::dec(x_33);
lean::dec(x_16);
lean::dec(x_37);
x_49 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_51 = x_42;
} else {
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
return x_52;
}
else
{
obj* x_53; obj* x_56; obj* x_58; obj* x_60; obj* x_62; 
x_53 = lean::cnstr_get(x_42, 0);
lean::inc(x_53);
lean::dec(x_42);
x_56 = lean::cnstr_get(x_53, 0);
x_58 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_set(x_53, 0, lean::box(0));
 lean::cnstr_set(x_53, 1, lean::box(0));
 x_60 = x_53;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_53);
 x_60 = lean::box(0);
}
lean::inc(x_2);
x_62 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_0, x_1, x_2, x_14, x_4, x_5, x_58);
if (lean::obj_tag(x_62) == 0)
{
obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_2);
lean::dec(x_60);
lean::dec(x_33);
lean::dec(x_16);
lean::dec(x_37);
lean::dec(x_56);
x_69 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_71 = x_62;
} else {
 lean::inc(x_69);
 lean::dec(x_62);
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
obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_73 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_75 = x_62;
} else {
 lean::inc(x_73);
 lean::dec(x_62);
 x_75 = lean::box(0);
}
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
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_33);
lean::cnstr_set(x_81, 1, x_56);
if (lean::is_scalar(x_60)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_60;
}
lean::cnstr_set(x_82, 0, x_2);
lean::cnstr_set(x_82, 1, x_81);
if (lean::is_scalar(x_16)) {
 x_83 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_83 = x_16;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_76);
if (lean::is_scalar(x_37)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_37;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_78);
if (lean::is_scalar(x_75)) {
 x_85 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_85 = x_75;
}
lean::cnstr_set(x_85, 0, x_84);
return x_85;
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
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___rarg), 3, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___rarg), 3, 0);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6___rarg), 3, 0);
return x_2;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5___rarg), 3, 0);
return x_2;
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
x_16 = l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6___rarg(x_9, x_1, x_15);
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
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__9(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__9(x_4);
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
obj* l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__10(obj* x_0, obj* x_1) {
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
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__11(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__11(x_4);
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
obj* l_lean_elaborator_elab__def__like___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__9(x_10);
x_14 = l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__10(x_8, x_13);
x_15 = lean::cnstr_get(x_1, 4);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 5);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 6);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 7);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_1, 8);
lean::inc(x_23);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_26, 0, x_2);
lean::cnstr_set(x_26, 1, x_4);
lean::cnstr_set(x_26, 2, x_6);
lean::cnstr_set(x_26, 3, x_14);
lean::cnstr_set(x_26, 4, x_15);
lean::cnstr_set(x_26, 5, x_17);
lean::cnstr_set(x_26, 6, x_19);
lean::cnstr_set(x_26, 7, x_21);
lean::cnstr_set(x_26, 8, x_23);
return x_26;
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
obj* l_lean_elaborator_elab__def__like(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_0);
x_17 = l_lean_elaborator_elab__def__like___closed__1;
x_18 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_16, x_17, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_16);
return x_18;
}
else
{
obj* x_21; obj* x_23; obj* x_25; obj* x_28; obj* x_31; obj* x_35; 
x_21 = lean::cnstr_get(x_2, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 4);
lean::inc(x_25);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_7, 1);
lean::inc(x_28);
lean::dec(x_7);
x_31 = lean::cnstr_get(x_9, 0);
lean::inc(x_31);
lean::dec(x_9);
lean::inc(x_5);
x_35 = l_lean_elaborator_decl__modifiers__to__pexpr(x_1, x_4, x_5, x_6);
if (lean::obj_tag(x_35) == 0)
{
obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_28);
x_44 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_46 = x_35;
} else {
 lean::inc(x_44);
 lean::dec(x_35);
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
obj* x_48; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_48 = lean::cnstr_get(x_35, 0);
lean::inc(x_48);
lean::dec(x_35);
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
lean::dec(x_48);
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_57, 0, x_3);
x_58 = lean_expr_mk_lit(x_57);
if (lean::obj_tag(x_21) == 0)
{
obj* x_62; obj* x_65; 
x_62 = l_lean_expander_get__opt__type___main(x_28);
lean::dec(x_28);
lean::inc(x_5);
x_65 = l_lean_elaborator_to__pexpr___main(x_62, x_4, x_5, x_53);
if (lean::obj_tag(x_21) == 0)
{
if (lean::obj_tag(x_65) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_51);
x_73 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_75 = x_65;
} else {
 lean::inc(x_73);
 lean::dec(x_65);
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
x_77 = lean::cnstr_get(x_65, 0);
lean::inc(x_77);
lean::dec(x_65);
x_59 = x_56;
x_60 = x_77;
goto lbl_61;
}
}
else
{
if (lean::obj_tag(x_65) == 0)
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_51);
x_87 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_89 = x_65;
} else {
 lean::inc(x_87);
 lean::dec(x_65);
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
obj* x_91; obj* x_94; obj* x_97; obj* x_100; 
x_91 = lean::cnstr_get(x_21, 0);
lean::inc(x_91);
lean::dec(x_21);
x_94 = lean::cnstr_get(x_65, 0);
lean::inc(x_94);
lean::dec(x_65);
x_97 = lean::cnstr_get(x_91, 1);
lean::inc(x_97);
lean::dec(x_91);
x_100 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(x_97);
x_59 = x_100;
x_60 = x_94;
goto lbl_61;
}
}
}
else
{
obj* x_101; obj* x_104; obj* x_106; 
x_101 = lean::cnstr_get(x_21, 0);
lean::inc(x_101);
lean::inc(x_101);
x_104 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___lambda__1), 2, 1);
lean::closure_set(x_104, 0, x_101);
lean::inc(x_5);
x_106 = l_lean_elaborator_modify__current__scope(x_104, x_4, x_5, x_53);
if (lean::obj_tag(x_106) == 0)
{
obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_28);
lean::dec(x_51);
lean::dec(x_101);
x_117 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 x_119 = x_106;
} else {
 lean::inc(x_117);
 lean::dec(x_106);
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
obj* x_121; obj* x_124; obj* x_127; obj* x_130; 
x_121 = lean::cnstr_get(x_106, 0);
lean::inc(x_121);
lean::dec(x_106);
x_124 = lean::cnstr_get(x_121, 1);
lean::inc(x_124);
lean::dec(x_121);
x_127 = l_lean_expander_get__opt__type___main(x_28);
lean::dec(x_28);
lean::inc(x_5);
x_130 = l_lean_elaborator_to__pexpr___main(x_127, x_4, x_5, x_124);
if (lean::obj_tag(x_21) == 0)
{
lean::dec(x_101);
if (lean::obj_tag(x_130) == 0)
{
obj* x_139; obj* x_141; obj* x_142; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_51);
x_139 = lean::cnstr_get(x_130, 0);
if (lean::is_exclusive(x_130)) {
 x_141 = x_130;
} else {
 lean::inc(x_139);
 lean::dec(x_130);
 x_141 = lean::box(0);
}
if (lean::is_scalar(x_141)) {
 x_142 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_142 = x_141;
}
lean::cnstr_set(x_142, 0, x_139);
return x_142;
}
else
{
obj* x_143; 
x_143 = lean::cnstr_get(x_130, 0);
lean::inc(x_143);
lean::dec(x_130);
x_59 = x_56;
x_60 = x_143;
goto lbl_61;
}
}
else
{
lean::dec(x_21);
if (lean::obj_tag(x_130) == 0)
{
obj* x_155; obj* x_157; obj* x_158; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_51);
lean::dec(x_101);
x_155 = lean::cnstr_get(x_130, 0);
if (lean::is_exclusive(x_130)) {
 x_157 = x_130;
} else {
 lean::inc(x_155);
 lean::dec(x_130);
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
obj* x_159; obj* x_162; obj* x_165; 
x_159 = lean::cnstr_get(x_130, 0);
lean::inc(x_159);
lean::dec(x_130);
x_162 = lean::cnstr_get(x_101, 1);
lean::inc(x_162);
lean::dec(x_101);
x_165 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__11(x_162);
x_59 = x_165;
x_60 = x_159;
goto lbl_61;
}
}
}
}
lbl_61:
{
obj* x_166; obj* x_168; obj* x_170; obj* x_171; obj* x_172; obj* x_175; uint8 x_176; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; 
x_166 = lean::cnstr_get(x_60, 0);
x_168 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_set(x_60, 0, lean::box(0));
 lean::cnstr_set(x_60, 1, lean::box(0));
 x_170 = x_60;
} else {
 lean::inc(x_166);
 lean::inc(x_168);
 lean::dec(x_60);
 x_170 = lean::box(0);
}
x_171 = l_lean_elaborator_names__to__pexpr(x_59);
x_172 = lean::cnstr_get(x_23, 0);
lean::inc(x_172);
lean::inc(x_172);
x_175 = l_lean_elaborator_mangle__ident(x_172);
x_176 = 4;
lean::inc(x_166);
lean::inc(x_175);
lean::inc(x_175);
x_180 = lean_expr_local(x_175, x_175, x_166, x_176);
x_181 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_181, 0, x_180);
lean::cnstr_set(x_181, 1, x_56);
x_182 = l_lean_elaborator_mk__eqns___closed__1;
x_183 = l_lean_expr_mk__capp(x_182, x_181);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_191; obj* x_194; obj* x_198; 
lean::dec(x_170);
lean::dec(x_175);
lean::dec(x_23);
lean::dec(x_166);
lean::dec(x_172);
x_191 = lean::cnstr_get(x_25, 0);
lean::inc(x_191);
lean::dec(x_25);
x_194 = lean::cnstr_get(x_191, 1);
lean::inc(x_194);
lean::dec(x_191);
lean::inc(x_5);
x_198 = l_lean_elaborator_to__pexpr___main(x_194, x_4, x_5, x_168);
if (lean::obj_tag(x_198) == 0)
{
obj* x_206; obj* x_208; obj* x_209; 
lean::dec(x_183);
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_51);
lean::dec(x_171);
x_206 = lean::cnstr_get(x_198, 0);
if (lean::is_exclusive(x_198)) {
 x_208 = x_198;
} else {
 lean::inc(x_206);
 lean::dec(x_198);
 x_208 = lean::box(0);
}
if (lean::is_scalar(x_208)) {
 x_209 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_209 = x_208;
}
lean::cnstr_set(x_209, 0, x_206);
return x_209;
}
else
{
obj* x_210; 
x_210 = lean::cnstr_get(x_198, 0);
lean::inc(x_210);
lean::dec(x_198);
x_184 = x_210;
goto lbl_185;
}
}
case 1:
{
obj* x_217; obj* x_218; 
lean::dec(x_175);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_172);
x_217 = l_lean_elaborator_mk__eqns(x_166, x_56);
if (lean::is_scalar(x_170)) {
 x_218 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_218 = x_170;
}
lean::cnstr_set(x_218, 0, x_217);
lean::cnstr_set(x_218, 1, x_168);
x_184 = x_218;
goto lbl_185;
}
default:
{
obj* x_220; obj* x_224; 
lean::dec(x_170);
x_220 = lean::cnstr_get(x_25, 0);
lean::inc(x_220);
lean::dec(x_25);
lean::inc(x_5);
x_224 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_23, x_172, x_175, x_220, x_4, x_5, x_168);
lean::dec(x_172);
lean::dec(x_23);
if (lean::obj_tag(x_224) == 0)
{
obj* x_235; obj* x_237; obj* x_238; 
lean::dec(x_183);
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_51);
lean::dec(x_166);
lean::dec(x_171);
x_235 = lean::cnstr_get(x_224, 0);
if (lean::is_exclusive(x_224)) {
 x_237 = x_224;
} else {
 lean::inc(x_235);
 lean::dec(x_224);
 x_237 = lean::box(0);
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
obj* x_239; obj* x_242; obj* x_244; obj* x_246; obj* x_247; obj* x_248; 
x_239 = lean::cnstr_get(x_224, 0);
lean::inc(x_239);
lean::dec(x_224);
x_242 = lean::cnstr_get(x_239, 0);
x_244 = lean::cnstr_get(x_239, 1);
if (lean::is_exclusive(x_239)) {
 x_246 = x_239;
} else {
 lean::inc(x_242);
 lean::inc(x_244);
 lean::dec(x_239);
 x_246 = lean::box(0);
}
x_247 = l_lean_elaborator_mk__eqns(x_166, x_242);
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_247);
lean::cnstr_set(x_248, 1, x_244);
x_184 = x_248;
goto lbl_185;
}
}
}
lbl_185:
{
obj* x_249; obj* x_251; obj* x_255; 
x_249 = lean::cnstr_get(x_184, 0);
lean::inc(x_249);
x_251 = lean::cnstr_get(x_184, 1);
lean::inc(x_251);
lean::dec(x_184);
lean::inc(x_5);
x_255 = l_lean_elaborator_simple__binders__to__pexpr(x_31, x_4, x_5, x_251);
if (lean::obj_tag(x_255) == 0)
{
obj* x_263; obj* x_265; obj* x_266; 
lean::dec(x_249);
lean::dec(x_183);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_51);
lean::dec(x_171);
x_263 = lean::cnstr_get(x_255, 0);
if (lean::is_exclusive(x_255)) {
 x_265 = x_255;
} else {
 lean::inc(x_263);
 lean::dec(x_255);
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
x_267 = lean::cnstr_get(x_255, 0);
lean::inc(x_267);
lean::dec(x_255);
x_270 = lean::cnstr_get(x_267, 0);
lean::inc(x_270);
x_272 = lean::cnstr_get(x_267, 1);
lean::inc(x_272);
lean::dec(x_267);
x_275 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_275, 0, x_249);
lean::cnstr_set(x_275, 1, x_56);
x_276 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_276, 0, x_270);
lean::cnstr_set(x_276, 1, x_275);
x_277 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_277, 0, x_183);
lean::cnstr_set(x_277, 1, x_276);
x_278 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_278, 0, x_171);
lean::cnstr_set(x_278, 1, x_277);
x_279 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_279, 0, x_58);
lean::cnstr_set(x_279, 1, x_278);
x_280 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_280, 0, x_51);
lean::cnstr_set(x_280, 1, x_279);
x_281 = l_lean_expr_mk__capp(x_182, x_280);
x_282 = l_lean_elaborator_elab__def__like___closed__2;
x_283 = lean_expr_mk_mdata(x_282, x_281);
x_284 = l_lean_elaborator_old__elab__command(x_0, x_283, x_4, x_5, x_272);
lean::dec(x_0);
return x_284;
}
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_4);
return x_7;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_elab__def__like___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_lean_elaborator_elab__def__like(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
return x_7;
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
obj* l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; 
lean::inc(x_3);
lean::inc(x_2);
x_7 = lean::apply_3(x_0, x_2, x_3, x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_13 = x_7;
} else {
 lean::inc(x_11);
 lean::dec(x_7);
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
obj* x_15; obj* x_18; obj* x_20; obj* x_23; 
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
lean::dec(x_7);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
lean::dec(x_15);
x_23 = lean::apply_4(x_1, x_18, x_2, x_3, x_20);
return x_23;
}
}
}
obj* l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("declaration.elaborate: unexpected input");
return x_0;
}
}
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_10 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_14 = x_1;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
x_17 = lean::cnstr_get(x_10, 3);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_10);
lean::dec(x_17);
lean::dec(x_19);
lean::inc(x_0);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_0);
x_26 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1;
lean::inc(x_3);
x_28 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_25, x_26, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_25);
if (lean::obj_tag(x_28) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
x_35 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_37 = x_28;
} else {
 lean::inc(x_35);
 lean::dec(x_28);
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
x_39 = lean::cnstr_get(x_28, 0);
lean::inc(x_39);
lean::dec(x_28);
x_15 = x_39;
goto lbl_16;
}
}
else
{
obj* x_42; 
x_42 = lean::cnstr_get(x_19, 0);
lean::inc(x_42);
lean::dec(x_19);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; 
x_45 = lean::cnstr_get(x_17, 1);
lean::inc(x_45);
lean::dec(x_17);
if (lean::obj_tag(x_45) == 0)
{
obj* x_50; obj* x_51; obj* x_53; 
lean::dec(x_10);
lean::inc(x_0);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_0);
x_51 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1;
lean::inc(x_3);
x_53 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_50, x_51, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_50);
if (lean::obj_tag(x_53) == 0)
{
obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
x_60 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_62 = x_53;
} else {
 lean::inc(x_60);
 lean::dec(x_53);
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
obj* x_64; 
x_64 = lean::cnstr_get(x_53, 0);
lean::inc(x_64);
lean::dec(x_53);
x_15 = x_64;
goto lbl_16;
}
}
else
{
obj* x_67; obj* x_70; obj* x_74; 
x_67 = lean::cnstr_get(x_45, 0);
lean::inc(x_67);
lean::dec(x_45);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
lean::inc(x_3);
x_74 = l_lean_elaborator_to__pexpr___main(x_70, x_2, x_3, x_4);
if (lean::obj_tag(x_74) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_12);
x_80 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_82 = x_74;
} else {
 lean::inc(x_80);
 lean::dec(x_74);
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
obj* x_84; obj* x_87; obj* x_89; obj* x_91; obj* x_92; obj* x_95; uint8 x_96; obj* x_98; obj* x_99; 
x_84 = lean::cnstr_get(x_74, 0);
lean::inc(x_84);
lean::dec(x_74);
x_87 = lean::cnstr_get(x_84, 0);
x_89 = lean::cnstr_get(x_84, 1);
if (lean::is_exclusive(x_84)) {
 x_91 = x_84;
} else {
 lean::inc(x_87);
 lean::inc(x_89);
 lean::dec(x_84);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_10, 1);
lean::inc(x_92);
lean::dec(x_10);
x_95 = l_lean_elaborator_mangle__ident(x_92);
x_96 = 0;
lean::inc(x_95);
x_98 = lean_expr_local(x_95, x_95, x_87, x_96);
if (lean::is_scalar(x_91)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_91;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_89);
x_15 = x_99;
goto lbl_16;
}
}
}
else
{
obj* x_104; obj* x_105; obj* x_107; 
lean::dec(x_10);
lean::dec(x_17);
lean::dec(x_42);
lean::inc(x_0);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_0);
x_105 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1;
lean::inc(x_3);
x_107 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_104, x_105, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_104);
if (lean::obj_tag(x_107) == 0)
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
x_114 = lean::cnstr_get(x_107, 0);
if (lean::is_exclusive(x_107)) {
 x_116 = x_107;
} else {
 lean::inc(x_114);
 lean::dec(x_107);
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
obj* x_118; 
x_118 = lean::cnstr_get(x_107, 0);
lean::inc(x_118);
lean::dec(x_107);
x_15 = x_118;
goto lbl_16;
}
}
}
lbl_16:
{
obj* x_121; obj* x_123; obj* x_126; 
x_121 = lean::cnstr_get(x_15, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_15, 1);
lean::inc(x_123);
lean::dec(x_15);
x_126 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2(x_0, x_12, x_2, x_3, x_123);
if (lean::obj_tag(x_126) == 0)
{
obj* x_129; obj* x_131; obj* x_132; 
lean::dec(x_14);
lean::dec(x_121);
x_129 = lean::cnstr_get(x_126, 0);
if (lean::is_exclusive(x_126)) {
 x_131 = x_126;
} else {
 lean::inc(x_129);
 lean::dec(x_126);
 x_131 = lean::box(0);
}
if (lean::is_scalar(x_131)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_131;
}
lean::cnstr_set(x_132, 0, x_129);
return x_132;
}
else
{
obj* x_133; obj* x_135; obj* x_136; obj* x_138; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_133 = lean::cnstr_get(x_126, 0);
if (lean::is_exclusive(x_126)) {
 x_135 = x_126;
} else {
 lean::inc(x_133);
 lean::dec(x_126);
 x_135 = lean::box(0);
}
x_136 = lean::cnstr_get(x_133, 0);
x_138 = lean::cnstr_get(x_133, 1);
if (lean::is_exclusive(x_133)) {
 x_140 = x_133;
} else {
 lean::inc(x_136);
 lean::inc(x_138);
 lean::dec(x_133);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_14;
}
lean::cnstr_set(x_141, 0, x_121);
lean::cnstr_set(x_141, 1, x_136);
if (lean::is_scalar(x_140)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_140;
}
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_138);
if (lean::is_scalar(x_135)) {
 x_143 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_143 = x_135;
}
lean::cnstr_set(x_143, 0, x_142);
return x_143;
}
}
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
x_12 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_4);
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
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__5(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__5(x_4);
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
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__6(obj* x_0, obj* x_1) {
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
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__7(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__7(x_4);
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
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
lean::inc(x_2);
x_17 = l_lean_elaborator_to__pexpr___main(x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
x_33 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__8(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_12);
lean::dec(x_28);
x_36 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_38 = x_33;
} else {
 lean::inc(x_36);
 lean::dec(x_33);
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
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_42 = x_33;
} else {
 lean::inc(x_40);
 lean::dec(x_33);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 0);
x_45 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 x_47 = x_40;
} else {
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_12;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_43);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
if (lean::is_scalar(x_42)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_42;
}
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__9(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__9(x_4);
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
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_5);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_2, 0);
x_14 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_16 = x_2;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_2);
 x_16 = lean::box(0);
}
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_28; obj* x_30; 
lean::dec(x_22);
lean::inc(x_0);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_0);
x_28 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1;
lean::inc(x_4);
x_30 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_27, x_28, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_38 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_40 = x_30;
} else {
 lean::inc(x_38);
 lean::dec(x_30);
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
obj* x_42; 
x_42 = lean::cnstr_get(x_30, 0);
lean::inc(x_42);
lean::dec(x_30);
x_17 = x_42;
goto lbl_18;
}
}
else
{
obj* x_45; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; 
x_45 = lean::cnstr_get(x_22, 0);
lean::inc(x_45);
lean::dec(x_22);
x_48 = 0;
x_49 = lean::box(x_48);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_45);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_5);
x_17 = x_51;
goto lbl_18;
}
}
case 1:
{
obj* x_52; obj* x_55; uint8 x_58; obj* x_59; obj* x_60; obj* x_61; 
x_52 = lean::cnstr_get(x_12, 0);
lean::inc(x_52);
lean::dec(x_12);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_58 = 1;
x_59 = lean::box(x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_55);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_5);
x_17 = x_61;
goto lbl_18;
}
case 2:
{
obj* x_62; obj* x_65; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; 
x_62 = lean::cnstr_get(x_12, 0);
lean::inc(x_62);
lean::dec(x_12);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_68 = 2;
x_69 = lean::box(x_68);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_65);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_5);
x_17 = x_71;
goto lbl_18;
}
default:
{
obj* x_72; obj* x_75; uint8 x_78; obj* x_79; obj* x_80; obj* x_81; 
x_72 = lean::cnstr_get(x_12, 0);
lean::inc(x_72);
lean::dec(x_12);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
x_78 = 3;
x_79 = lean::box(x_78);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_75);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_5);
x_17 = x_81;
goto lbl_18;
}
}
lbl_18:
{
obj* x_82; obj* x_84; obj* x_87; obj* x_89; obj* x_92; obj* x_94; obj* x_97; obj* x_100; 
x_82 = lean::cnstr_get(x_17, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_17, 1);
lean::inc(x_84);
lean::dec(x_17);
x_87 = lean::cnstr_get(x_82, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_82, 1);
lean::inc(x_89);
lean::dec(x_82);
x_92 = lean::cnstr_get(x_89, 2);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_92, 1);
lean::inc(x_94);
lean::dec(x_92);
x_97 = l_lean_expander_get__opt__type___main(x_94);
lean::dec(x_94);
lean::inc(x_4);
x_100 = l_lean_elaborator_to__pexpr___main(x_97, x_3, x_4, x_84);
if (lean::obj_tag(x_100) == 0)
{
obj* x_108; obj* x_110; obj* x_111; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_87);
lean::dec(x_89);
x_108 = lean::cnstr_get(x_100, 0);
if (lean::is_exclusive(x_100)) {
 x_110 = x_100;
} else {
 lean::inc(x_108);
 lean::dec(x_100);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
return x_111;
}
else
{
obj* x_112; obj* x_115; obj* x_117; obj* x_121; 
x_112 = lean::cnstr_get(x_100, 0);
lean::inc(x_112);
lean::dec(x_100);
x_115 = lean::cnstr_get(x_112, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_112, 1);
lean::inc(x_117);
lean::dec(x_112);
lean::inc(x_1);
x_121 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__10(x_0, x_1, x_14, x_3, x_4, x_117);
if (lean::obj_tag(x_121) == 0)
{
obj* x_127; obj* x_129; obj* x_130; 
lean::dec(x_16);
lean::dec(x_1);
lean::dec(x_87);
lean::dec(x_89);
lean::dec(x_115);
x_127 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 x_129 = x_121;
} else {
 lean::inc(x_127);
 lean::dec(x_121);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_127);
return x_130;
}
else
{
obj* x_131; obj* x_133; obj* x_134; obj* x_136; obj* x_138; obj* x_139; uint8 x_140; obj* x_143; obj* x_144; obj* x_146; obj* x_147; obj* x_148; obj* x_151; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_131 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 x_133 = x_121;
} else {
 lean::inc(x_131);
 lean::dec(x_121);
 x_133 = lean::box(0);
}
x_134 = lean::cnstr_get(x_131, 0);
x_136 = lean::cnstr_get(x_131, 1);
if (lean::is_exclusive(x_131)) {
 x_138 = x_131;
} else {
 lean::inc(x_134);
 lean::inc(x_136);
 lean::dec(x_131);
 x_138 = lean::box(0);
}
x_139 = l_lean_elaborator_dummy;
x_140 = lean::unbox(x_87);
lean::inc(x_1);
lean::inc(x_1);
x_143 = lean_expr_local(x_1, x_1, x_139, x_140);
x_144 = lean::cnstr_get(x_89, 0);
lean::inc(x_144);
x_146 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__9(x_144);
x_147 = l_lean_elaborator_names__to__pexpr(x_146);
x_148 = lean::cnstr_get(x_89, 1);
lean::inc(x_148);
lean::dec(x_89);
x_151 = l_lean_elaborator_infer__mod__to__pexpr(x_148);
lean::dec(x_148);
x_153 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_154 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_154 = x_16;
}
lean::cnstr_set(x_154, 0, x_115);
lean::cnstr_set(x_154, 1, x_153);
x_155 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_155, 0, x_151);
lean::cnstr_set(x_155, 1, x_154);
x_156 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_156, 0, x_147);
lean::cnstr_set(x_156, 1, x_155);
x_157 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_157, 0, x_143);
lean::cnstr_set(x_157, 1, x_156);
x_158 = l_lean_expr_mk__capp(x_1, x_157);
x_159 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_159, 0, x_158);
lean::cnstr_set(x_159, 1, x_134);
if (lean::is_scalar(x_138)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_138;
}
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_136);
if (lean::is_scalar(x_133)) {
 x_161 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_161 = x_133;
}
lean::cnstr_set(x_161, 0, x_160);
return x_161;
}
}
}
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
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__12(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__12(x_4);
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
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__13(obj* x_0, obj* x_1) {
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
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__14(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__14(x_4);
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
obj* l_lean_elaborator_declaration_elaborate___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_13; 
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_7);
x_13 = l_lean_elaborator_to__pexpr___main(x_9, x_6, x_7, x_8);
if (lean::obj_tag(x_13) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_21 = x_13;
} else {
 lean::inc(x_19);
 lean::dec(x_13);
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
obj* x_23; obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_23 = lean::cnstr_get(x_13, 0);
lean::inc(x_23);
lean::dec(x_13);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
lean::dec(x_23);
x_31 = l_lean_elaborator_ident__univ__params__to__pexpr(x_1);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_26);
lean::cnstr_set(x_32, 1, x_2);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_5);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_lean_elaborator_mk__eqns___closed__1;
x_36 = l_lean_expr_mk__capp(x_35, x_34);
x_37 = lean_expr_mk_mdata(x_3, x_36);
x_38 = l_lean_elaborator_old__elab__command(x_4, x_37, x_6, x_7, x_28);
return x_38;
}
}
}
obj* l_lean_elaborator_declaration_elaborate___lambda__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__5(x_10);
x_14 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__6(x_8, x_13);
x_15 = lean::cnstr_get(x_1, 4);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 5);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 6);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 7);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_1, 8);
lean::inc(x_23);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_26, 0, x_2);
lean::cnstr_set(x_26, 1, x_4);
lean::cnstr_set(x_26, 2, x_6);
lean::cnstr_set(x_26, 3, x_14);
lean::cnstr_set(x_26, 4, x_15);
lean::cnstr_set(x_26, 5, x_17);
lean::cnstr_set(x_26, 6, x_19);
lean::cnstr_set(x_26, 7, x_21);
lean::cnstr_set(x_26, 8, x_23);
return x_26;
}
}
obj* l_lean_elaborator_declaration_elaborate___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12) {
_start:
{
obj* x_13; obj* x_15; 
x_15 = lean::cnstr_get(x_8, 1);
if (lean::obj_tag(x_15) == 0)
{
lean::inc(x_0);
x_13 = x_0;
goto lbl_14;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_15, 0);
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
x_13 = x_18;
goto lbl_14;
}
lbl_14:
{
obj* x_21; 
lean::inc(x_11);
x_21 = l_lean_elaborator_attrs__to__pexpr(x_13, x_10, x_11, x_12);
if (lean::obj_tag(x_21) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_33 = x_21;
} else {
 lean::inc(x_31);
 lean::dec(x_21);
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
obj* x_35; obj* x_38; obj* x_40; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_35 = lean::cnstr_get(x_21, 0);
lean::inc(x_35);
lean::dec(x_21);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
lean::inc(x_0);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_38);
lean::cnstr_set(x_44, 1, x_0);
x_45 = l_lean_elaborator_mk__eqns___closed__1;
x_46 = l_lean_expr_mk__capp(x_45, x_44);
if (lean::obj_tag(x_6) == 0)
{
obj* x_50; obj* x_52; 
x_50 = l_lean_expander_get__opt__type___main(x_7);
lean::inc(x_11);
x_52 = l_lean_elaborator_to__pexpr___main(x_50, x_10, x_11, x_40);
if (lean::obj_tag(x_6) == 0)
{
if (lean::obj_tag(x_52) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_62 = lean::cnstr_get(x_52, 0);
if (lean::is_exclusive(x_52)) {
 x_64 = x_52;
} else {
 lean::inc(x_62);
 lean::dec(x_52);
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
obj* x_66; 
x_66 = lean::cnstr_get(x_52, 0);
lean::inc(x_66);
lean::dec(x_52);
lean::inc(x_0);
x_47 = x_0;
x_48 = x_66;
goto lbl_49;
}
}
else
{
if (lean::obj_tag(x_52) == 0)
{
obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_79 = lean::cnstr_get(x_52, 0);
if (lean::is_exclusive(x_52)) {
 x_81 = x_52;
} else {
 lean::inc(x_79);
 lean::dec(x_52);
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
x_83 = lean::cnstr_get(x_6, 0);
lean::inc(x_83);
lean::dec(x_6);
x_86 = lean::cnstr_get(x_52, 0);
lean::inc(x_86);
lean::dec(x_52);
x_89 = lean::cnstr_get(x_83, 1);
lean::inc(x_89);
lean::dec(x_83);
x_92 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(x_89);
x_47 = x_92;
x_48 = x_86;
goto lbl_49;
}
}
}
else
{
obj* x_93; obj* x_96; obj* x_98; 
x_93 = lean::cnstr_get(x_6, 0);
lean::inc(x_93);
lean::inc(x_93);
x_96 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_declaration_elaborate___lambda__2), 2, 1);
lean::closure_set(x_96, 0, x_93);
lean::inc(x_11);
x_98 = l_lean_elaborator_modify__current__scope(x_96, x_10, x_11, x_40);
if (lean::obj_tag(x_98) == 0)
{
obj* x_110; obj* x_112; obj* x_113; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_93);
lean::dec(x_46);
x_110 = lean::cnstr_get(x_98, 0);
if (lean::is_exclusive(x_98)) {
 x_112 = x_98;
} else {
 lean::inc(x_110);
 lean::dec(x_98);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_110);
return x_113;
}
else
{
obj* x_114; obj* x_117; obj* x_120; obj* x_122; 
x_114 = lean::cnstr_get(x_98, 0);
lean::inc(x_114);
lean::dec(x_98);
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
x_120 = l_lean_expander_get__opt__type___main(x_7);
lean::inc(x_11);
x_122 = l_lean_elaborator_to__pexpr___main(x_120, x_10, x_11, x_117);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_93);
if (lean::obj_tag(x_122) == 0)
{
obj* x_133; obj* x_135; obj* x_136; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_133 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
 x_135 = x_122;
} else {
 lean::inc(x_133);
 lean::dec(x_122);
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
obj* x_137; 
x_137 = lean::cnstr_get(x_122, 0);
lean::inc(x_137);
lean::dec(x_122);
lean::inc(x_0);
x_47 = x_0;
x_48 = x_137;
goto lbl_49;
}
}
else
{
lean::dec(x_6);
if (lean::obj_tag(x_122) == 0)
{
obj* x_152; obj* x_154; obj* x_155; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_93);
lean::dec(x_46);
x_152 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
 x_154 = x_122;
} else {
 lean::inc(x_152);
 lean::dec(x_122);
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
obj* x_156; obj* x_159; obj* x_162; 
x_156 = lean::cnstr_get(x_122, 0);
lean::inc(x_156);
lean::dec(x_122);
x_159 = lean::cnstr_get(x_93, 1);
lean::inc(x_159);
lean::dec(x_93);
x_162 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__7(x_159);
x_47 = x_162;
x_48 = x_156;
goto lbl_49;
}
}
}
}
lbl_49:
{
obj* x_163; obj* x_165; obj* x_169; 
x_163 = lean::cnstr_get(x_48, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_48, 1);
lean::inc(x_165);
lean::dec(x_48);
lean::inc(x_11);
x_169 = l_lean_elaborator_simple__binders__to__pexpr(x_1, x_10, x_11, x_165);
if (lean::obj_tag(x_169) == 0)
{
obj* x_180; obj* x_182; obj* x_183; 
lean::dec(x_163);
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
lean::dec(x_47);
x_180 = lean::cnstr_get(x_169, 0);
if (lean::is_exclusive(x_169)) {
 x_182 = x_169;
} else {
 lean::inc(x_180);
 lean::dec(x_169);
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
obj* x_184; obj* x_187; obj* x_189; obj* x_195; 
x_184 = lean::cnstr_get(x_169, 0);
lean::inc(x_184);
lean::dec(x_169);
x_187 = lean::cnstr_get(x_184, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_184, 1);
lean::inc(x_189);
lean::dec(x_184);
lean::inc(x_11);
lean::inc(x_3);
lean::inc(x_2);
x_195 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2(x_2, x_3, x_10, x_11, x_189);
if (lean::obj_tag(x_195) == 0)
{
obj* x_207; obj* x_209; obj* x_210; 
lean::dec(x_187);
lean::dec(x_163);
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
lean::dec(x_47);
x_207 = lean::cnstr_get(x_195, 0);
if (lean::is_exclusive(x_195)) {
 x_209 = x_195;
} else {
 lean::inc(x_207);
 lean::dec(x_195);
 x_209 = lean::box(0);
}
if (lean::is_scalar(x_209)) {
 x_210 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_210 = x_209;
}
lean::cnstr_set(x_210, 0, x_207);
return x_210;
}
else
{
obj* x_211; obj* x_214; obj* x_216; obj* x_219; obj* x_220; obj* x_223; uint8 x_224; obj* x_226; obj* x_228; obj* x_229; obj* x_230; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; 
x_211 = lean::cnstr_get(x_195, 0);
lean::inc(x_211);
lean::dec(x_195);
x_214 = lean::cnstr_get(x_211, 0);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_211, 1);
lean::inc(x_216);
lean::dec(x_211);
x_219 = l_lean_elaborator_names__to__pexpr(x_47);
x_220 = lean::cnstr_get(x_4, 0);
lean::inc(x_220);
lean::dec(x_4);
x_223 = l_lean_elaborator_mangle__ident(x_220);
x_224 = 0;
lean::inc(x_223);
x_226 = lean_expr_local(x_223, x_223, x_163, x_224);
lean::inc(x_0);
x_228 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_228, 0, x_226);
lean::cnstr_set(x_228, 1, x_0);
x_229 = l_lean_expr_mk__capp(x_45, x_228);
x_230 = l_lean_expr_mk__capp(x_45, x_214);
lean::inc(x_0);
x_232 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_232, 0, x_230);
lean::cnstr_set(x_232, 1, x_0);
x_233 = l_lean_expr_mk__capp(x_45, x_232);
x_234 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_3);
x_235 = l_lean_expr_mk__capp(x_45, x_234);
lean::inc(x_0);
x_237 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_237, 0, x_235);
lean::cnstr_set(x_237, 1, x_0);
x_238 = l_lean_expr_mk__capp(x_45, x_237);
x_239 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_239, 1, x_0);
x_240 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_240, 0, x_233);
lean::cnstr_set(x_240, 1, x_239);
x_241 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_241, 0, x_187);
lean::cnstr_set(x_241, 1, x_240);
x_242 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_242, 0, x_229);
lean::cnstr_set(x_242, 1, x_241);
x_243 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_243, 0, x_219);
lean::cnstr_set(x_243, 1, x_242);
x_244 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_244, 0, x_46);
lean::cnstr_set(x_244, 1, x_243);
x_245 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_245, 0, x_9);
lean::cnstr_set(x_245, 1, x_244);
x_246 = l_lean_expr_mk__capp(x_45, x_245);
x_247 = lean_expr_mk_mdata(x_5, x_246);
x_248 = l_lean_elaborator_old__elab__command(x_2, x_247, x_10, x_11, x_216);
lean::dec(x_2);
return x_248;
}
}
}
}
}
}
}
obj* l_lean_elaborator_declaration_elaborate___lambda__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__12(x_10);
x_14 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__13(x_8, x_13);
x_15 = lean::cnstr_get(x_1, 4);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 5);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 6);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 7);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_1, 8);
lean::inc(x_23);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_26, 0, x_2);
lean::cnstr_set(x_26, 1, x_4);
lean::cnstr_set(x_26, 2, x_6);
lean::cnstr_set(x_26, 3, x_14);
lean::cnstr_set(x_26, 4, x_15);
lean::cnstr_set(x_26, 5, x_17);
lean::cnstr_set(x_26, 6, x_19);
lean::cnstr_set(x_26, 7, x_21);
lean::cnstr_set(x_26, 8, x_23);
return x_26;
}
}
obj* _init_l_lean_elaborator_declaration_elaborate___lambda__5___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_lean_elaborator_infer__mod__to__pexpr(x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_declaration_elaborate___lambda__5___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("mk");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_declaration_elaborate___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
_start:
{
obj* x_14; obj* x_15; 
if (lean::obj_tag(x_8) == 0)
{
obj* x_17; obj* x_19; 
x_17 = l_lean_expander_get__opt__type___main(x_9);
lean::inc(x_12);
x_19 = l_lean_elaborator_to__pexpr___main(x_17, x_11, x_12, x_13);
if (lean::obj_tag(x_8) == 0)
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_31 = x_19;
} else {
 lean::inc(x_29);
 lean::dec(x_19);
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
x_33 = lean::cnstr_get(x_19, 0);
lean::inc(x_33);
lean::dec(x_19);
lean::inc(x_5);
x_14 = x_5;
x_15 = x_33;
goto lbl_16;
}
}
else
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
x_46 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_48 = x_19;
} else {
 lean::inc(x_46);
 lean::dec(x_19);
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
obj* x_50; obj* x_53; obj* x_56; obj* x_59; 
x_50 = lean::cnstr_get(x_8, 0);
lean::inc(x_50);
lean::dec(x_8);
x_53 = lean::cnstr_get(x_19, 0);
lean::inc(x_53);
lean::dec(x_19);
x_56 = lean::cnstr_get(x_50, 1);
lean::inc(x_56);
lean::dec(x_50);
x_59 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(x_56);
x_14 = x_59;
x_15 = x_53;
goto lbl_16;
}
}
}
else
{
obj* x_60; obj* x_63; obj* x_65; 
x_60 = lean::cnstr_get(x_8, 0);
lean::inc(x_60);
lean::inc(x_60);
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_declaration_elaborate___lambda__4), 2, 1);
lean::closure_set(x_63, 0, x_60);
lean::inc(x_12);
x_65 = l_lean_elaborator_modify__current__scope(x_63, x_11, x_12, x_13);
if (lean::obj_tag(x_65) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_5);
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_60);
x_77 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_79 = x_65;
} else {
 lean::inc(x_77);
 lean::dec(x_65);
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
obj* x_81; obj* x_84; obj* x_87; obj* x_89; 
x_81 = lean::cnstr_get(x_65, 0);
lean::inc(x_81);
lean::dec(x_65);
x_84 = lean::cnstr_get(x_81, 1);
lean::inc(x_84);
lean::dec(x_81);
x_87 = l_lean_expander_get__opt__type___main(x_9);
lean::inc(x_12);
x_89 = l_lean_elaborator_to__pexpr___main(x_87, x_11, x_12, x_84);
if (lean::obj_tag(x_8) == 0)
{
lean::dec(x_60);
if (lean::obj_tag(x_89) == 0)
{
obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
x_100 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_102 = x_89;
} else {
 lean::inc(x_100);
 lean::dec(x_89);
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
obj* x_104; 
x_104 = lean::cnstr_get(x_89, 0);
lean::inc(x_104);
lean::dec(x_89);
lean::inc(x_5);
x_14 = x_5;
x_15 = x_104;
goto lbl_16;
}
}
else
{
lean::dec(x_8);
if (lean::obj_tag(x_89) == 0)
{
obj* x_119; obj* x_121; obj* x_122; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_60);
x_119 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_121 = x_89;
} else {
 lean::inc(x_119);
 lean::dec(x_89);
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
obj* x_123; obj* x_126; obj* x_129; 
x_123 = lean::cnstr_get(x_89, 0);
lean::inc(x_123);
lean::dec(x_89);
x_126 = lean::cnstr_get(x_60, 1);
lean::inc(x_126);
lean::dec(x_60);
x_129 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__14(x_126);
x_14 = x_129;
x_15 = x_123;
goto lbl_16;
}
}
}
}
lbl_16:
{
obj* x_130; obj* x_132; obj* x_136; 
x_130 = lean::cnstr_get(x_15, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_15, 1);
lean::inc(x_132);
lean::dec(x_15);
lean::inc(x_12);
x_136 = l_lean_elaborator_simple__binders__to__pexpr(x_0, x_11, x_12, x_132);
if (lean::obj_tag(x_136) == 0)
{
obj* x_147; obj* x_149; obj* x_150; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_130);
lean::dec(x_14);
x_147 = lean::cnstr_get(x_136, 0);
if (lean::is_exclusive(x_136)) {
 x_149 = x_136;
} else {
 lean::inc(x_147);
 lean::dec(x_136);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_147);
return x_150;
}
else
{
obj* x_151; obj* x_154; obj* x_156; obj* x_159; obj* x_160; obj* x_163; obj* x_164; uint8 x_165; obj* x_167; obj* x_168; 
x_151 = lean::cnstr_get(x_136, 0);
lean::inc(x_151);
lean::dec(x_136);
x_154 = lean::cnstr_get(x_151, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_151, 1);
lean::inc(x_156);
lean::dec(x_151);
x_159 = l_lean_elaborator_names__to__pexpr(x_14);
x_160 = lean::cnstr_get(x_1, 0);
lean::inc(x_160);
lean::dec(x_1);
x_163 = l_lean_elaborator_mangle__ident(x_160);
x_164 = l_lean_elaborator_dummy;
x_165 = 0;
lean::inc(x_163);
x_167 = lean_expr_local(x_163, x_163, x_164, x_165);
if (lean::obj_tag(x_7) == 0)
{
lean::inc(x_5);
x_168 = x_5;
goto lbl_169;
}
else
{
obj* x_171; obj* x_172; 
x_171 = lean::cnstr_get(x_7, 0);
x_172 = lean::cnstr_get(x_171, 1);
lean::inc(x_172);
x_168 = x_172;
goto lbl_169;
}
lbl_169:
{
obj* x_175; 
lean::inc(x_12);
x_175 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__8(x_168, x_11, x_12, x_156);
if (lean::obj_tag(x_175) == 0)
{
obj* x_187; obj* x_189; obj* x_190; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_130);
lean::dec(x_167);
lean::dec(x_154);
lean::dec(x_159);
x_187 = lean::cnstr_get(x_175, 0);
if (lean::is_exclusive(x_175)) {
 x_189 = x_175;
} else {
 lean::inc(x_187);
 lean::dec(x_175);
 x_189 = lean::box(0);
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
obj* x_191; obj* x_194; obj* x_196; obj* x_199; obj* x_200; obj* x_203; obj* x_204; 
x_191 = lean::cnstr_get(x_175, 0);
lean::inc(x_191);
lean::dec(x_175);
x_194 = lean::cnstr_get(x_191, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_191, 1);
lean::inc(x_196);
lean::dec(x_191);
x_199 = l_lean_elaborator_mk__eqns___closed__1;
x_200 = l_lean_expr_mk__capp(x_199, x_194);
lean::inc(x_12);
lean::inc(x_2);
x_203 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__10(x_2, x_199, x_3, x_11, x_12, x_196);
if (lean::obj_tag(x_4) == 0)
{
obj* x_206; 
x_206 = l_lean_elaborator_declaration_elaborate___lambda__5___closed__2;
x_204 = x_206;
goto lbl_205;
}
else
{
obj* x_207; obj* x_209; obj* x_212; 
x_207 = lean::cnstr_get(x_4, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_207, 0);
lean::inc(x_209);
lean::dec(x_207);
x_212 = l_lean_elaborator_mangle__ident(x_209);
x_204 = x_212;
goto lbl_205;
}
lbl_205:
{
obj* x_214; 
lean::inc(x_204);
x_214 = lean_expr_local(x_204, x_204, x_164, x_165);
if (lean::obj_tag(x_4) == 0)
{
if (lean::obj_tag(x_203) == 0)
{
obj* x_226; obj* x_228; obj* x_229; 
lean::dec(x_200);
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_130);
lean::dec(x_214);
lean::dec(x_167);
lean::dec(x_154);
lean::dec(x_159);
x_226 = lean::cnstr_get(x_203, 0);
if (lean::is_exclusive(x_203)) {
 x_228 = x_203;
} else {
 lean::inc(x_226);
 lean::dec(x_203);
 x_228 = lean::box(0);
}
if (lean::is_scalar(x_228)) {
 x_229 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_229 = x_228;
}
lean::cnstr_set(x_229, 0, x_226);
return x_229;
}
else
{
obj* x_230; obj* x_233; obj* x_235; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
x_230 = lean::cnstr_get(x_203, 0);
lean::inc(x_230);
lean::dec(x_203);
x_233 = lean::cnstr_get(x_230, 0);
lean::inc(x_233);
x_235 = lean::cnstr_get(x_230, 1);
lean::inc(x_235);
lean::dec(x_230);
x_238 = l_lean_expr_mk__capp(x_199, x_233);
x_239 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_239, 1, x_5);
x_240 = l_lean_elaborator_declaration_elaborate___lambda__5___closed__1;
x_241 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_241, 0, x_240);
lean::cnstr_set(x_241, 1, x_239);
x_242 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_242, 0, x_214);
lean::cnstr_set(x_242, 1, x_241);
x_243 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_243, 0, x_130);
lean::cnstr_set(x_243, 1, x_242);
x_244 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_244, 0, x_200);
lean::cnstr_set(x_244, 1, x_243);
x_245 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_245, 0, x_154);
lean::cnstr_set(x_245, 1, x_244);
x_246 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_246, 0, x_167);
lean::cnstr_set(x_246, 1, x_245);
x_247 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_247, 0, x_159);
lean::cnstr_set(x_247, 1, x_246);
x_248 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_248, 0, x_10);
lean::cnstr_set(x_248, 1, x_247);
x_249 = l_lean_expr_mk__capp(x_199, x_248);
x_250 = lean_expr_mk_mdata(x_6, x_249);
x_251 = l_lean_elaborator_old__elab__command(x_2, x_250, x_11, x_12, x_235);
lean::dec(x_2);
return x_251;
}
}
else
{
if (lean::obj_tag(x_203) == 0)
{
obj* x_265; obj* x_267; obj* x_268; 
lean::dec(x_200);
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_130);
lean::dec(x_214);
lean::dec(x_167);
lean::dec(x_154);
lean::dec(x_159);
x_265 = lean::cnstr_get(x_203, 0);
if (lean::is_exclusive(x_203)) {
 x_267 = x_203;
} else {
 lean::inc(x_265);
 lean::dec(x_203);
 x_267 = lean::box(0);
}
if (lean::is_scalar(x_267)) {
 x_268 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_268 = x_267;
}
lean::cnstr_set(x_268, 0, x_265);
return x_268;
}
else
{
obj* x_269; obj* x_272; obj* x_275; obj* x_277; obj* x_280; obj* x_283; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; 
x_269 = lean::cnstr_get(x_203, 0);
lean::inc(x_269);
lean::dec(x_203);
x_272 = lean::cnstr_get(x_4, 0);
lean::inc(x_272);
lean::dec(x_4);
x_275 = lean::cnstr_get(x_269, 0);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_269, 1);
lean::inc(x_277);
lean::dec(x_269);
x_280 = lean::cnstr_get(x_272, 1);
lean::inc(x_280);
lean::dec(x_272);
x_283 = l_lean_elaborator_infer__mod__to__pexpr(x_280);
lean::dec(x_280);
x_285 = l_lean_expr_mk__capp(x_199, x_275);
x_286 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_286, 0, x_285);
lean::cnstr_set(x_286, 1, x_5);
x_287 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_287, 0, x_283);
lean::cnstr_set(x_287, 1, x_286);
x_288 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_288, 0, x_214);
lean::cnstr_set(x_288, 1, x_287);
x_289 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_289, 0, x_130);
lean::cnstr_set(x_289, 1, x_288);
x_290 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_290, 0, x_200);
lean::cnstr_set(x_290, 1, x_289);
x_291 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_291, 0, x_154);
lean::cnstr_set(x_291, 1, x_290);
x_292 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_292, 0, x_167);
lean::cnstr_set(x_292, 1, x_291);
x_293 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_293, 0, x_159);
lean::cnstr_set(x_293, 1, x_292);
x_294 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_294, 0, x_10);
lean::cnstr_set(x_294, 1, x_293);
x_295 = l_lean_expr_mk__capp(x_199, x_294);
x_296 = lean_expr_mk_mdata(x_6, x_295);
x_297 = l_lean_elaborator_old__elab__command(x_2, x_296, x_11, x_12, x_277);
lean::dec(x_2);
return x_297;
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_elaborator_declaration_elaborate___closed__1() {
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
obj* _init_l_lean_elaborator_declaration_elaborate___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("def");
x_2 = l_string_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_lean_elaborator_declaration_elaborate___closed__3() {
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
obj* _init_l_lean_elaborator_declaration_elaborate___closed__4() {
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
obj* _init_l_lean_elaborator_declaration_elaborate___closed__5() {
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
obj* l_lean_elaborator_declaration_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; 
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
obj* x_20; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_17);
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
lean::dec(x_11);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___boxed), 7, 4);
lean::closure_set(x_24, 0, x_0);
lean::closure_set(x_24, 1, x_20);
lean::closure_set(x_24, 2, x_14);
lean::closure_set(x_24, 3, x_23);
x_25 = l_lean_elaborator_locally(x_24, x_1, x_2, x_3);
return x_25;
}
case 1:
{
obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_17);
x_27 = lean::cnstr_get(x_11, 0);
lean::inc(x_27);
lean::dec(x_11);
x_30 = lean::mk_nat_obj(5u);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___boxed), 7, 4);
lean::closure_set(x_31, 0, x_0);
lean::closure_set(x_31, 1, x_27);
lean::closure_set(x_31, 2, x_14);
lean::closure_set(x_31, 3, x_30);
x_32 = l_lean_elaborator_locally(x_31, x_1, x_2, x_3);
return x_32;
}
default:
{
obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_17);
x_34 = lean::cnstr_get(x_11, 0);
lean::inc(x_34);
lean::dec(x_11);
x_37 = lean::mk_nat_obj(0u);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___boxed), 7, 4);
lean::closure_set(x_38, 0, x_0);
lean::closure_set(x_38, 1, x_34);
lean::closure_set(x_38, 2, x_14);
lean::closure_set(x_38, 3, x_37);
x_39 = l_lean_elaborator_locally(x_38, x_1, x_2, x_3);
return x_39;
}
}
}
case 1:
{
obj* x_40; obj* x_43; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_40 = lean::cnstr_get(x_12, 0);
lean::inc(x_40);
lean::dec(x_12);
x_43 = lean::cnstr_get(x_11, 0);
lean::inc(x_43);
lean::dec(x_11);
x_46 = lean::box(0);
x_47 = lean::cnstr_get(x_40, 1);
lean::inc(x_47);
x_49 = l_lean_elaborator_declaration_elaborate___closed__1;
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
x_64 = l_lean_elaborator_declaration_elaborate___closed__2;
x_65 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_46);
lean::cnstr_set(x_65, 2, x_50);
lean::cnstr_set(x_65, 3, x_60);
lean::cnstr_set(x_65, 4, x_61);
x_66 = lean::mk_nat_obj(3u);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___boxed), 7, 4);
lean::closure_set(x_67, 0, x_0);
lean::closure_set(x_67, 1, x_43);
lean::closure_set(x_67, 2, x_65);
lean::closure_set(x_67, 3, x_66);
x_68 = l_lean_elaborator_locally(x_67, x_1, x_2, x_3);
return x_68;
}
case 2:
{
obj* x_69; obj* x_72; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_83; obj* x_84; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
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
x_88 = l_lean_elaborator_declaration_elaborate___closed__2;
x_89 = l_lean_elaborator_declaration_elaborate___closed__1;
x_90 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_75);
lean::cnstr_set(x_90, 2, x_89);
lean::cnstr_set(x_90, 3, x_84);
lean::cnstr_set(x_90, 4, x_85);
x_91 = lean::mk_nat_obj(2u);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___boxed), 7, 4);
lean::closure_set(x_92, 0, x_0);
lean::closure_set(x_92, 1, x_72);
lean::closure_set(x_92, 2, x_90);
lean::closure_set(x_92, 3, x_91);
x_93 = l_lean_elaborator_locally(x_92, x_1, x_2, x_3);
return x_93;
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
obj* x_105; 
lean::dec(x_11);
lean::dec(x_97);
lean::dec(x_99);
lean::dec(x_94);
x_105 = lean::box(0);
x_4 = x_105;
goto lbl_5;
}
else
{
obj* x_106; 
x_106 = lean::cnstr_get(x_99, 0);
lean::inc(x_106);
lean::dec(x_99);
if (lean::obj_tag(x_106) == 0)
{
obj* x_109; obj* x_112; obj* x_115; obj* x_116; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_109 = lean::cnstr_get(x_94, 1);
lean::inc(x_109);
lean::dec(x_94);
x_112 = lean::cnstr_get(x_97, 1);
lean::inc(x_112);
lean::dec(x_97);
x_115 = lean::box(0);
x_116 = lean::cnstr_get(x_11, 0);
lean::inc(x_116);
lean::dec(x_11);
x_119 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_decl__modifiers__to__pexpr___boxed), 4, 1);
lean::closure_set(x_119, 0, x_116);
x_120 = l_lean_elaborator_declaration_elaborate___closed__3;
x_121 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_declaration_elaborate___lambda__1___boxed), 9, 5);
lean::closure_set(x_121, 0, x_112);
lean::closure_set(x_121, 1, x_109);
lean::closure_set(x_121, 2, x_115);
lean::closure_set(x_121, 3, x_120);
lean::closure_set(x_121, 4, x_0);
x_122 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_122, 0, x_119);
lean::closure_set(x_122, 1, x_121);
x_123 = l_lean_elaborator_locally(x_122, x_1, x_2, x_3);
return x_123;
}
else
{
obj* x_128; 
lean::dec(x_11);
lean::dec(x_97);
lean::dec(x_94);
lean::dec(x_106);
x_128 = lean::box(0);
x_4 = x_128;
goto lbl_5;
}
}
}
case 4:
{
obj* x_129; obj* x_132; 
x_129 = lean::cnstr_get(x_12, 0);
lean::inc(x_129);
lean::dec(x_12);
x_132 = lean::cnstr_get(x_129, 0);
lean::inc(x_132);
if (lean::obj_tag(x_132) == 0)
{
obj* x_134; obj* x_136; 
x_134 = lean::cnstr_get(x_129, 4);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_134, 0);
lean::inc(x_136);
if (lean::obj_tag(x_136) == 0)
{
obj* x_142; 
lean::dec(x_11);
lean::dec(x_129);
lean::dec(x_134);
lean::dec(x_136);
x_142 = lean::box(0);
x_4 = x_142;
goto lbl_5;
}
else
{
obj* x_143; obj* x_145; obj* x_147; obj* x_150; obj* x_153; obj* x_156; obj* x_157; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
x_143 = lean::cnstr_get(x_129, 2);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_129, 3);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_129, 6);
lean::inc(x_147);
lean::dec(x_129);
x_150 = lean::cnstr_get(x_134, 1);
lean::inc(x_150);
lean::dec(x_134);
x_153 = lean::cnstr_get(x_136, 0);
lean::inc(x_153);
lean::dec(x_136);
x_156 = lean::box(0);
x_157 = lean::cnstr_get(x_11, 0);
lean::inc(x_157);
lean::dec(x_11);
lean::inc(x_157);
x_161 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_decl__modifiers__to__pexpr___boxed), 4, 1);
lean::closure_set(x_161, 0, x_157);
x_162 = l_lean_elaborator_declaration_elaborate___closed__4;
x_163 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_declaration_elaborate___lambda__3___boxed), 13, 9);
lean::closure_set(x_163, 0, x_156);
lean::closure_set(x_163, 1, x_153);
lean::closure_set(x_163, 2, x_0);
lean::closure_set(x_163, 3, x_147);
lean::closure_set(x_163, 4, x_145);
lean::closure_set(x_163, 5, x_162);
lean::closure_set(x_163, 6, x_143);
lean::closure_set(x_163, 7, x_150);
lean::closure_set(x_163, 8, x_157);
x_164 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_164, 0, x_161);
lean::closure_set(x_164, 1, x_163);
x_165 = l_lean_elaborator_locally(x_164, x_1, x_2, x_3);
return x_165;
}
}
else
{
obj* x_169; 
lean::dec(x_11);
lean::dec(x_129);
lean::dec(x_132);
x_169 = lean::box(0);
x_4 = x_169;
goto lbl_5;
}
}
default:
{
obj* x_170; obj* x_173; 
x_170 = lean::cnstr_get(x_12, 0);
lean::inc(x_170);
lean::dec(x_12);
x_173 = lean::cnstr_get(x_170, 0);
lean::inc(x_173);
if (lean::obj_tag(x_173) == 0)
{
obj* x_176; obj* x_178; 
lean::dec(x_173);
x_176 = lean::cnstr_get(x_170, 3);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_176, 0);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
obj* x_184; 
lean::dec(x_178);
lean::dec(x_176);
lean::dec(x_170);
lean::dec(x_11);
x_184 = lean::box(0);
x_4 = x_184;
goto lbl_5;
}
else
{
obj* x_185; obj* x_187; obj* x_189; obj* x_191; obj* x_193; obj* x_196; obj* x_199; obj* x_202; obj* x_203; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
x_185 = lean::cnstr_get(x_170, 1);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_170, 2);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_170, 4);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_170, 6);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_170, 7);
lean::inc(x_193);
lean::dec(x_170);
x_196 = lean::cnstr_get(x_176, 1);
lean::inc(x_196);
lean::dec(x_176);
x_199 = lean::cnstr_get(x_178, 0);
lean::inc(x_199);
lean::dec(x_178);
x_202 = lean::box(0);
x_203 = lean::cnstr_get(x_11, 0);
lean::inc(x_203);
lean::dec(x_11);
x_206 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_decl__modifiers__to__pexpr___boxed), 4, 1);
lean::closure_set(x_206, 0, x_203);
x_207 = l_lean_elaborator_declaration_elaborate___closed__5;
x_208 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_declaration_elaborate___lambda__5___boxed), 14, 10);
lean::closure_set(x_208, 0, x_199);
lean::closure_set(x_208, 1, x_187);
lean::closure_set(x_208, 2, x_0);
lean::closure_set(x_208, 3, x_193);
lean::closure_set(x_208, 4, x_191);
lean::closure_set(x_208, 5, x_202);
lean::closure_set(x_208, 6, x_207);
lean::closure_set(x_208, 7, x_189);
lean::closure_set(x_208, 8, x_185);
lean::closure_set(x_208, 9, x_196);
x_209 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_209, 0, x_206);
lean::closure_set(x_209, 1, x_208);
x_210 = l_lean_elaborator_locally(x_209, x_1, x_2, x_3);
return x_210;
}
}
else
{
obj* x_214; 
lean::dec(x_173);
lean::dec(x_170);
lean::dec(x_11);
x_214 = lean::box(0);
x_4 = x_214;
goto lbl_5;
}
}
}
lbl_5:
{
obj* x_216; obj* x_217; obj* x_218; obj* x_219; 
lean::dec(x_4);
x_216 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_216, 0, x_0);
x_217 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1;
x_218 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg___boxed), 5, 2);
lean::closure_set(x_218, 0, x_216);
lean::closure_set(x_218, 1, x_217);
x_219 = l_lean_elaborator_locally(x_218, x_1, x_2, x_3);
return x_219;
}
}
}
obj* l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__10(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_lean_elaborator_declaration_elaborate___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_lean_elaborator_declaration_elaborate___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_4);
lean::dec(x_6);
return x_9;
}
}
obj* l_lean_elaborator_declaration_elaborate___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12) {
_start:
{
obj* x_13; 
x_13 = l_lean_elaborator_declaration_elaborate___lambda__3(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean::dec(x_7);
lean::dec(x_8);
lean::dec(x_10);
return x_13;
}
}
obj* l_lean_elaborator_declaration_elaborate___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
_start:
{
obj* x_14; 
x_14 = l_lean_elaborator_declaration_elaborate___lambda__5(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
return x_14;
}
}
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_name_quick__lt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = l_lean_name_quick__lt(x_5, x_1);
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___rarg___boxed), 2, 0);
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
x_5 = l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___rarg(x_2, x_1);
return x_5;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___rarg), 3, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___rarg), 3, 0);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6___rarg), 3, 0);
return x_2;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__4(obj* x_0, obj* x_1, obj* x_2) {
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
x_16 = l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6___rarg(x_9, x_1, x_15);
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
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_31; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 3);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_3, 4);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_16);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_1);
x_20 = x_19;
x_21 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__4(x_12, x_2, x_20);
x_22 = lean::cnstr_get(x_3, 5);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_3, 6);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_3, 7);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_3, 8);
lean::inc(x_28);
lean::dec(x_3);
x_31 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_31, 0, x_4);
lean::cnstr_set(x_31, 1, x_6);
lean::cnstr_set(x_31, 2, x_8);
lean::cnstr_set(x_31, 3, x_10);
lean::cnstr_set(x_31, 4, x_21);
lean::cnstr_set(x_31, 5, x_22);
lean::cnstr_set(x_31, 6, x_24);
lean::cnstr_set(x_31, 7, x_26);
lean::cnstr_set(x_31, 8, x_28);
return x_31;
}
}
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_28; uint8 x_29; 
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
lean::inc(x_7);
x_15 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_7);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_16, 0);
x_23 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_25 = x_16;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_16);
 x_25 = lean::box(0);
}
x_28 = l_lean_expander_binding__annotation__update;
x_29 = l_lean_parser_syntax_is__of__kind___main(x_28, x_23);
lean::dec(x_23);
if (x_29 == 0)
{
uint8 x_33; obj* x_34; obj* x_35; 
lean::dec(x_18);
lean::dec(x_21);
x_33 = 1;
x_34 = lean::box(x_33);
if (lean::is_scalar(x_25)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_25;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_3);
x_12 = x_35;
goto lbl_13;
}
else
{
obj* x_37; 
lean::dec(x_25);
x_37 = lean::box(0);
x_26 = x_37;
goto lbl_27;
}
lbl_13:
{
obj* x_38; obj* x_40; obj* x_43; 
x_38 = lean::cnstr_get(x_12, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_12, 1);
lean::inc(x_40);
lean::dec(x_12);
x_43 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9(x_9, x_1, x_2, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_7);
lean::dec(x_11);
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
obj* x_51; obj* x_53; uint8 x_54; 
x_51 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_set(x_43, 0, lean::box(0));
 x_53 = x_43;
} else {
 lean::inc(x_51);
 lean::dec(x_43);
 x_53 = lean::box(0);
}
x_54 = lean::unbox(x_38);
if (x_54 == 0)
{
obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_7);
lean::dec(x_11);
x_57 = lean::cnstr_get(x_51, 0);
x_59 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 x_61 = x_51;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_51);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_57);
lean::cnstr_set(x_62, 1, x_59);
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
obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_64 = lean::cnstr_get(x_51, 0);
x_66 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 x_68 = x_51;
} else {
 lean::inc(x_64);
 lean::inc(x_66);
 lean::dec(x_51);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_11;
}
lean::cnstr_set(x_69, 0, x_7);
lean::cnstr_set(x_69, 1, x_64);
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_66);
if (lean::is_scalar(x_53)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_53;
}
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
}
}
lbl_27:
{
obj* x_74; 
lean::dec(x_26);
lean::inc(x_2);
x_74 = l_lean_elaborator_current__scope(x_1, x_2, x_3);
if (lean::obj_tag(x_74) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_18);
lean::dec(x_21);
x_81 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_83 = x_74;
} else {
 lean::inc(x_81);
 lean::dec(x_74);
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
obj* x_85; obj* x_88; obj* x_90; obj* x_93; obj* x_94; obj* x_97; 
x_85 = lean::cnstr_get(x_74, 0);
lean::inc(x_85);
lean::dec(x_74);
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_85, 1);
lean::inc(x_90);
lean::dec(x_85);
x_93 = l_lean_elaborator_mangle__ident(x_21);
x_94 = lean::cnstr_get(x_88, 4);
lean::inc(x_94);
lean::dec(x_88);
x_97 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_94, x_93);
if (lean::obj_tag(x_97) == 0)
{
obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_110; 
lean::dec(x_18);
x_99 = lean::box(0);
x_100 = l_lean_name_to__string___closed__1;
lean::inc(x_93);
x_102 = l_lean_name_to__string__with__sep___main(x_100, x_93);
x_103 = l_lean_parser_substring_of__string(x_102);
x_104 = lean::box(0);
x_105 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_105, 0, x_99);
lean::cnstr_set(x_105, 1, x_103);
lean::cnstr_set(x_105, 2, x_93);
lean::cnstr_set(x_105, 3, x_104);
lean::cnstr_set(x_105, 4, x_104);
x_106 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_106, 0, x_105);
x_107 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_107, 0, x_106);
x_108 = l_string_iterator_extract___main___closed__1;
lean::inc(x_2);
x_110 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_107, x_108, x_1, x_2, x_90);
lean::dec(x_90);
lean::dec(x_107);
if (lean::obj_tag(x_110) == 0)
{
obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
x_117 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_119 = x_110;
} else {
 lean::inc(x_117);
 lean::dec(x_110);
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
obj* x_121; obj* x_124; obj* x_126; uint8 x_127; obj* x_128; obj* x_129; 
x_121 = lean::cnstr_get(x_110, 0);
lean::inc(x_121);
lean::dec(x_110);
x_124 = lean::cnstr_get(x_121, 1);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 x_126 = x_121;
} else {
 lean::inc(x_124);
 lean::dec(x_121);
 x_126 = lean::box(0);
}
x_127 = 0;
x_128 = lean::box(x_127);
if (lean::is_scalar(x_126)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_126;
}
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_124);
x_12 = x_129;
goto lbl_13;
}
}
else
{
obj* x_130; obj* x_133; obj* x_136; obj* x_138; 
x_130 = lean::cnstr_get(x_97, 0);
lean::inc(x_130);
lean::dec(x_97);
x_133 = lean::cnstr_get(x_130, 1);
lean::inc(x_133);
lean::dec(x_130);
x_136 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___lambda__1___boxed), 4, 3);
lean::closure_set(x_136, 0, x_133);
lean::closure_set(x_136, 1, x_18);
lean::closure_set(x_136, 2, x_93);
lean::inc(x_2);
x_138 = l_lean_elaborator_modify__current__scope(x_136, x_1, x_2, x_90);
if (lean::obj_tag(x_138) == 0)
{
obj* x_143; obj* x_145; obj* x_146; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
x_143 = lean::cnstr_get(x_138, 0);
if (lean::is_exclusive(x_138)) {
 x_145 = x_138;
} else {
 lean::inc(x_143);
 lean::dec(x_138);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_143);
return x_146;
}
else
{
obj* x_147; obj* x_150; obj* x_152; uint8 x_153; obj* x_154; obj* x_155; 
x_147 = lean::cnstr_get(x_138, 0);
lean::inc(x_147);
lean::dec(x_138);
x_150 = lean::cnstr_get(x_147, 1);
if (lean::is_exclusive(x_147)) {
 lean::cnstr_release(x_147, 0);
 x_152 = x_147;
} else {
 lean::inc(x_150);
 lean::dec(x_147);
 x_152 = lean::box(0);
}
x_153 = 0;
x_154 = lean::box(x_153);
if (lean::is_scalar(x_152)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_152;
}
lean::cnstr_set(x_155, 0, x_154);
lean::cnstr_set(x_155, 1, x_150);
x_12 = x_155;
goto lbl_13;
}
}
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
obj* l_lean_elaborator_variables_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; 
x_4 = l_lean_parser_command_variables_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_16; obj* x_18; 
lean::dec(x_10);
lean::inc(x_0);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_0);
x_16 = l_lean_elaborator_variables_elaborate___closed__1;
lean::inc(x_2);
x_18 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_15, x_16, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_15);
if (lean::obj_tag(x_18) == 0)
{
obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_0);
lean::dec(x_2);
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
obj* x_27; obj* x_30; obj* x_32; obj* x_36; 
x_27 = lean::cnstr_get(x_18, 0);
lean::inc(x_27);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
lean::dec(x_27);
lean::inc(x_2);
x_36 = l_lean_elaborator_simple__binders__to__pexpr(x_30, x_1, x_2, x_32);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_0);
lean::dec(x_2);
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
obj* x_43; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_36, 0);
lean::inc(x_43);
lean::dec(x_36);
x_46 = lean::cnstr_get(x_43, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_43, 1);
lean::inc(x_48);
lean::dec(x_43);
x_51 = l_lean_elaborator_variables_elaborate___closed__2;
x_52 = lean_expr_mk_mdata(x_51, x_46);
x_53 = l_lean_elaborator_old__elab__command(x_0, x_52, x_1, x_2, x_48);
lean::dec(x_0);
return x_53;
}
}
}
else
{
obj* x_55; obj* x_59; 
x_55 = lean::cnstr_get(x_10, 0);
lean::inc(x_55);
lean::dec(x_10);
lean::inc(x_2);
x_59 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9(x_55, x_1, x_2, x_3);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_0);
lean::dec(x_2);
x_62 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 x_64 = x_59;
} else {
 lean::inc(x_62);
 lean::dec(x_59);
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
obj* x_66; obj* x_69; obj* x_71; obj* x_75; 
x_66 = lean::cnstr_get(x_59, 0);
lean::inc(x_66);
lean::dec(x_59);
x_69 = lean::cnstr_get(x_66, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
lean::dec(x_66);
lean::inc(x_2);
x_75 = l_lean_elaborator_simple__binders__to__pexpr(x_69, x_1, x_2, x_71);
if (lean::obj_tag(x_75) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_0);
lean::dec(x_2);
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
obj* x_82; obj* x_85; obj* x_87; obj* x_90; obj* x_91; obj* x_92; 
x_82 = lean::cnstr_get(x_75, 0);
lean::inc(x_82);
lean::dec(x_75);
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_82, 1);
lean::inc(x_87);
lean::dec(x_82);
x_90 = l_lean_elaborator_variables_elaborate___closed__2;
x_91 = lean_expr_mk_mdata(x_90, x_85);
x_92 = l_lean_elaborator_old__elab__command(x_0, x_91, x_1, x_2, x_87);
lean::dec(x_0);
return x_92;
}
}
}
}
}
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
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
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_variables_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_variables_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_foldl___main___at_lean_elaborator_include_elaborate___spec__1(obj* x_0, obj* x_1) {
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
x_9 = l_rbmap_insert___main___at_lean_name__set_insert___spec__1(x_0, x_7, x_8);
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* l_lean_elaborator_include_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 4);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 5);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
lean::dec(x_0);
x_17 = l_list_foldl___main___at_lean_elaborator_include_elaborate___spec__1(x_12, x_14);
x_18 = lean::cnstr_get(x_1, 6);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_1, 7);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_1, 8);
lean::inc(x_22);
lean::dec(x_1);
x_25 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_8);
lean::cnstr_set(x_25, 4, x_10);
lean::cnstr_set(x_25, 5, x_17);
lean::cnstr_set(x_25, 6, x_18);
lean::cnstr_set(x_25, 7, x_20);
lean::cnstr_set(x_25, 8, x_22);
return x_25;
}
}
obj* l_lean_elaborator_include_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_4 = l_lean_parser_command_include_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_include_elaborate___lambda__1), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = l_lean_elaborator_modify__current__scope(x_9, x_1, x_2, x_3);
return x_10;
}
}
obj* l_lean_elaborator_include_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_include_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_lean_elaborator_module_header_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; 
x_4 = l_lean_parser_module_header_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_9);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_0);
x_14 = l_lean_elaborator_module_header_elaborate___closed__1;
x_15 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_13, x_14, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_13);
return x_15;
}
else
{
obj* x_18; obj* x_19; 
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_18 = x_10;
} else {
 lean::dec(x_10);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_9, 1);
lean::inc(x_19);
lean::dec(x_9);
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_18);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_3);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_19);
if (lean::is_scalar(x_18)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_18;
}
lean::cnstr_set(x_29, 0, x_0);
x_30 = l_lean_elaborator_module_header_elaborate___closed__1;
x_31 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_29, x_30, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_29);
return x_31;
}
}
}
}
obj* l_lean_elaborator_module_header_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_module_header_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* x_14; obj* x_17; obj* x_20; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; 
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
lean::dec(x_30);
x_35 = l_lean_elaborator_prec__to__nat___main(x_17);
x_36 = lean::box(0);
lean::inc(x_33);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_33);
lean::cnstr_set(x_38, 1, x_35);
lean::cnstr_set(x_38, 2, x_36);
x_39 = l_lean_parser_trie_insert___rarg(x_27, x_33, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_25);
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
x_1 = l_lean_expander_expand__bracketed__binder___main___closed__8;
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
obj* x_18; obj* x_21; obj* x_24; obj* x_27; obj* x_28; obj* x_29; 
x_18 = lean::cnstr_get(x_13, 0);
lean::inc(x_18);
lean::dec(x_13);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_string_trim(x_21);
lean::dec(x_21);
lean::inc(x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_27, 0, x_24);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed), 8, 3);
lean::closure_set(x_29, 0, x_24);
lean::closure_set(x_29, 1, x_28);
lean::closure_set(x_29, 2, x_27);
x_9 = x_29;
goto lbl_10;
}
lbl_8:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_6);
lean::dec(x_4);
x_32 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_34 = x_7;
} else {
 lean::inc(x_32);
 lean::dec(x_7);
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
obj* x_36; obj* x_39; 
x_36 = lean::cnstr_get(x_7, 0);
lean::inc(x_36);
lean::dec(x_7);
x_39 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(x_4);
if (lean::obj_tag(x_39) == 0)
{
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_6);
lean::dec(x_36);
x_42 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_44 = x_39;
} else {
 lean::inc(x_42);
 lean::dec(x_39);
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
obj* x_46; obj* x_48; obj* x_49; obj* x_50; 
x_46 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_48 = x_39;
} else {
 lean::inc(x_46);
 lean::dec(x_39);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_6;
}
lean::cnstr_set(x_49, 0, x_36);
lean::cnstr_set(x_49, 1, x_46);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
lbl_10:
{
obj* x_51; obj* x_53; 
x_53 = lean::cnstr_get(x_2, 1);
lean::inc(x_53);
lean::dec(x_2);
if (lean::obj_tag(x_53) == 0)
{
obj* x_56; 
x_56 = l_lean_expander_no__expansion___closed__1;
x_51 = x_56;
goto lbl_52;
}
else
{
obj* x_57; 
x_57 = lean::cnstr_get(x_53, 0);
lean::inc(x_57);
lean::dec(x_53);
switch (lean::obj_tag(x_57)) {
case 0:
{
obj* x_61; 
lean::dec(x_57);
x_61 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
x_51 = x_61;
goto lbl_52;
}
case 1:
{
obj* x_63; 
lean::dec(x_57);
x_63 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2;
x_51 = x_63;
goto lbl_52;
}
default:
{
obj* x_64; obj* x_67; 
x_64 = lean::cnstr_get(x_57, 0);
lean::inc(x_64);
lean::dec(x_57);
x_67 = lean::cnstr_get(x_64, 1);
lean::inc(x_67);
lean::dec(x_64);
if (lean::obj_tag(x_67) == 0)
{
obj* x_70; 
x_70 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3;
x_51 = x_70;
goto lbl_52;
}
else
{
obj* x_71; obj* x_73; obj* x_74; 
x_71 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_set(x_67, 0, lean::box(0));
 x_73 = x_67;
} else {
 lean::inc(x_71);
 lean::dec(x_67);
 x_73 = lean::box(0);
}
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
switch (lean::obj_tag(x_74)) {
case 0:
{
obj* x_77; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_77 = lean::cnstr_get(x_74, 0);
lean::inc(x_77);
lean::dec(x_74);
x_80 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_77);
x_81 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_81, 0, x_80);
if (lean::is_scalar(x_73)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_73;
}
lean::cnstr_set(x_82, 0, x_81);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
x_51 = x_83;
goto lbl_52;
}
case 2:
{
obj* x_84; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_84 = lean::cnstr_get(x_74, 0);
lean::inc(x_84);
lean::dec(x_74);
x_87 = lean::cnstr_get(x_84, 2);
lean::inc(x_87);
lean::dec(x_84);
x_90 = l_lean_elaborator_prec__to__nat___main(x_87);
x_91 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_91, 0, x_90);
if (lean::is_scalar(x_73)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_73;
}
lean::cnstr_set(x_92, 0, x_91);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
x_51 = x_93;
goto lbl_52;
}
default:
{
obj* x_96; 
lean::dec(x_73);
lean::dec(x_74);
x_96 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
x_51 = x_96;
goto lbl_52;
}
}
}
}
}
}
lbl_52:
{
if (lean::obj_tag(x_51) == 0)
{
obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_9);
x_98 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_100 = x_51;
} else {
 lean::inc(x_98);
 lean::dec(x_51);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
x_7 = x_101;
goto lbl_8;
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_102 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_104 = x_51;
} else {
 lean::inc(x_102);
 lean::dec(x_51);
 x_104 = lean::box(0);
}
x_105 = l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(x_102);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_9);
lean::cnstr_set(x_106, 1, x_105);
if (lean::is_scalar(x_104)) {
 x_107 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_107 = x_104;
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
lean::dec(x_49);
x_21 = x_52;
goto lbl_22;
}
}
lbl_22:
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(x_18);
x_55 = l_list_join___main___rarg(x_54);
x_56 = lean::cnstr_get(x_1, 0);
lean::inc(x_56);
lean::dec(x_1);
if (lean::obj_tag(x_56) == 0)
{
obj* x_59; 
x_59 = lean::cnstr_get(x_3, 0);
lean::inc(x_59);
lean::dec(x_3);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_77; obj* x_78; 
x_62 = lean::cnstr_get(x_2, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_2, 1);
lean::inc(x_64);
x_66 = lean::box(0);
x_67 = lean_name_mk_string(x_66, x_21);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1), 7, 2);
lean::closure_set(x_68, 0, x_0);
lean::closure_set(x_68, 1, x_55);
x_69 = l_lean_parser_token__map_insert___rarg(x_64, x_67, x_68);
x_70 = lean::cnstr_get(x_2, 2);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_2, 3);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_2, 4);
lean::inc(x_74);
lean::dec(x_2);
x_77 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_77, 0, x_62);
lean::cnstr_set(x_77, 1, x_69);
lean::cnstr_set(x_77, 2, x_70);
lean::cnstr_set(x_77, 3, x_72);
lean::cnstr_set(x_77, 4, x_74);
if (lean::is_scalar(x_20)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_20;
}
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
else
{
obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_95; obj* x_98; obj* x_99; 
lean::dec(x_59);
x_80 = lean::cnstr_get(x_2, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_2, 1);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_2, 2);
lean::inc(x_84);
x_86 = lean::box(0);
x_87 = lean_name_mk_string(x_86, x_21);
x_88 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(x_55);
x_89 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_88);
x_91 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3), 8, 2);
lean::closure_set(x_91, 0, x_0);
lean::closure_set(x_91, 1, x_90);
x_92 = l_lean_parser_token__map_insert___rarg(x_84, x_87, x_91);
x_93 = lean::cnstr_get(x_2, 3);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_2, 4);
lean::inc(x_95);
lean::dec(x_2);
x_98 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_98, 0, x_80);
lean::cnstr_set(x_98, 1, x_82);
lean::cnstr_set(x_98, 2, x_92);
lean::cnstr_set(x_98, 3, x_93);
lean::cnstr_set(x_98, 4, x_95);
if (lean::is_scalar(x_20)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_20;
}
lean::cnstr_set(x_99, 0, x_98);
return x_99;
}
}
else
{
obj* x_101; 
lean::dec(x_56);
x_101 = lean::cnstr_get(x_3, 0);
lean::inc(x_101);
lean::dec(x_3);
if (lean::obj_tag(x_101) == 0)
{
obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_119; obj* x_120; 
x_104 = lean::cnstr_get(x_2, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_2, 1);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_2, 2);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_2, 3);
lean::inc(x_110);
x_112 = lean::box(0);
x_113 = lean_name_mk_string(x_112, x_21);
x_114 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1), 7, 2);
lean::closure_set(x_114, 0, x_0);
lean::closure_set(x_114, 1, x_55);
x_115 = l_lean_parser_token__map_insert___rarg(x_110, x_113, x_114);
x_116 = lean::cnstr_get(x_2, 4);
lean::inc(x_116);
lean::dec(x_2);
x_119 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_119, 0, x_104);
lean::cnstr_set(x_119, 1, x_106);
lean::cnstr_set(x_119, 2, x_108);
lean::cnstr_set(x_119, 3, x_115);
lean::cnstr_set(x_119, 4, x_116);
if (lean::is_scalar(x_20)) {
 x_120 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_120 = x_20;
}
lean::cnstr_set(x_120, 0, x_119);
return x_120;
}
else
{
obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
lean::dec(x_101);
x_122 = lean::cnstr_get(x_2, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_2, 1);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_2, 2);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_2, 3);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_2, 4);
lean::inc(x_130);
lean::dec(x_2);
x_133 = lean::box(0);
x_134 = lean_name_mk_string(x_133, x_21);
x_135 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(x_55);
x_136 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
x_137 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_135);
x_138 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3), 8, 2);
lean::closure_set(x_138, 0, x_0);
lean::closure_set(x_138, 1, x_137);
x_139 = l_lean_parser_token__map_insert___rarg(x_130, x_134, x_138);
x_140 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_140, 0, x_122);
lean::cnstr_set(x_140, 1, x_124);
lean::cnstr_set(x_140, 2, x_126);
lean::cnstr_set(x_140, 3, x_128);
lean::cnstr_set(x_140, 4, x_139);
if (lean::is_scalar(x_20)) {
 x_141 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_141 = x_20;
}
lean::cnstr_set(x_141, 0, x_140);
return x_141;
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
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_15; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
x_15 = l_lean_elaborator_command__parser__config_register__notation__tokens(x_13, x_0);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_26; 
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_19 = l_lean_parser_command_reserve__notation_has__view;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_8);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::inc(x_3);
x_26 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_24, x_16, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_24);
if (lean::obj_tag(x_26) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_3);
lean::dec(x_10);
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
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_26, 0);
lean::inc(x_35);
lean::dec(x_26);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
x_0 = x_38;
x_1 = x_10;
x_4 = x_40;
goto _start;
}
}
else
{
obj* x_45; 
lean::dec(x_8);
x_45 = lean::cnstr_get(x_15, 0);
lean::inc(x_45);
lean::dec(x_15);
x_0 = x_45;
x_1 = x_10;
goto _start;
}
}
}
}
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_17; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 2);
lean::inc(x_15);
x_17 = l_lean_elaborator_command__parser__config_register__notation__tokens(x_15, x_0);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_29; 
lean::dec(x_8);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_22 = l_lean_parser_command_notation_has__view;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_13);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::inc(x_3);
x_29 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_27, x_19, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_27);
if (lean::obj_tag(x_29) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_3);
lean::dec(x_10);
x_34 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
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
obj* x_38; obj* x_41; obj* x_43; 
x_38 = lean::cnstr_get(x_29, 0);
lean::inc(x_38);
lean::dec(x_29);
x_41 = lean::cnstr_get(x_38, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 1);
lean::inc(x_43);
lean::dec(x_38);
x_0 = x_41;
x_1 = x_10;
x_4 = x_43;
goto _start;
}
}
else
{
obj* x_47; obj* x_50; obj* x_54; 
x_47 = lean::cnstr_get(x_17, 0);
lean::inc(x_47);
lean::dec(x_17);
x_50 = lean::cnstr_get(x_8, 0);
lean::inc(x_50);
lean::dec(x_8);
lean::inc(x_13);
x_54 = l_lean_elaborator_command__parser__config_register__notation__parser(x_50, x_13, x_47);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_65; 
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
lean::dec(x_54);
x_58 = l_lean_parser_command_notation_has__view;
x_59 = lean::cnstr_get(x_58, 1);
lean::inc(x_59);
lean::dec(x_58);
x_62 = lean::apply_1(x_59, x_13);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::inc(x_3);
x_65 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_63, x_55, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_63);
if (lean::obj_tag(x_65) == 0)
{
obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_3);
lean::dec(x_10);
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
obj* x_74; obj* x_77; obj* x_79; 
x_74 = lean::cnstr_get(x_65, 0);
lean::inc(x_74);
lean::dec(x_65);
x_77 = lean::cnstr_get(x_74, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 1);
lean::inc(x_79);
lean::dec(x_74);
x_0 = x_77;
x_1 = x_10;
x_4 = x_79;
goto _start;
}
}
else
{
obj* x_84; 
lean::dec(x_13);
x_84 = lean::cnstr_get(x_54, 0);
lean::inc(x_84);
lean::dec(x_54);
x_0 = x_84;
x_1 = x_10;
goto _start;
}
}
}
}
}
obj* l_lean_elaborator_update__parser__config(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; 
lean::inc(x_2);
lean::inc(x_1);
x_5 = l_lean_elaborator_current__scope(x_0, x_1, x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_1);
lean::dec(x_2);
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
obj* x_12; obj* x_15; obj* x_17; obj* x_20; obj* x_22; obj* x_24; obj* x_28; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = lean::cnstr_get(x_1, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_2, 0);
lean::inc(x_24);
lean::inc(x_1);
lean::inc(x_24);
x_28 = l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(x_22, x_24, x_0, x_1, x_17);
if (lean::obj_tag(x_28) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_20);
lean::dec(x_24);
x_34 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_34);
 lean::dec(x_28);
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
obj* x_38; obj* x_41; obj* x_43; obj* x_46; obj* x_48; obj* x_52; obj* x_53; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
lean::dec(x_28);
x_41 = lean::cnstr_get(x_38, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 1);
lean::inc(x_43);
lean::dec(x_38);
x_46 = lean::cnstr_get(x_2, 1);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_15, 2);
lean::inc(x_48);
lean::dec(x_15);
lean::inc(x_46);
x_52 = l_list_append___rarg(x_46, x_48);
x_53 = l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(x_41, x_52, x_0, x_1, x_43);
if (lean::obj_tag(x_53) == 0)
{
obj* x_58; obj* x_60; obj* x_61; 
lean::dec(x_2);
lean::dec(x_20);
lean::dec(x_24);
lean::dec(x_46);
x_58 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_60 = x_53;
} else {
 lean::inc(x_58);
 lean::dec(x_53);
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
obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_62 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_64 = x_53;
} else {
 lean::inc(x_62);
 lean::dec(x_53);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 1);
 x_67 = x_62;
} else {
 lean::inc(x_65);
 lean::dec(x_62);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_2, 2);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_2, 3);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_2, 4);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_2, 5);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_20, 1);
lean::inc(x_76);
lean::dec(x_20);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_65);
lean::cnstr_set(x_79, 1, x_76);
x_80 = lean::cnstr_get(x_2, 7);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_2, 8);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_2, 9);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_2, 10);
lean::inc(x_86);
lean::dec(x_2);
x_89 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_89, 0, x_24);
lean::cnstr_set(x_89, 1, x_46);
lean::cnstr_set(x_89, 2, x_68);
lean::cnstr_set(x_89, 3, x_70);
lean::cnstr_set(x_89, 4, x_72);
lean::cnstr_set(x_89, 5, x_74);
lean::cnstr_set(x_89, 6, x_79);
lean::cnstr_set(x_89, 7, x_80);
lean::cnstr_set(x_89, 8, x_82);
lean::cnstr_set(x_89, 9, x_84);
lean::cnstr_set(x_89, 10, x_86);
x_90 = lean::box(0);
if (lean::is_scalar(x_67)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_67;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
if (lean::is_scalar(x_64)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_64;
}
lean::cnstr_set(x_92, 0, x_91);
return x_92;
}
}
}
}
}
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_lean_elaborator_update__parser__config___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_update__parser__config(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* _init_l_lean_elaborator_postprocess__notation__spec___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::mk_string(":");
x_2 = l_string_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_lean_parser_max__prec;
x_7 = l_lean_parser_number_view_of__nat(x_6);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
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
obj* l_lean_elaborator_reserve__notation_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; obj* x_43; 
x_4 = l_lean_parser_command_reserve__notation_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_elaborator_postprocess__notation__spec(x_13);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::cnstr_get(x_3, 0);
lean::inc(x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::cnstr_get(x_3, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_3, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_3, 3);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_3, 4);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_3, 5);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_3, 6);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_3, 7);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_3, 8);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_3, 9);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_3, 10);
lean::inc(x_39);
lean::dec(x_3);
x_42 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_42, 0, x_20);
lean::cnstr_set(x_42, 1, x_21);
lean::cnstr_set(x_42, 2, x_23);
lean::cnstr_set(x_42, 3, x_25);
lean::cnstr_set(x_42, 4, x_27);
lean::cnstr_set(x_42, 5, x_29);
lean::cnstr_set(x_42, 6, x_31);
lean::cnstr_set(x_42, 7, x_33);
lean::cnstr_set(x_42, 8, x_35);
lean::cnstr_set(x_42, 9, x_37);
lean::cnstr_set(x_42, 10, x_39);
x_43 = l_lean_elaborator_update__parser__config(x_1, x_2, x_42);
return x_43;
}
}
obj* l_lean_elaborator_reserve__notation_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_reserve__notation_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* x_46; 
lean::dec(x_6);
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_21);
lean::dec(x_24);
lean::dec(x_27);
x_46 = lean::box(0);
return x_46;
}
else
{
obj* x_47; obj* x_49; obj* x_52; obj* x_55; obj* x_57; obj* x_60; uint8 x_62; 
x_47 = lean::cnstr_get(x_30, 3);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_36, 0);
lean::inc(x_49);
lean::dec(x_36);
x_52 = lean::cnstr_get(x_27, 1);
lean::inc(x_52);
lean::dec(x_27);
x_55 = l_string_trim(x_52);
lean::dec(x_52);
x_57 = lean::cnstr_get(x_49, 1);
lean::inc(x_57);
lean::dec(x_49);
x_60 = l_string_trim(x_57);
lean::dec(x_57);
x_62 = lean::string_dec_eq(x_55, x_60);
lean::dec(x_60);
lean::dec(x_55);
if (x_62 == 0)
{
obj* x_73; 
lean::dec(x_6);
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_21);
lean::dec(x_24);
lean::dec(x_47);
x_73 = lean::box(0);
return x_73;
}
else
{
uint8 x_74; 
x_74 = l_lean_elaborator_match__precedence___main(x_24, x_47);
if (x_74 == 0)
{
obj* x_81; 
lean::dec(x_6);
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_21);
x_81 = lean::box(0);
return x_81;
}
else
{
obj* x_82; 
x_82 = lean::box(0);
x_34 = x_82;
goto lbl_35;
}
}
}
lbl_33:
{
if (lean::obj_tag(x_32) == 0)
{
obj* x_86; 
lean::dec(x_6);
lean::dec(x_30);
lean::dec(x_4);
x_86 = lean::box(0);
return x_86;
}
else
{
obj* x_87; obj* x_90; 
x_87 = lean::cnstr_get(x_32, 0);
lean::inc(x_87);
lean::dec(x_32);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_30);
lean::cnstr_set(x_90, 1, x_87);
x_7 = x_90;
goto lbl_8;
}
}
lbl_35:
{
obj* x_92; 
lean::dec(x_34);
x_92 = lean::cnstr_get(x_9, 1);
lean::inc(x_92);
lean::dec(x_9);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; 
x_95 = lean::cnstr_get(x_21, 1);
lean::inc(x_95);
lean::dec(x_21);
if (lean::obj_tag(x_95) == 0)
{
obj* x_98; 
if (lean::is_scalar(x_29)) {
 x_98 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_98 = x_29;
}
lean::cnstr_set(x_98, 0, x_95);
x_32 = x_98;
goto lbl_33;
}
else
{
obj* x_101; 
lean::dec(x_29);
lean::dec(x_95);
x_101 = lean::box(0);
x_32 = x_101;
goto lbl_33;
}
}
else
{
obj* x_103; obj* x_105; 
lean::dec(x_29);
x_103 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_set(x_92, 0, lean::box(0));
 x_105 = x_92;
} else {
 lean::inc(x_103);
 lean::dec(x_92);
 x_105 = lean::box(0);
}
switch (lean::obj_tag(x_103)) {
case 0:
{
obj* x_106; 
x_106 = lean::cnstr_get(x_21, 1);
lean::inc(x_106);
lean::dec(x_21);
if (lean::obj_tag(x_106) == 0)
{
obj* x_111; 
lean::dec(x_105);
lean::dec(x_103);
x_111 = lean::box(0);
x_32 = x_111;
goto lbl_33;
}
else
{
obj* x_112; 
x_112 = lean::cnstr_get(x_106, 0);
lean::inc(x_112);
switch (lean::obj_tag(x_112)) {
case 0:
{
obj* x_114; obj* x_117; obj* x_120; obj* x_123; uint8 x_126; 
x_114 = lean::cnstr_get(x_103, 0);
lean::inc(x_114);
lean::dec(x_103);
x_117 = lean::cnstr_get(x_112, 0);
lean::inc(x_117);
lean::dec(x_112);
x_120 = lean::cnstr_get(x_114, 1);
lean::inc(x_120);
lean::dec(x_114);
x_123 = lean::cnstr_get(x_117, 1);
lean::inc(x_123);
lean::dec(x_117);
x_126 = l_lean_elaborator_match__precedence___main(x_120, x_123);
if (x_126 == 0)
{
obj* x_129; 
lean::dec(x_105);
lean::dec(x_106);
x_129 = lean::box(0);
x_32 = x_129;
goto lbl_33;
}
else
{
obj* x_130; 
if (lean::is_scalar(x_105)) {
 x_130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_130 = x_105;
}
lean::cnstr_set(x_130, 0, x_106);
x_32 = x_130;
goto lbl_33;
}
}
default:
{
obj* x_135; 
lean::dec(x_105);
lean::dec(x_103);
lean::dec(x_106);
lean::dec(x_112);
x_135 = lean::box(0);
x_32 = x_135;
goto lbl_33;
}
}
}
}
case 1:
{
obj* x_136; 
x_136 = lean::cnstr_get(x_21, 1);
lean::inc(x_136);
lean::dec(x_21);
if (lean::obj_tag(x_136) == 0)
{
obj* x_141; 
lean::dec(x_105);
lean::dec(x_103);
x_141 = lean::box(0);
x_32 = x_141;
goto lbl_33;
}
else
{
obj* x_142; 
x_142 = lean::cnstr_get(x_136, 0);
lean::inc(x_142);
switch (lean::obj_tag(x_142)) {
case 1:
{
obj* x_144; obj* x_147; obj* x_150; obj* x_153; uint8 x_156; 
x_144 = lean::cnstr_get(x_103, 0);
lean::inc(x_144);
lean::dec(x_103);
x_147 = lean::cnstr_get(x_142, 0);
lean::inc(x_147);
lean::dec(x_142);
x_150 = lean::cnstr_get(x_144, 1);
lean::inc(x_150);
lean::dec(x_144);
x_153 = lean::cnstr_get(x_147, 1);
lean::inc(x_153);
lean::dec(x_147);
x_156 = l_lean_elaborator_match__precedence___main(x_150, x_153);
if (x_156 == 0)
{
obj* x_159; 
lean::dec(x_105);
lean::dec(x_136);
x_159 = lean::box(0);
x_32 = x_159;
goto lbl_33;
}
else
{
obj* x_160; 
if (lean::is_scalar(x_105)) {
 x_160 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_160 = x_105;
}
lean::cnstr_set(x_160, 0, x_136);
x_32 = x_160;
goto lbl_33;
}
}
default:
{
obj* x_165; 
lean::dec(x_105);
lean::dec(x_103);
lean::dec(x_136);
lean::dec(x_142);
x_165 = lean::box(0);
x_32 = x_165;
goto lbl_33;
}
}
}
}
default:
{
obj* x_166; obj* x_168; obj* x_169; obj* x_171; 
x_166 = lean::cnstr_get(x_103, 0);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_set(x_103, 0, lean::box(0));
 x_168 = x_103;
} else {
 lean::inc(x_166);
 lean::dec(x_103);
 x_168 = lean::box(0);
}
x_171 = lean::cnstr_get(x_21, 1);
lean::inc(x_171);
lean::dec(x_21);
if (lean::obj_tag(x_171) == 0)
{
obj* x_177; 
lean::dec(x_105);
lean::dec(x_168);
lean::dec(x_166);
x_177 = lean::box(0);
x_32 = x_177;
goto lbl_33;
}
else
{
obj* x_178; obj* x_180; 
x_178 = lean::cnstr_get(x_171, 0);
if (lean::is_exclusive(x_171)) {
 lean::cnstr_set(x_171, 0, lean::box(0));
 x_180 = x_171;
} else {
 lean::inc(x_178);
 lean::dec(x_171);
 x_180 = lean::box(0);
}
switch (lean::obj_tag(x_178)) {
case 2:
{
obj* x_181; obj* x_184; obj* x_186; 
x_181 = lean::cnstr_get(x_178, 0);
lean::inc(x_181);
lean::dec(x_178);
x_184 = lean::cnstr_get(x_166, 1);
lean::inc(x_184);
if (lean::obj_tag(x_184) == 0)
{
obj* x_188; 
x_188 = lean::cnstr_get(x_181, 1);
lean::inc(x_188);
lean::dec(x_181);
if (lean::obj_tag(x_188) == 0)
{
obj* x_192; 
lean::dec(x_180);
x_192 = lean::box(0);
x_169 = x_192;
goto lbl_170;
}
else
{
obj* x_193; obj* x_195; 
x_193 = lean::cnstr_get(x_188, 0);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_193, 1);
lean::inc(x_195);
lean::dec(x_193);
switch (lean::obj_tag(x_195)) {
case 0:
{
obj* x_199; 
lean::dec(x_195);
if (lean::is_scalar(x_180)) {
 x_199 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_199 = x_180;
}
lean::cnstr_set(x_199, 0, x_188);
x_169 = x_199;
goto lbl_170;
}
default:
{
obj* x_203; 
lean::dec(x_195);
lean::dec(x_188);
lean::dec(x_180);
x_203 = lean::box(0);
x_169 = x_203;
goto lbl_170;
}
}
}
}
else
{
obj* x_205; obj* x_207; 
lean::dec(x_180);
x_205 = lean::cnstr_get(x_184, 0);
lean::inc(x_205);
x_207 = lean::cnstr_get(x_205, 1);
lean::inc(x_207);
lean::dec(x_205);
x_186 = x_207;
goto lbl_187;
}
lbl_187:
{
switch (lean::obj_tag(x_186)) {
case 0:
{
obj* x_210; 
x_210 = lean::cnstr_get(x_181, 1);
lean::inc(x_210);
lean::dec(x_181);
if (lean::obj_tag(x_210) == 0)
{
obj* x_215; 
lean::dec(x_184);
lean::dec(x_186);
x_215 = lean::box(0);
x_169 = x_215;
goto lbl_170;
}
else
{
obj* x_216; obj* x_218; obj* x_219; 
x_216 = lean::cnstr_get(x_210, 0);
if (lean::is_exclusive(x_210)) {
 lean::cnstr_set(x_210, 0, lean::box(0));
 x_218 = x_210;
} else {
 lean::inc(x_216);
 lean::dec(x_210);
 x_218 = lean::box(0);
}
x_219 = lean::cnstr_get(x_216, 1);
lean::inc(x_219);
lean::dec(x_216);
switch (lean::obj_tag(x_219)) {
case 0:
{
obj* x_222; obj* x_225; obj* x_228; obj* x_229; uint8 x_230; 
x_222 = lean::cnstr_get(x_186, 0);
lean::inc(x_222);
lean::dec(x_186);
x_225 = lean::cnstr_get(x_219, 0);
lean::inc(x_225);
lean::dec(x_219);
x_228 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_222);
x_229 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_225);
x_230 = lean::nat_dec_eq(x_228, x_229);
lean::dec(x_229);
lean::dec(x_228);
if (x_230 == 0)
{
obj* x_235; 
lean::dec(x_218);
lean::dec(x_184);
x_235 = lean::box(0);
x_169 = x_235;
goto lbl_170;
}
else
{
obj* x_236; 
if (lean::is_scalar(x_218)) {
 x_236 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_236 = x_218;
}
lean::cnstr_set(x_236, 0, x_184);
x_169 = x_236;
goto lbl_170;
}
}
default:
{
obj* x_241; 
lean::dec(x_218);
lean::dec(x_219);
lean::dec(x_184);
lean::dec(x_186);
x_241 = lean::box(0);
x_169 = x_241;
goto lbl_170;
}
}
}
}
default:
{
obj* x_245; 
lean::dec(x_184);
lean::dec(x_186);
lean::dec(x_181);
x_245 = lean::box(0);
x_169 = x_245;
goto lbl_170;
}
}
}
}
default:
{
obj* x_251; 
lean::dec(x_105);
lean::dec(x_180);
lean::dec(x_178);
lean::dec(x_168);
lean::dec(x_166);
x_251 = lean::box(0);
x_32 = x_251;
goto lbl_33;
}
}
}
lbl_170:
{
if (lean::obj_tag(x_169) == 0)
{
obj* x_255; 
lean::dec(x_105);
lean::dec(x_168);
lean::dec(x_166);
x_255 = lean::box(0);
x_32 = x_255;
goto lbl_33;
}
else
{
obj* x_256; obj* x_258; obj* x_259; obj* x_262; obj* x_263; obj* x_264; obj* x_265; 
x_256 = lean::cnstr_get(x_169, 0);
if (lean::is_exclusive(x_169)) {
 x_258 = x_169;
} else {
 lean::inc(x_256);
 lean::dec(x_169);
 x_258 = lean::box(0);
}
x_259 = lean::cnstr_get(x_166, 0);
lean::inc(x_259);
lean::dec(x_166);
x_262 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_262, 0, x_259);
lean::cnstr_set(x_262, 1, x_256);
if (lean::is_scalar(x_168)) {
 x_263 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_263 = x_168;
}
lean::cnstr_set(x_263, 0, x_262);
if (lean::is_scalar(x_258)) {
 x_264 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_264 = x_258;
}
lean::cnstr_set(x_264, 0, x_263);
if (lean::is_scalar(x_105)) {
 x_265 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_265 = x_105;
}
lean::cnstr_set(x_265, 0, x_264);
x_32 = x_265;
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
obj* x_266; 
x_266 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(x_4);
if (lean::obj_tag(x_266) == 0)
{
obj* x_269; 
lean::dec(x_6);
lean::dec(x_7);
x_269 = lean::box(0);
return x_269;
}
else
{
obj* x_270; obj* x_272; obj* x_273; obj* x_274; 
x_270 = lean::cnstr_get(x_266, 0);
if (lean::is_exclusive(x_266)) {
 x_272 = x_266;
} else {
 lean::inc(x_270);
 lean::dec(x_266);
 x_272 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_273 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_273 = x_6;
}
lean::cnstr_set(x_273, 0, x_7);
lean::cnstr_set(x_273, 1, x_270);
if (lean::is_scalar(x_272)) {
 x_274 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_274 = x_272;
}
lean::cnstr_set(x_274, 0, x_273);
return x_274;
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
obj* l_lean_elaborator_notation_elaborate__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; 
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_notation_elaborate__aux___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = l_list_filter__map___main___rarg(x_5, x_6);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 2);
lean::inc(x_14);
x_16 = l_lean_elaborator_postprocess__notation__spec(x_14);
x_17 = lean::cnstr_get(x_0, 3);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 4);
lean::inc(x_19);
lean::dec(x_0);
x_22 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_22, 0, x_10);
lean::cnstr_set(x_22, 1, x_12);
lean::cnstr_set(x_22, 2, x_16);
lean::cnstr_set(x_22, 3, x_17);
lean::cnstr_set(x_22, 4, x_19);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_3);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_8, 1);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_28; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_2);
x_28 = lean::cnstr_get(x_8, 0);
lean::inc(x_28);
lean::dec(x_8);
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 3);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 4);
lean::inc(x_37);
lean::dec(x_0);
x_40 = l_lean_elaborator_postprocess__notation__spec(x_28);
x_41 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_41, 0, x_31);
lean::cnstr_set(x_41, 1, x_33);
lean::cnstr_set(x_41, 2, x_40);
lean::cnstr_set(x_41, 3, x_35);
lean::cnstr_set(x_41, 4, x_37);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_3);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
return x_43;
}
else
{
obj* x_46; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_8);
lean::dec(x_25);
x_46 = l_lean_parser_command_notation_has__view;
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
lean::dec(x_46);
x_50 = lean::apply_1(x_47, x_0);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = l_lean_elaborator_notation_elaborate__aux___closed__1;
x_53 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_51, x_52, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_51);
if (lean::obj_tag(x_53) == 0)
{
obj* x_56; obj* x_58; obj* x_59; 
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
obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_80; obj* x_81; obj* x_82; 
x_60 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_62 = x_53;
} else {
 lean::inc(x_60);
 lean::dec(x_53);
 x_62 = lean::box(0);
}
x_63 = lean::cnstr_get(x_60, 0);
x_65 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 x_67 = x_60;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_60);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_63, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_63, 1);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_63, 2);
lean::inc(x_72);
x_74 = l_lean_elaborator_postprocess__notation__spec(x_72);
x_75 = lean::cnstr_get(x_63, 3);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_63, 4);
lean::inc(x_77);
lean::dec(x_63);
x_80 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_80, 0, x_68);
lean::cnstr_set(x_80, 1, x_70);
lean::cnstr_set(x_80, 2, x_74);
lean::cnstr_set(x_80, 3, x_75);
lean::cnstr_set(x_80, 4, x_77);
if (lean::is_scalar(x_67)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_67;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_65);
if (lean::is_scalar(x_62)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_62;
}
lean::cnstr_set(x_82, 0, x_81);
return x_82;
}
}
}
}
}
obj* l_lean_elaborator_notation_elaborate__aux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_notation_elaborate__aux(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_lean_elaborator_mk__notation__kind(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_mk__notation__kind___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_elaborator_mk__notation__kind___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_elaborator_mk__notation__kind(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___rarg), 3, 0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_elaborator_register__notation__macro(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_mk__notation__kind___rarg(x_3);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_54; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
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
x_43 = l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1(x_40, x_13, x_21);
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
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_elaborator_register__notation__macro___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_register__notation__macro(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
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
obj* l_lean_elaborator_notation_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_22; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 4);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 5);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 6);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 7);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 8);
lean::inc(x_19);
lean::dec(x_1);
x_22 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_22, 0, x_2);
lean::cnstr_set(x_22, 1, x_4);
lean::cnstr_set(x_22, 2, x_8);
lean::cnstr_set(x_22, 3, x_9);
lean::cnstr_set(x_22, 4, x_11);
lean::cnstr_set(x_22, 5, x_13);
lean::cnstr_set(x_22, 6, x_15);
lean::cnstr_set(x_22, 7, x_17);
lean::cnstr_set(x_22, 8, x_19);
return x_22;
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
obj* l_lean_elaborator_notation_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; uint8 x_16; 
x_4 = l_lean_parser_command_notation_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_11 = lean::cnstr_get(x_8, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
lean::dec(x_11);
x_16 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_13);
lean::dec(x_13);
if (x_16 == 0)
{
obj* x_18; 
x_18 = lean::box(0);
x_9 = x_18;
goto lbl_10;
}
else
{
obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_33; obj* x_36; obj* x_37; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_8);
x_20 = lean::cnstr_get(x_3, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_3, 2);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_3, 3);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_3, 4);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_2, 0);
lean::inc(x_30);
lean::dec(x_2);
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
lean::dec(x_30);
x_36 = lean::box(0);
x_37 = l_lean_elaborator_notation_elaborate___closed__1;
x_38 = 1;
x_39 = l_string_iterator_extract___main___closed__1;
x_40 = l_lean_elaborator_notation_elaborate___closed__2;
x_41 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_41, 0, x_33);
lean::cnstr_set(x_41, 1, x_37);
lean::cnstr_set(x_41, 2, x_36);
lean::cnstr_set(x_41, 3, x_39);
lean::cnstr_set(x_41, 4, x_40);
lean::cnstr_set_scalar(x_41, sizeof(void*)*5, x_38);
x_42 = x_41;
x_43 = lean::cnstr_get(x_3, 5);
lean::inc(x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set(x_45, 1, x_43);
x_46 = lean::cnstr_get(x_3, 6);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_3, 7);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_3, 8);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_3, 9);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_3, 10);
lean::inc(x_54);
lean::dec(x_3);
x_57 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_57, 0, x_20);
lean::cnstr_set(x_57, 1, x_22);
lean::cnstr_set(x_57, 2, x_24);
lean::cnstr_set(x_57, 3, x_26);
lean::cnstr_set(x_57, 4, x_28);
lean::cnstr_set(x_57, 5, x_45);
lean::cnstr_set(x_57, 6, x_46);
lean::cnstr_set(x_57, 7, x_48);
lean::cnstr_set(x_57, 8, x_50);
lean::cnstr_set(x_57, 9, x_52);
lean::cnstr_set(x_57, 10, x_54);
x_58 = lean::box(0);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_57);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
lbl_10:
{
obj* x_63; 
lean::dec(x_9);
lean::inc(x_2);
x_63 = l_lean_elaborator_notation_elaborate__aux(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_63) == 0)
{
obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_2);
x_65 = lean::cnstr_get(x_63, 0);
if (lean::is_exclusive(x_63)) {
 x_67 = x_63;
} else {
 lean::inc(x_65);
 lean::dec(x_63);
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
obj* x_69; obj* x_72; obj* x_74; obj* x_78; 
x_69 = lean::cnstr_get(x_63, 0);
lean::inc(x_69);
lean::dec(x_63);
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
lean::inc(x_72);
x_78 = l_lean_elaborator_register__notation__macro(x_72, x_1, x_2, x_74);
if (lean::obj_tag(x_78) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_2);
lean::dec(x_72);
x_81 = lean::cnstr_get(x_78, 0);
if (lean::is_exclusive(x_78)) {
 x_83 = x_78;
} else {
 lean::inc(x_81);
 lean::dec(x_78);
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
obj* x_85; obj* x_88; 
x_85 = lean::cnstr_get(x_78, 0);
lean::inc(x_85);
lean::dec(x_78);
x_88 = lean::cnstr_get(x_72, 0);
lean::inc(x_88);
lean::dec(x_72);
if (lean::obj_tag(x_88) == 0)
{
obj* x_91; obj* x_93; obj* x_96; obj* x_98; obj* x_100; obj* x_101; obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; obj* x_120; obj* x_121; 
x_91 = lean::cnstr_get(x_85, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_85, 1);
lean::inc(x_93);
lean::dec(x_85);
x_96 = lean::cnstr_get(x_93, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_93, 1);
lean::inc(x_98);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_91);
lean::cnstr_set(x_100, 1, x_98);
x_101 = lean::cnstr_get(x_93, 2);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_93, 3);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_93, 4);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_93, 5);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_93, 6);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_93, 7);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_93, 8);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_93, 9);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_93, 10);
lean::inc(x_117);
lean::dec(x_93);
x_120 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_120, 0, x_96);
lean::cnstr_set(x_120, 1, x_100);
lean::cnstr_set(x_120, 2, x_101);
lean::cnstr_set(x_120, 3, x_103);
lean::cnstr_set(x_120, 4, x_105);
lean::cnstr_set(x_120, 5, x_107);
lean::cnstr_set(x_120, 6, x_109);
lean::cnstr_set(x_120, 7, x_111);
lean::cnstr_set(x_120, 8, x_113);
lean::cnstr_set(x_120, 9, x_115);
lean::cnstr_set(x_120, 10, x_117);
x_121 = l_lean_elaborator_update__parser__config(x_1, x_2, x_120);
return x_121;
}
else
{
obj* x_123; obj* x_125; obj* x_128; obj* x_130; 
lean::dec(x_88);
x_123 = lean::cnstr_get(x_85, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_85, 1);
lean::inc(x_125);
lean::dec(x_85);
x_128 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_notation_elaborate___lambda__1), 2, 1);
lean::closure_set(x_128, 0, x_123);
lean::inc(x_2);
x_130 = l_lean_elaborator_modify__current__scope(x_128, x_1, x_2, x_125);
if (lean::obj_tag(x_130) == 0)
{
obj* x_132; obj* x_134; obj* x_135; 
lean::dec(x_2);
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
return x_135;
}
else
{
obj* x_136; obj* x_139; obj* x_142; 
x_136 = lean::cnstr_get(x_130, 0);
lean::inc(x_136);
lean::dec(x_130);
x_139 = lean::cnstr_get(x_136, 1);
lean::inc(x_139);
lean::dec(x_136);
x_142 = l_lean_elaborator_update__parser__config(x_1, x_2, x_139);
return x_142;
}
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
obj* l_lean_elaborator_notation_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_notation_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_universe_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
lean::inc(x_0);
x_11 = level_mk_param(x_0);
x_12 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_8, x_0, x_11);
x_13 = lean::cnstr_get(x_1, 4);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 5);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 6);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 7);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 8);
lean::inc(x_21);
lean::dec(x_1);
x_24 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_24, 0, x_2);
lean::cnstr_set(x_24, 1, x_4);
lean::cnstr_set(x_24, 2, x_6);
lean::cnstr_set(x_24, 3, x_12);
lean::cnstr_set(x_24, 4, x_13);
lean::cnstr_set(x_24, 5, x_15);
lean::cnstr_set(x_24, 6, x_17);
lean::cnstr_set(x_24, 7, x_19);
lean::cnstr_set(x_24, 8, x_21);
return x_24;
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
obj* l_lean_elaborator_universe_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_2);
x_5 = l_lean_elaborator_current__scope(x_1, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
lean::dec(x_2);
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
obj* x_12; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_33; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = l_lean_parser_command_universe_has__view;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
lean::dec(x_20);
lean::inc(x_0);
x_25 = lean::apply_1(x_21, x_0);
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
lean::dec(x_25);
x_29 = l_lean_elaborator_mangle__ident(x_26);
x_30 = lean::cnstr_get(x_15, 3);
lean::inc(x_30);
lean::dec(x_15);
x_33 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_30, x_29);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_36; 
lean::dec(x_0);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_universe_elaborate___lambda__1), 2, 1);
lean::closure_set(x_35, 0, x_29);
x_36 = l_lean_elaborator_modify__current__scope(x_35, x_1, x_2, x_17);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_37 = x_33;
} else {
 lean::dec(x_33);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_0);
x_39 = l_lean_name_to__string___closed__1;
x_40 = l_lean_name_to__string__with__sep___main(x_39, x_29);
x_41 = l_lean_elaborator_universe_elaborate___closed__1;
x_42 = lean::string_append(x_41, x_40);
lean::dec(x_40);
x_44 = l_lean_elaborator_universe_elaborate___closed__2;
x_45 = lean::string_append(x_42, x_44);
x_46 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_38, x_45, x_1, x_2, x_17);
lean::dec(x_17);
lean::dec(x_38);
return x_46;
}
}
}
}
obj* l_lean_elaborator_universe_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_universe_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_29; 
x_12 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_14 = x_0;
} else {
 lean::inc(x_12);
 lean::dec(x_0);
 x_14 = lean::box(0);
}
lean::inc(x_8);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_8);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::cnstr_get(x_8, 2);
lean::inc(x_18);
lean::dec(x_8);
x_21 = l_lean_name_to__string___closed__1;
x_22 = l_lean_name_to__string__with__sep___main(x_21, x_18);
x_23 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_26 = l_char_has__repr___closed__1;
x_27 = lean::string_append(x_24, x_26);
lean::inc(x_2);
x_29 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_17, x_27, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_17);
if (lean::obj_tag(x_29) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_12);
lean::dec(x_14);
lean::dec(x_2);
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
obj* x_39; obj* x_42; obj* x_44; obj* x_47; 
x_39 = lean::cnstr_get(x_29, 0);
lean::inc(x_39);
lean::dec(x_29);
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
lean::dec(x_39);
x_47 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_12, x_1, x_2, x_44);
if (lean::obj_tag(x_47) == 0)
{
obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_14);
lean::dec(x_42);
x_50 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_52 = x_47;
} else {
 lean::inc(x_50);
 lean::dec(x_47);
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
obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_54 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_56 = x_47;
} else {
 lean::inc(x_54);
 lean::dec(x_47);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 0);
x_59 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_61 = x_54;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_54);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_62 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_62 = x_14;
}
lean::cnstr_set(x_62, 0, x_42);
lean::cnstr_set(x_62, 1, x_57);
if (lean::is_scalar(x_61)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_61;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_59);
if (lean::is_scalar(x_56)) {
 x_64 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_64 = x_56;
}
lean::cnstr_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
obj* x_65; 
x_65 = lean::cnstr_get(x_10, 1);
lean::inc(x_65);
if (lean::obj_tag(x_65) == 0)
{
obj* x_68; obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_8);
x_68 = lean::cnstr_get(x_0, 1);
lean::inc(x_68);
lean::dec(x_0);
x_71 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_release(x_10, 1);
 x_73 = x_10;
} else {
 lean::inc(x_71);
 lean::dec(x_10);
 x_73 = lean::box(0);
}
x_74 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_68, x_1, x_2, x_3);
if (lean::obj_tag(x_74) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_71);
lean::dec(x_73);
x_77 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_79 = x_74;
} else {
 lean::inc(x_77);
 lean::dec(x_74);
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
obj* x_81; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_81 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_83 = x_74;
} else {
 lean::inc(x_81);
 lean::dec(x_74);
 x_83 = lean::box(0);
}
x_84 = lean::cnstr_get(x_81, 0);
x_86 = lean::cnstr_get(x_81, 1);
if (lean::is_exclusive(x_81)) {
 x_88 = x_81;
} else {
 lean::inc(x_84);
 lean::inc(x_86);
 lean::dec(x_81);
 x_88 = lean::box(0);
}
x_89 = lean::box(0);
x_90 = lean_expr_mk_const(x_71, x_89);
if (lean::is_scalar(x_73)) {
 x_91 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_91 = x_73;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_84);
if (lean::is_scalar(x_88)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_88;
}
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_86);
if (lean::is_scalar(x_83)) {
 x_93 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_93 = x_83;
}
lean::cnstr_set(x_93, 0, x_92);
return x_93;
}
}
else
{
obj* x_95; obj* x_96; obj* x_99; obj* x_100; obj* x_101; obj* x_103; 
lean::dec(x_10);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_95 = x_65;
} else {
 lean::dec(x_65);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_0, 1);
lean::inc(x_96);
lean::dec(x_0);
x_99 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_99, 0, x_8);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
x_101 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
lean::inc(x_2);
x_103 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_100, x_101, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_100);
if (lean::obj_tag(x_103) == 0)
{
obj* x_109; obj* x_111; obj* x_112; 
lean::dec(x_2);
lean::dec(x_95);
lean::dec(x_96);
x_109 = lean::cnstr_get(x_103, 0);
if (lean::is_exclusive(x_103)) {
 x_111 = x_103;
} else {
 lean::inc(x_109);
 lean::dec(x_103);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
return x_112;
}
else
{
obj* x_113; obj* x_116; obj* x_118; obj* x_121; 
x_113 = lean::cnstr_get(x_103, 0);
lean::inc(x_113);
lean::dec(x_103);
x_116 = lean::cnstr_get(x_113, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_113, 1);
lean::inc(x_118);
lean::dec(x_113);
x_121 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_96, x_1, x_2, x_118);
if (lean::obj_tag(x_121) == 0)
{
obj* x_124; obj* x_126; obj* x_127; 
lean::dec(x_95);
lean::dec(x_116);
x_124 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 x_126 = x_121;
} else {
 lean::inc(x_124);
 lean::dec(x_121);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
return x_127;
}
else
{
obj* x_128; obj* x_130; obj* x_131; obj* x_133; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_128 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 x_130 = x_121;
} else {
 lean::inc(x_128);
 lean::dec(x_121);
 x_130 = lean::box(0);
}
x_131 = lean::cnstr_get(x_128, 0);
x_133 = lean::cnstr_get(x_128, 1);
if (lean::is_exclusive(x_128)) {
 x_135 = x_128;
} else {
 lean::inc(x_131);
 lean::inc(x_133);
 lean::dec(x_128);
 x_135 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_136 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_136 = x_95;
}
lean::cnstr_set(x_136, 0, x_116);
lean::cnstr_set(x_136, 1, x_131);
if (lean::is_scalar(x_135)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_135;
}
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_133);
if (lean::is_scalar(x_130)) {
 x_138 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_138 = x_130;
}
lean::cnstr_set(x_138, 0, x_137);
return x_138;
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
obj* l_lean_elaborator_attribute_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_13; 
x_4 = l_lean_parser_command_attribute_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
lean::inc(x_2);
x_13 = l_lean_elaborator_attrs__to__pexpr(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
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
obj* x_21; obj* x_24; obj* x_26; obj* x_29; obj* x_32; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = lean::cnstr_get(x_9, 5);
lean::inc(x_29);
lean::inc(x_2);
x_32 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_29, x_1, x_2, x_26);
if (lean::obj_tag(x_32) == 0)
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_24);
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_37 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_39 = x_32;
} else {
 lean::inc(x_37);
 lean::dec(x_32);
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
obj* x_41; obj* x_44; obj* x_46; obj* x_49; uint8 x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_41 = lean::cnstr_get(x_32, 0);
lean::inc(x_41);
lean::dec(x_32);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
lean::dec(x_41);
x_49 = lean::cnstr_get(x_9, 0);
lean::inc(x_49);
lean::dec(x_9);
x_52 = l_option_is__some___main___rarg(x_49);
lean::dec(x_49);
x_54 = l_lean_elaborator_attribute_elaborate___closed__1;
x_55 = l_lean_elaborator_attribute_elaborate___closed__2;
x_56 = l_lean_kvmap_set__bool(x_54, x_55, x_52);
x_57 = l_lean_elaborator_mk__eqns___closed__1;
x_58 = l_lean_expr_mk__capp(x_57, x_44);
x_59 = lean_expr_mk_app(x_24, x_58);
x_60 = lean_expr_mk_mdata(x_56, x_59);
x_61 = l_lean_elaborator_old__elab__command(x_0, x_60, x_1, x_2, x_46);
lean::dec(x_0);
return x_61;
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_attribute_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_attribute_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_lean_elaborator_check_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_14; 
x_4 = l_lean_parser_command_check_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
lean::inc(x_2);
x_14 = l_lean_elaborator_to__pexpr___main(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_0);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_19 = x_14;
} else {
 lean::inc(x_17);
 lean::dec(x_14);
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
obj* x_21; obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
lean::dec(x_14);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_lean_elaborator_check_elaborate___closed__1;
x_30 = lean_expr_mk_mdata(x_29, x_24);
x_31 = l_lean_elaborator_old__elab__command(x_0, x_30, x_1, x_2, x_26);
lean::dec(x_0);
return x_31;
}
}
}
obj* l_lean_elaborator_check_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_check_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_open_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 4);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 5);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_1, 6);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_1, 7);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_list_append___rarg(x_16, x_18);
x_22 = lean::cnstr_get(x_1, 8);
lean::inc(x_22);
lean::dec(x_1);
x_25 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_8);
lean::cnstr_set(x_25, 4, x_10);
lean::cnstr_set(x_25, 5, x_12);
lean::cnstr_set(x_25, 6, x_14);
lean::cnstr_set(x_25, 7, x_21);
lean::cnstr_set(x_25, 8, x_22);
return x_25;
}
}
obj* l_lean_elaborator_open_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_4 = l_lean_parser_command_open_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_open_elaborate___lambda__1), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = l_lean_elaborator_modify__current__scope(x_9, x_1, x_2, x_3);
return x_10;
}
}
obj* l_lean_elaborator_open_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_open_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_lean_elaborator_export_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_get__namespace(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
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
obj* l_lean_elaborator_export_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_export_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_lean_elaborator_init__quot_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_elaborator_init__quot_elaborate___closed__1;
x_5 = l_lean_elaborator_old__elab__command(x_0, x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_elaborator_init__quot_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_init__quot_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_set__option_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_19; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 4);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 5);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_1, 6);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_1, 7);
lean::inc(x_16);
lean::dec(x_1);
x_19 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_19, 0, x_2);
lean::cnstr_set(x_19, 1, x_4);
lean::cnstr_set(x_19, 2, x_6);
lean::cnstr_set(x_19, 3, x_8);
lean::cnstr_set(x_19, 4, x_10);
lean::cnstr_set(x_19, 5, x_12);
lean::cnstr_set(x_19, 6, x_14);
lean::cnstr_set(x_19, 7, x_16);
lean::cnstr_set(x_19, 8, x_0);
return x_19;
}
}
obj* l_lean_elaborator_set__option_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_2);
x_5 = l_lean_elaborator_current__scope(x_1, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
lean::dec(x_2);
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
obj* x_12; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_24; obj* x_25; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = l_lean_parser_command_set__option_has__view;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
lean::dec(x_20);
x_24 = lean::apply_1(x_21, x_0);
x_25 = lean::cnstr_get(x_24, 2);
lean::inc(x_25);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_27; 
x_27 = lean::cnstr_get(x_25, 0);
lean::inc(x_27);
lean::dec(x_25);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_34; obj* x_37; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_27);
x_31 = lean::cnstr_get(x_24, 1);
lean::inc(x_31);
lean::dec(x_24);
x_34 = lean::cnstr_get(x_31, 2);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::cnstr_get(x_15, 8);
lean::inc(x_37);
lean::dec(x_15);
x_40 = 1;
x_41 = l_lean_kvmap_set__bool(x_37, x_34, x_40);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_set__option_elaborate___lambda__1), 2, 1);
lean::closure_set(x_42, 0, x_41);
x_43 = l_lean_elaborator_modify__current__scope(x_42, x_1, x_2, x_17);
return x_43;
}
else
{
obj* x_45; obj* x_48; obj* x_51; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_27);
x_45 = lean::cnstr_get(x_24, 1);
lean::inc(x_45);
lean::dec(x_24);
x_48 = lean::cnstr_get(x_45, 2);
lean::inc(x_48);
lean::dec(x_45);
x_51 = lean::cnstr_get(x_15, 8);
lean::inc(x_51);
lean::dec(x_15);
x_54 = 0;
x_55 = l_lean_kvmap_set__bool(x_51, x_48, x_54);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_set__option_elaborate___lambda__1), 2, 1);
lean::closure_set(x_56, 0, x_55);
x_57 = l_lean_elaborator_modify__current__scope(x_56, x_1, x_2, x_17);
return x_57;
}
}
case 1:
{
obj* x_58; obj* x_61; obj* x_64; obj* x_67; obj* x_70; 
x_58 = lean::cnstr_get(x_24, 1);
lean::inc(x_58);
lean::dec(x_24);
x_61 = lean::cnstr_get(x_58, 2);
lean::inc(x_61);
lean::dec(x_58);
x_64 = lean::cnstr_get(x_15, 8);
lean::inc(x_64);
lean::dec(x_15);
x_67 = lean::cnstr_get(x_25, 0);
lean::inc(x_67);
lean::dec(x_25);
x_70 = l_lean_parser_string__lit_view_value(x_67);
if (lean::obj_tag(x_70) == 0)
{
obj* x_72; obj* x_73; 
lean::dec(x_61);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_set__option_elaborate___lambda__1), 2, 1);
lean::closure_set(x_72, 0, x_64);
x_73 = l_lean_elaborator_modify__current__scope(x_72, x_1, x_2, x_17);
return x_73;
}
else
{
obj* x_74; obj* x_77; obj* x_78; obj* x_79; 
x_74 = lean::cnstr_get(x_70, 0);
lean::inc(x_74);
lean::dec(x_70);
x_77 = l_lean_kvmap_set__string(x_64, x_61, x_74);
x_78 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_set__option_elaborate___lambda__1), 2, 1);
lean::closure_set(x_78, 0, x_77);
x_79 = l_lean_elaborator_modify__current__scope(x_78, x_1, x_2, x_17);
return x_79;
}
}
default:
{
obj* x_80; obj* x_83; obj* x_86; obj* x_89; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_80 = lean::cnstr_get(x_24, 1);
lean::inc(x_80);
lean::dec(x_24);
x_83 = lean::cnstr_get(x_80, 2);
lean::inc(x_83);
lean::dec(x_80);
x_86 = lean::cnstr_get(x_15, 8);
lean::inc(x_86);
lean::dec(x_15);
x_89 = lean::cnstr_get(x_25, 0);
lean::inc(x_89);
lean::dec(x_25);
x_92 = l_lean_parser_number_view_to__nat___main(x_89);
x_93 = l_lean_kvmap_set__nat(x_86, x_83, x_92);
x_94 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_set__option_elaborate___lambda__1), 2, 1);
lean::closure_set(x_94, 0, x_93);
x_95 = l_lean_elaborator_modify__current__scope(x_94, x_1, x_2, x_17);
return x_95;
}
}
}
}
}
obj* l_lean_elaborator_set__option_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_set__option_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_1);
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
obj* x_9; obj* x_11; obj* x_16; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_1);
x_16 = lean::apply_3(x_1, x_9, x_2, x_3);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_2);
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
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_0 = x_11;
x_3 = x_27;
goto _start;
}
}
}
}
obj* _init_l_lean_elaborator_no__kind_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("no_kind.elaborate: unreachable");
return x_0;
}
}
obj* l_lean_elaborator_no__kind_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_0);
x_5 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_0);
x_7 = l_lean_elaborator_no__kind_elaborate___closed__1;
x_8 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_6, x_7, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_6);
return x_8;
}
else
{
obj* x_13; obj* x_16; obj* x_19; 
lean::dec(x_0);
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
lean::dec(x_5);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__1(x_16, x_1, x_2, x_3);
return x_19;
}
}
}
obj* _init_l_lean_elaborator_end_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid 'end', there is no open scope to end");
return x_0;
}
}
obj* _init_l_lean_elaborator_end_elaborate___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
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
return x_7;
}
}
obj* _init_l_lean_elaborator_end_elaborate___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid end of ");
return x_0;
}
}
obj* _init_l_lean_elaborator_end_elaborate___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", expected name '");
return x_0;
}
}
obj* l_lean_elaborator_end_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_3, 4);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_0);
x_7 = l_lean_elaborator_end_elaborate___closed__1;
x_8 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_6, x_7, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_6);
return x_8;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_4);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_0);
x_15 = l_lean_elaborator_end_elaborate___closed__1;
x_16 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_14, x_15, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_14);
return x_16;
}
else
{
obj* x_19; obj* x_22; obj* x_23; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_34; obj* x_35; uint8 x_37; 
x_19 = lean::cnstr_get(x_4, 0);
lean::inc(x_19);
lean::dec(x_4);
x_22 = l_lean_parser_command_end_has__view;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
lean::inc(x_0);
x_27 = lean::apply_1(x_23, x_0);
x_28 = lean::cnstr_get(x_27, 1);
lean::inc(x_28);
lean::dec(x_27);
x_31 = l_lean_elaborator_end_elaborate___closed__2;
x_32 = l_option_get__or__else___main___rarg(x_28, x_31);
lean::dec(x_28);
x_34 = l_lean_elaborator_mangle__ident(x_32);
x_35 = lean::cnstr_get(x_19, 1);
lean::inc(x_35);
x_37 = lean_name_dec_eq(x_34, x_35);
lean::dec(x_34);
if (x_37 == 0)
{
obj* x_39; obj* x_40; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_55; 
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_0);
x_40 = lean::cnstr_get(x_19, 0);
lean::inc(x_40);
lean::dec(x_19);
x_43 = l_lean_elaborator_end_elaborate___closed__3;
x_44 = lean::string_append(x_43, x_40);
lean::dec(x_40);
x_46 = l_lean_elaborator_end_elaborate___closed__4;
x_47 = lean::string_append(x_44, x_46);
x_48 = l_lean_name_to__string___closed__1;
x_49 = l_lean_name_to__string__with__sep___main(x_48, x_35);
x_50 = lean::string_append(x_47, x_49);
lean::dec(x_49);
x_52 = l_char_has__repr___closed__1;
x_53 = lean::string_append(x_50, x_52);
lean::inc(x_2);
x_55 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_39, x_53, x_1, x_2, x_3);
lean::dec(x_39);
if (lean::obj_tag(x_55) == 0)
{
obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_2);
x_60 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 x_62 = x_55;
} else {
 lean::inc(x_60);
 lean::dec(x_55);
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
obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_87; 
lean::dec(x_55);
x_65 = lean::cnstr_get(x_3, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_3, 1);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_3, 2);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_3, 3);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_3, 5);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_3, 6);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_3, 7);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_3, 8);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_3, 9);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_3, 10);
lean::inc(x_83);
lean::dec(x_3);
x_86 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_86, 0, x_65);
lean::cnstr_set(x_86, 1, x_67);
lean::cnstr_set(x_86, 2, x_69);
lean::cnstr_set(x_86, 3, x_71);
lean::cnstr_set(x_86, 4, x_11);
lean::cnstr_set(x_86, 5, x_73);
lean::cnstr_set(x_86, 6, x_75);
lean::cnstr_set(x_86, 7, x_77);
lean::cnstr_set(x_86, 8, x_79);
lean::cnstr_set(x_86, 9, x_81);
lean::cnstr_set(x_86, 10, x_83);
x_87 = l_lean_elaborator_update__parser__config(x_1, x_2, x_86);
return x_87;
}
}
else
{
obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_112; obj* x_113; 
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_35);
x_91 = lean::cnstr_get(x_3, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_3, 1);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_3, 2);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_3, 3);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_3, 5);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_3, 6);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_3, 7);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_3, 8);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_3, 9);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_3, 10);
lean::inc(x_109);
lean::dec(x_3);
x_112 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_112, 0, x_91);
lean::cnstr_set(x_112, 1, x_93);
lean::cnstr_set(x_112, 2, x_95);
lean::cnstr_set(x_112, 3, x_97);
lean::cnstr_set(x_112, 4, x_11);
lean::cnstr_set(x_112, 5, x_99);
lean::cnstr_set(x_112, 6, x_101);
lean::cnstr_set(x_112, 7, x_103);
lean::cnstr_set(x_112, 8, x_105);
lean::cnstr_set(x_112, 9, x_107);
lean::cnstr_set(x_112, 10, x_109);
x_113 = l_lean_elaborator_update__parser__config(x_1, x_2, x_112);
return x_113;
}
}
}
}
}
obj* l_lean_elaborator_end_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_end_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_lean_elaborator_section_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("section");
return x_0;
}
}
obj* l_lean_elaborator_section_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_current__scope(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_53; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_17 = x_10;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
x_18 = l_lean_parser_command_section_has__view;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_0);
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_26 = l_lean_elaborator_end_elaborate___closed__2;
x_27 = l_option_get__or__else___main___rarg(x_23, x_26);
lean::dec(x_23);
x_29 = l_lean_elaborator_mangle__ident(x_27);
x_30 = lean::cnstr_get(x_15, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_15, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_15, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_15, 3);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_13, 2);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_13, 3);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_13, 4);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_13, 5);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_13, 6);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_13, 7);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_13, 8);
lean::inc(x_50);
lean::dec(x_13);
x_53 = l_lean_elaborator_section_elaborate___closed__1;
x_54 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_29);
lean::cnstr_set(x_54, 2, x_38);
lean::cnstr_set(x_54, 3, x_40);
lean::cnstr_set(x_54, 4, x_42);
lean::cnstr_set(x_54, 5, x_44);
lean::cnstr_set(x_54, 6, x_46);
lean::cnstr_set(x_54, 7, x_48);
lean::cnstr_set(x_54, 8, x_50);
x_55 = lean::cnstr_get(x_15, 4);
lean::inc(x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set(x_57, 1, x_55);
x_58 = lean::cnstr_get(x_15, 5);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_15, 6);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_15, 7);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_15, 8);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_15, 9);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_15, 10);
lean::inc(x_68);
lean::dec(x_15);
x_71 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_71, 0, x_30);
lean::cnstr_set(x_71, 1, x_32);
lean::cnstr_set(x_71, 2, x_34);
lean::cnstr_set(x_71, 3, x_36);
lean::cnstr_set(x_71, 4, x_57);
lean::cnstr_set(x_71, 5, x_58);
lean::cnstr_set(x_71, 6, x_60);
lean::cnstr_set(x_71, 7, x_62);
lean::cnstr_set(x_71, 8, x_64);
lean::cnstr_set(x_71, 9, x_66);
lean::cnstr_set(x_71, 10, x_68);
x_72 = lean::box(0);
if (lean::is_scalar(x_17)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_17;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_71);
if (lean::is_scalar(x_12)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_12;
}
lean::cnstr_set(x_74, 0, x_73);
return x_74;
}
}
}
obj* l_lean_elaborator_section_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_section_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_lean_elaborator_namespace_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("namespace");
return x_0;
}
}
obj* l_lean_elaborator_namespace_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_2);
x_5 = l_lean_elaborator_current__scope(x_1, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
lean::dec(x_2);
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
obj* x_12; obj* x_15; obj* x_17; obj* x_20; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = l_lean_elaborator_get__namespace(x_1, x_2, x_17);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_0);
lean::dec(x_15);
x_23 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_25 = x_20;
} else {
 lean::inc(x_23);
 lean::dec(x_20);
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
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_39; obj* x_40; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_27 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_29 = x_20;
} else {
 lean::inc(x_27);
 lean::dec(x_20);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 0);
x_32 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_34 = x_27;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_27);
 x_34 = lean::box(0);
}
x_35 = l_lean_parser_command_namespace_has__view;
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
lean::dec(x_35);
x_39 = lean::apply_1(x_36, x_0);
x_40 = lean::cnstr_get(x_39, 1);
lean::inc(x_40);
lean::dec(x_39);
x_43 = l_lean_elaborator_mangle__ident(x_40);
x_44 = lean::cnstr_get(x_15, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_15, 3);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_15, 4);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_15, 5);
lean::inc(x_50);
lean::inc(x_43);
x_53 = l_lean_name_append___main(x_30, x_43);
lean::dec(x_30);
x_55 = lean::cnstr_get(x_15, 6);
lean::inc(x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set(x_57, 1, x_55);
x_58 = lean::cnstr_get(x_15, 7);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_15, 8);
lean::inc(x_60);
lean::dec(x_15);
x_63 = l_lean_elaborator_namespace_elaborate___closed__1;
x_64 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_43);
lean::cnstr_set(x_64, 2, x_44);
lean::cnstr_set(x_64, 3, x_46);
lean::cnstr_set(x_64, 4, x_48);
lean::cnstr_set(x_64, 5, x_50);
lean::cnstr_set(x_64, 6, x_57);
lean::cnstr_set(x_64, 7, x_58);
lean::cnstr_set(x_64, 8, x_60);
x_65 = lean::cnstr_get(x_32, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_32, 1);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_32, 2);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_32, 3);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_32, 4);
lean::inc(x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_64);
lean::cnstr_set(x_75, 1, x_73);
x_76 = lean::cnstr_get(x_32, 5);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_32, 6);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_32, 7);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_32, 8);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_32, 9);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_32, 10);
lean::inc(x_86);
lean::dec(x_32);
x_89 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_89, 0, x_65);
lean::cnstr_set(x_89, 1, x_67);
lean::cnstr_set(x_89, 2, x_69);
lean::cnstr_set(x_89, 3, x_71);
lean::cnstr_set(x_89, 4, x_75);
lean::cnstr_set(x_89, 5, x_76);
lean::cnstr_set(x_89, 6, x_78);
lean::cnstr_set(x_89, 7, x_80);
lean::cnstr_set(x_89, 8, x_82);
lean::cnstr_set(x_89, 9, x_84);
lean::cnstr_set(x_89, 10, x_86);
x_90 = lean::box(0);
if (lean::is_scalar(x_34)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_34;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
if (lean::is_scalar(x_29)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_29;
}
lean::cnstr_set(x_92, 0, x_91);
return x_92;
}
}
}
}
obj* l_lean_elaborator_namespace_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_namespace_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_lean_elaborator_eoi_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid end of input, expected 'end'");
return x_0;
}
}
obj* l_lean_elaborator_eoi_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; uint8 x_10; 
x_4 = lean::cnstr_get(x_3, 4);
lean::inc(x_4);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_list_length__aux___main___rarg(x_4, x_6);
lean::dec(x_4);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_dec_lt(x_9, x_7);
lean::dec(x_7);
if (x_10 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_0);
lean::dec(x_2);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_3);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_0);
x_18 = l_lean_elaborator_eoi_elaborate___closed__1;
x_19 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_17, x_18, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_17);
return x_19;
}
}
}
obj* l_lean_elaborator_eoi_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_eoi_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___rarg), 3, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_lean_name_quick__lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
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
x_37 = l_lean_name_quick__lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_name_quick__lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_rbnode_is__red___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___rarg(x_34, x_1, x_2);
x_51 = l_rbnode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_rbnode_is__red___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___rarg(x_28, x_1, x_2);
x_60 = l_rbnode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___rarg), 3, 0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_14; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_14 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___rarg(x_2, x_9, x_11);
x_1 = x_0;
x_2 = x_14;
x_3 = x_6;
goto _start;
}
}
}
obj* _init_l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_0 = l_lean_parser_module_header;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_module_header_elaborate___boxed), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = l_lean_parser_command_notation;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_notation_elaborate___boxed), 4, 0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_lean_parser_command_reserve__notation;
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_reserve__notation_elaborate___boxed), 4, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_lean_parser_command_universe;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_universe_elaborate___boxed), 4, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_lean_parser_no__kind;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_no__kind_elaborate), 4, 0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_lean_parser_command_end;
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_end_elaborate___boxed), 4, 0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_command_section;
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_section_elaborate___boxed), 4, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_parser_command_namespace;
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_namespace_elaborate___boxed), 4, 0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_lean_parser_command_variables;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_variables_elaborate___boxed), 4, 0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_lean_parser_command_include;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_include_elaborate___boxed), 4, 0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_command_declaration;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_declaration_elaborate), 4, 0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_lean_parser_command_attribute;
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_attribute_elaborate___boxed), 4, 0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_lean_parser_command_open;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_open_elaborate___boxed), 4, 0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_lean_parser_command_export;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_export_elaborate___boxed), 4, 0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_lean_parser_command_check;
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_check_elaborate___boxed), 4, 0);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_lean_parser_command_init__quot;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_init__quot_elaborate___boxed), 4, 0);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_lean_parser_command_set__option;
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_set__option_elaborate___boxed), 4, 0);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
x_51 = l_lean_parser_module_eoi;
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_eoi_elaborate___boxed), 4, 0);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::box(0);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_50);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_47);
lean::cnstr_set(x_57, 1, x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_44);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_41);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_38);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_35);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_32);
lean::cnstr_set(x_62, 1, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_29);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_26);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_23);
lean::cnstr_set(x_65, 1, x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_20);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_17);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_14);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_11);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_8);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_5);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_2);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::box(0);
x_74 = lean::box(0);
x_75 = l_list_foldl___main___at_lean_elaborator_elaborators___spec__6(x_73, lean::box(0), x_74, x_72);
return x_75;
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
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_foldl___main___at_lean_elaborator_elaborators___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
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
uint8 l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_5, 2);
x_7 = lean_name_dec_eq(x_6, x_0);
if (x_7 == 0)
{
x_1 = x_4;
goto _start;
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
uint8 l_lean_elaborator_is__open__namespace___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::box(0);
x_3 = lean_name_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_0, 6);
x_5 = l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_0, 7);
x_7 = l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(x_1, x_6);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = 1;
return x_11;
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
uint8 x_2; obj* x_3; 
x_2 = l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
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
uint8 l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_3, 2);
x_6 = lean_name_dec_eq(x_0, x_5);
if (x_6 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
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
obj* x_23; uint8 x_26; 
x_23 = lean::cnstr_get(x_13, 2);
lean::inc(x_23);
lean::dec(x_13);
x_26 = l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(x_0, x_23);
lean::dec(x_23);
if (x_26 == 0)
{
obj* x_31; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_15);
x_31 = lean::box(0);
return x_31;
}
else
{
obj* x_32; obj* x_35; obj* x_38; obj* x_40; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
lean::dec(x_1);
x_35 = lean::cnstr_get(x_32, 2);
lean::inc(x_35);
lean::dec(x_32);
x_38 = l_lean_name_append___main(x_35, x_0);
lean::dec(x_35);
if (lean::is_scalar(x_15)) {
 x_40 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_40 = x_15;
}
lean::cnstr_set(x_40, 0, x_38);
return x_40;
}
}
else
{
obj* x_42; obj* x_45; obj* x_48; obj* x_50; 
lean::dec(x_13);
x_42 = lean::cnstr_get(x_1, 0);
lean::inc(x_42);
lean::dec(x_1);
x_45 = lean::cnstr_get(x_42, 2);
lean::inc(x_45);
lean::dec(x_42);
x_48 = l_lean_name_append___main(x_45, x_0);
lean::dec(x_45);
if (lean::is_scalar(x_15)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_15;
}
lean::cnstr_set(x_50, 0, x_48);
return x_50;
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; uint8 x_12; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_1, 8);
lean::inc(x_0);
x_11 = l_lean_name_append___main(x_4, x_0);
x_12 = lean_environment_contains(x_9, x_11);
lean::dec(x_11);
if (x_12 == 0)
{
lean::dec(x_8);
lean::dec(x_4);
x_2 = x_6;
goto _start;
}
else
{
obj* x_17; obj* x_18; 
x_17 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(x_0, x_1, x_6);
if (lean::is_scalar(x_8)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_8;
}
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_8; 
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
x_8 = lean_environment_contains(x_1, x_3);
if (x_8 == 0)
{
lean::dec(x_7);
lean::dec(x_3);
x_2 = x_5;
goto _start;
}
else
{
obj* x_12; obj* x_13; 
x_12 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(x_0, x_1, x_5);
if (lean::is_scalar(x_7)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_7;
}
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
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
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_8; 
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
x_8 = lean_environment_contains(x_1, x_3);
if (x_8 == 0)
{
lean::dec(x_7);
lean::dec(x_3);
x_2 = x_5;
goto _start;
}
else
{
obj* x_12; obj* x_13; 
x_12 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(x_0, x_1, x_5);
if (lean::is_scalar(x_7)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_7;
}
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
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
obj* l_lean_elaborator_resolve__context___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_3);
x_5 = l_lean_elaborator_current__scope(x_1, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_3);
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
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
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
x_20 = lean::cnstr_get(x_15, 4);
lean::inc(x_20);
x_22 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_20, x_0);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_26; 
x_23 = lean::cnstr_get(x_15, 6);
lean::inc(x_23);
lean::inc(x_0);
x_26 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(x_0, x_3, x_23);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; obj* x_30; obj* x_31; uint8 x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
x_27 = l_lean_elaborator_resolve__context___main___closed__1;
x_28 = lean::box(0);
lean::inc(x_0);
x_30 = l_lean_name_replace__prefix___main(x_0, x_27, x_28);
x_31 = lean::cnstr_get(x_3, 8);
lean::inc(x_31);
x_33 = lean_environment_contains(x_31, x_30);
lean::inc(x_0);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_match__open__spec), 2, 1);
lean::closure_set(x_35, 0, x_0);
x_36 = lean::cnstr_get(x_15, 7);
lean::inc(x_36);
x_38 = l_list_filter__map___main___rarg(x_35, x_36);
x_39 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(x_3, x_31, x_38);
x_40 = lean::cnstr_get(x_3, 3);
lean::inc(x_40);
x_42 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(x_15, x_40);
lean::dec(x_15);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_resolve__context___main___lambda__1), 2, 1);
lean::closure_set(x_44, 0, x_0);
x_45 = l_list_filter__map___main___rarg(x_44, x_42);
x_46 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(x_3, x_31, x_45);
lean::dec(x_31);
lean::dec(x_3);
if (x_33 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_30);
x_50 = l_list_append___rarg(x_26, x_39);
x_51 = l_list_append___rarg(x_50, x_46);
if (lean::is_scalar(x_19)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_19;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_14;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_30);
lean::cnstr_set(x_54, 1, x_26);
x_55 = l_list_append___rarg(x_54, x_39);
x_56 = l_list_append___rarg(x_55, x_46);
if (lean::is_scalar(x_19)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_19;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_14;
}
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
}
else
{
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_3);
lean::dec(x_15);
x_61 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 1);
 x_63 = x_26;
} else {
 lean::inc(x_61);
 lean::dec(x_26);
 x_63 = lean::box(0);
}
x_64 = l_lean_name_append___main(x_61, x_0);
lean::dec(x_61);
x_66 = lean::box(0);
if (lean::is_scalar(x_63)) {
 x_67 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_67 = x_63;
}
lean::cnstr_set(x_67, 0, x_64);
lean::cnstr_set(x_67, 1, x_66);
if (lean::is_scalar(x_19)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_19;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_14;
}
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
else
{
obj* x_74; obj* x_77; obj* x_79; obj* x_80; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_15);
lean::dec(x_19);
x_74 = lean::cnstr_get(x_22, 0);
lean::inc(x_74);
lean::dec(x_22);
x_77 = lean::cnstr_get(x_74, 1);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 x_79 = x_74;
} else {
 lean::inc(x_77);
 lean::dec(x_74);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
lean::dec(x_77);
x_83 = lean::box(0);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set(x_84, 1, x_83);
if (lean::is_scalar(x_79)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_79;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_86 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_86 = x_14;
}
lean::cnstr_set(x_86, 0, x_85);
return x_86;
}
}
}
}
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
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
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_elaborator_resolve__context___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_resolve__context___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_resolve__context(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_resolve__context___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_resolve__context___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_resolve__context(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
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
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_lean_elaborator_preresolve___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
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
x_30 = l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
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
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_lean_elaborator_preresolve___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_6 = x_0;
} else {
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
lean::inc(x_4);
x_8 = l_lean_elaborator_mangle__ident(x_4);
x_9 = l_lean_elaborator_resolve__context___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; obj* x_14; obj* x_15; 
lean::dec(x_6);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_14 = x_9;
} else {
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
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
obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_16 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_18 = x_9;
} else {
 lean::inc(x_16);
 lean::dec(x_9);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_16, 0);
x_21 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_23 = x_16;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_16);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_4, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_4, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_4, 2);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_4, 3);
lean::inc(x_30);
x_32 = l_list_append___rarg(x_19, x_30);
x_33 = lean::cnstr_get(x_4, 4);
lean::inc(x_33);
lean::dec(x_4);
x_36 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_36, 0, x_24);
lean::cnstr_set(x_36, 1, x_26);
lean::cnstr_set(x_36, 2, x_28);
lean::cnstr_set(x_36, 3, x_32);
lean::cnstr_set(x_36, 4, x_33);
if (lean::is_scalar(x_6)) {
 x_37 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_37 = x_6;
}
lean::cnstr_set(x_37, 0, x_36);
if (lean::is_scalar(x_23)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_23;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_21);
if (lean::is_scalar(x_18)) {
 x_39 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_39 = x_18;
}
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
}
case 2:
{
obj* x_40; obj* x_42; obj* x_43; obj* x_45; 
x_40 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
x_45 = l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(x_43, x_1, x_2, x_3);
if (lean::obj_tag(x_45) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_40);
lean::dec(x_42);
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
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
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
x_60 = lean::cnstr_get(x_40, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_40, 2);
lean::inc(x_62);
lean::dec(x_40);
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_60);
lean::cnstr_set(x_65, 1, x_55);
lean::cnstr_set(x_65, 2, x_62);
if (lean::is_scalar(x_42)) {
 x_66 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_66 = x_42;
}
lean::cnstr_set(x_66, 0, x_65);
if (lean::is_scalar(x_59)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_59;
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
default:
{
obj* x_70; obj* x_71; 
lean::dec(x_2);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_0);
lean::cnstr_set(x_70, 1, x_3);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_preresolve___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_preresolve___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_elaborator_preresolve(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_preresolve___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_preresolve___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_preresolve(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__1() {
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
obj* _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__2() {
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
obj* _init_l_lean_elaborator_mk__state___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("MODULE");
return x_0;
}
}
obj* _init_l_lean_elaborator_mk__state___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("MODULE");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_mk__state___closed__3() {
_start:
{
obj* x_0; 
x_0 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__1;
return x_0;
}
}
obj* _init_l_lean_elaborator_mk__state___closed__4() {
_start:
{
obj* x_0; 
x_0 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__2;
return x_0;
}
}
obj* _init_l_lean_elaborator_mk__state___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean_environment_mk_empty(x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_mk__state___closed__6() {
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
obj* l_lean_elaborator_mk__state(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_2 = lean::box(0);
x_3 = lean::box(0);
x_4 = l_lean_elaborator_mk__state___closed__1;
x_5 = l_lean_elaborator_mk__state___closed__2;
x_6 = l_lean_elaborator_mk__state___closed__3;
x_7 = l_lean_elaborator_mk__state___closed__4;
x_8 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set(x_8, 2, x_2);
lean::cnstr_set(x_8, 3, x_6);
lean::cnstr_set(x_8, 4, x_7);
lean::cnstr_set(x_8, 5, x_3);
lean::cnstr_set(x_8, 6, x_2);
lean::cnstr_set(x_8, 7, x_2);
lean::cnstr_set(x_8, 8, x_1);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_2);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_lean_expander_builtin__transformers;
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::mk_nat_obj(0u);
x_18 = l_lean_message__log_empty;
x_19 = l_lean_elaborator_mk__state___closed__5;
x_20 = l_lean_elaborator_mk__state___closed__6;
x_21 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_21, 0, x_2);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_2);
lean::cnstr_set(x_21, 4, x_9);
lean::cnstr_set(x_21, 5, x_18);
lean::cnstr_set(x_21, 6, x_10);
lean::cnstr_set(x_21, 7, x_16);
lean::cnstr_set(x_21, 8, x_19);
lean::cnstr_set(x_21, 9, x_20);
lean::cnstr_set(x_21, 10, x_17);
return x_21;
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
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_9; obj* x_12; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = l_lean_expander_error___rarg___lambda__1___closed__1;
x_14 = l_lean_file__map_to__position(x_9, x_13);
x_15 = 2;
x_16 = l_string_iterator_extract___main___closed__1;
x_17 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_17, 0, x_7);
lean::cnstr_set(x_17, 1, x_14);
lean::cnstr_set(x_17, 2, x_12);
lean::cnstr_set(x_17, 3, x_16);
lean::cnstr_set(x_17, 4, x_1);
lean::cnstr_set_scalar(x_17, sizeof(void*)*5, x_15);
x_18 = x_17;
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_20 = lean::cnstr_get(x_0, 0);
x_21 = l_lean_parser_syntax_get__pos(x_20);
x_22 = lean::mk_nat_obj(0u);
x_23 = l_option_get__or__else___main___rarg(x_21, x_22);
lean::dec(x_21);
x_25 = l_lean_file__map_to__position(x_9, x_23);
x_26 = 2;
x_27 = l_string_iterator_extract___main___closed__1;
x_28 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_28, 0, x_7);
lean::cnstr_set(x_28, 1, x_25);
lean::cnstr_set(x_28, 2, x_12);
lean::cnstr_set(x_28, 3, x_27);
lean::cnstr_set(x_28, 4, x_1);
lean::cnstr_set_scalar(x_28, sizeof(void*)*5, x_26);
x_29 = x_28;
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
}
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_process__command___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = l_lean_expander_error___rarg___lambda__1___closed__1;
x_15 = l_lean_file__map_to__position(x_10, x_14);
x_16 = 2;
x_17 = l_string_iterator_extract___main___closed__1;
x_18 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_18, 0, x_8);
lean::cnstr_set(x_18, 1, x_15);
lean::cnstr_set(x_18, 2, x_13);
lean::cnstr_set(x_18, 3, x_17);
lean::cnstr_set(x_18, 4, x_1);
lean::cnstr_set_scalar(x_18, sizeof(void*)*5, x_16);
x_19 = x_18;
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_21 = lean::cnstr_get(x_0, 0);
x_22 = l_lean_parser_syntax_get__pos(x_21);
x_23 = lean::mk_nat_obj(0u);
x_24 = l_option_get__or__else___main___rarg(x_22, x_23);
lean::dec(x_22);
x_26 = l_lean_file__map_to__position(x_10, x_24);
x_27 = 2;
x_28 = l_string_iterator_extract___main___closed__1;
x_29 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set(x_29, 4, x_1);
lean::cnstr_set_scalar(x_29, sizeof(void*)*5, x_27);
x_30 = x_29;
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
}
}
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_process__command___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_rbnode_find___main___at_lean_name__map_contains___spec__2(x_2, lean::box(0), lean::box(0), x_0, x_1);
return x_3;
}
}
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_process__command___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l___private_init_lean_parser_rec_1__run__aux___main___rarg(x_0, x_1, x_2, x_3);
x_7 = lean::apply_2(x_6, x_4, x_5);
return x_7;
}
}
obj* l_lean_parser_rec__t_run___at_lean_elaborator_process__command___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_process__command___spec__5___boxed), 6, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_2);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::apply_3(x_0, x_6, x_4, x_5);
return x_7;
}
}
obj* _init_l_lean_elaborator_process__command___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborator.run: recursion depth exceeded");
return x_0;
}
}
obj* l_lean_elaborator_process__command___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_0);
x_5 = l_lean_elaborator_process__command___lambda__1___closed__1;
x_6 = l_lean_expander_error___at_lean_elaborator_process__command___spec__1___rarg(x_4, x_5, x_2, x_3);
lean::dec(x_4);
return x_6;
}
}
obj* _init_l_lean_elaborator_process__command___lambda__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("not a command: ");
return x_0;
}
}
obj* _init_l_lean_elaborator_process__command___lambda__2___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown command: ");
return x_0;
}
}
obj* l_lean_elaborator_process__command___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_0);
x_5 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_0);
x_8 = l_lean_parser_syntax_to__format___main(x_0);
x_9 = lean::mk_nat_obj(80u);
x_10 = l_lean_format_pretty(x_8, x_9);
x_11 = l_lean_elaborator_process__command___lambda__2___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg(x_7, x_12, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_7);
return x_14;
}
else
{
obj* x_18; obj* x_20; obj* x_21; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_20 = x_5;
} else {
 lean::inc(x_18);
 lean::dec(x_5);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_lean_elaborator_elaborators;
x_25 = l_rbmap_find___main___at_lean_elaborator_process__command___spec__3(x_24, x_21);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; 
if (lean::is_scalar(x_20)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_20;
}
lean::cnstr_set(x_26, 0, x_0);
x_27 = l_lean_name_to__string___closed__1;
x_28 = l_lean_name_to__string__with__sep___main(x_27, x_21);
x_29 = l_lean_elaborator_process__command___lambda__2___closed__2;
x_30 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_32 = l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg(x_26, x_30, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_26);
return x_32;
}
else
{
obj* x_38; obj* x_42; 
lean::dec(x_20);
lean::dec(x_21);
x_38 = lean::cnstr_get(x_25, 0);
lean::inc(x_38);
lean::dec(x_25);
lean::inc(x_2);
x_42 = l_lean_elaborator_preresolve___main(x_0, x_1, x_2, x_3);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_38);
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
obj* x_50; obj* x_53; obj* x_55; obj* x_58; 
x_50 = lean::cnstr_get(x_42, 0);
lean::inc(x_50);
lean::dec(x_42);
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
lean::dec(x_50);
x_58 = lean::apply_4(x_38, x_53, x_1, x_2, x_55);
return x_58;
}
}
}
}
}
obj* _init_l_lean_elaborator_process__command___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_process__command___lambda__2), 4, 0);
return x_0;
}
}
obj* l_lean_elaborator_process__command(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 4);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 6);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 7);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 8);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 9);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 10);
lean::inc(x_21);
lean::dec(x_1);
x_24 = l_lean_message__log_empty;
lean::inc(x_21);
lean::inc(x_19);
lean::inc(x_17);
lean::inc(x_15);
lean::inc(x_13);
lean::inc(x_11);
lean::inc(x_9);
lean::inc(x_7);
lean::inc(x_5);
lean::inc(x_3);
x_35 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_35, 0, x_3);
lean::cnstr_set(x_35, 1, x_5);
lean::cnstr_set(x_35, 2, x_7);
lean::cnstr_set(x_35, 3, x_9);
lean::cnstr_set(x_35, 4, x_11);
lean::cnstr_set(x_35, 5, x_24);
lean::cnstr_set(x_35, 6, x_13);
lean::cnstr_set(x_35, 7, x_15);
lean::cnstr_set(x_35, 8, x_17);
lean::cnstr_set(x_35, 9, x_19);
lean::cnstr_set(x_35, 10, x_21);
lean::inc(x_2);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_command_elaborate), 4, 1);
lean::closure_set(x_37, 0, x_2);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_process__command___lambda__1___boxed), 4, 1);
lean::closure_set(x_38, 0, x_2);
x_39 = l_lean_elaborator_process__command___closed__1;
x_40 = l_lean_elaborator_max__recursion;
x_41 = l_lean_parser_rec__t_run___at_lean_elaborator_process__command___spec__4(x_37, x_38, x_39, x_40, x_0, x_35);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_45; obj* x_46; 
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
lean::dec(x_41);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set(x_45, 1, x_24);
x_46 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_46, 0, x_3);
lean::cnstr_set(x_46, 1, x_5);
lean::cnstr_set(x_46, 2, x_7);
lean::cnstr_set(x_46, 3, x_9);
lean::cnstr_set(x_46, 4, x_11);
lean::cnstr_set(x_46, 5, x_45);
lean::cnstr_set(x_46, 6, x_13);
lean::cnstr_set(x_46, 7, x_15);
lean::cnstr_set(x_46, 8, x_17);
lean::cnstr_set(x_46, 9, x_19);
lean::cnstr_set(x_46, 10, x_21);
return x_46;
}
else
{
obj* x_57; obj* x_60; 
lean::dec(x_7);
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_13);
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_21);
x_57 = lean::cnstr_get(x_41, 0);
lean::inc(x_57);
lean::dec(x_41);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
return x_60;
}
}
}
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_expander_error___at_lean_elaborator_process__command___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_error___at_lean_elaborator_process__command___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_error___at_lean_elaborator_process__command___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_process__command___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_elaborator_process__command___spec__3(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_process__command___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_rec_1__run__aux___at_lean_elaborator_process__command___spec__5(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_lean_elaborator_process__command___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_process__command___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_3);
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
 l_lean_elaborator_elaborator__m_monad = _init_l_lean_elaborator_elaborator__m_monad();
lean::mark_persistent(l_lean_elaborator_elaborator__m_monad);
 l_lean_elaborator_elaborator__m_lean_parser_monad__rec = _init_l_lean_elaborator_elaborator__m_lean_parser_monad__rec();
lean::mark_persistent(l_lean_elaborator_elaborator__m_lean_parser_monad__rec);
 l_lean_elaborator_elaborator__m_monad__reader = _init_l_lean_elaborator_elaborator__m_monad__reader();
lean::mark_persistent(l_lean_elaborator_elaborator__m_monad__reader);
 l_lean_elaborator_elaborator__m_monad__state = _init_l_lean_elaborator_elaborator__m_monad__state();
lean::mark_persistent(l_lean_elaborator_elaborator__m_monad__state);
 l_lean_elaborator_elaborator__m_monad__except = _init_l_lean_elaborator_elaborator__m_monad__except();
lean::mark_persistent(l_lean_elaborator_elaborator__m_monad__except);
 l_lean_elaborator_current__scope___closed__1 = _init_l_lean_elaborator_current__scope___closed__1();
lean::mark_persistent(l_lean_elaborator_current__scope___closed__1);
 l_lean_elaborator_modify__current__scope___closed__1 = _init_l_lean_elaborator_modify__current__scope___closed__1();
lean::mark_persistent(l_lean_elaborator_modify__current__scope___closed__1);
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
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3___closed__1();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3___closed__1);
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__1();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__1);
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2);
 l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1 = _init_l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1();
lean::mark_persistent(l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1);
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
 l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1 = _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1);
 l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9___closed__1 = _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9___closed__1();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9___closed__1);
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
 l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1();
lean::mark_persistent(l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1);
 l_lean_elaborator_declaration_elaborate___lambda__5___closed__1 = _init_l_lean_elaborator_declaration_elaborate___lambda__5___closed__1();
lean::mark_persistent(l_lean_elaborator_declaration_elaborate___lambda__5___closed__1);
 l_lean_elaborator_declaration_elaborate___lambda__5___closed__2 = _init_l_lean_elaborator_declaration_elaborate___lambda__5___closed__2();
lean::mark_persistent(l_lean_elaborator_declaration_elaborate___lambda__5___closed__2);
 l_lean_elaborator_declaration_elaborate___closed__1 = _init_l_lean_elaborator_declaration_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_declaration_elaborate___closed__1);
 l_lean_elaborator_declaration_elaborate___closed__2 = _init_l_lean_elaborator_declaration_elaborate___closed__2();
lean::mark_persistent(l_lean_elaborator_declaration_elaborate___closed__2);
 l_lean_elaborator_declaration_elaborate___closed__3 = _init_l_lean_elaborator_declaration_elaborate___closed__3();
lean::mark_persistent(l_lean_elaborator_declaration_elaborate___closed__3);
 l_lean_elaborator_declaration_elaborate___closed__4 = _init_l_lean_elaborator_declaration_elaborate___closed__4();
lean::mark_persistent(l_lean_elaborator_declaration_elaborate___closed__4);
 l_lean_elaborator_declaration_elaborate___closed__5 = _init_l_lean_elaborator_declaration_elaborate___closed__5();
lean::mark_persistent(l_lean_elaborator_declaration_elaborate___closed__5);
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
 l_lean_elaborator_no__kind_elaborate___closed__1 = _init_l_lean_elaborator_no__kind_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_no__kind_elaborate___closed__1);
 l_lean_elaborator_end_elaborate___closed__1 = _init_l_lean_elaborator_end_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_end_elaborate___closed__1);
 l_lean_elaborator_end_elaborate___closed__2 = _init_l_lean_elaborator_end_elaborate___closed__2();
lean::mark_persistent(l_lean_elaborator_end_elaborate___closed__2);
 l_lean_elaborator_end_elaborate___closed__3 = _init_l_lean_elaborator_end_elaborate___closed__3();
lean::mark_persistent(l_lean_elaborator_end_elaborate___closed__3);
 l_lean_elaborator_end_elaborate___closed__4 = _init_l_lean_elaborator_end_elaborate___closed__4();
lean::mark_persistent(l_lean_elaborator_end_elaborate___closed__4);
 l_lean_elaborator_section_elaborate___closed__1 = _init_l_lean_elaborator_section_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_section_elaborate___closed__1);
 l_lean_elaborator_namespace_elaborate___closed__1 = _init_l_lean_elaborator_namespace_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_namespace_elaborate___closed__1);
 l_lean_elaborator_eoi_elaborate___closed__1 = _init_l_lean_elaborator_eoi_elaborate___closed__1();
lean::mark_persistent(l_lean_elaborator_eoi_elaborate___closed__1);
 l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1 = _init_l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1();
lean::mark_persistent(l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1);
 l_lean_elaborator_elaborators = _init_l_lean_elaborator_elaborators();
lean::mark_persistent(l_lean_elaborator_elaborators);
 l_lean_elaborator_resolve__context___main___closed__1 = _init_l_lean_elaborator_resolve__context___main___closed__1();
lean::mark_persistent(l_lean_elaborator_resolve__context___main___closed__1);
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__1 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__1();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__1);
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__2 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__2();
lean::mark_persistent(l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__2);
 l_lean_elaborator_mk__state___closed__1 = _init_l_lean_elaborator_mk__state___closed__1();
lean::mark_persistent(l_lean_elaborator_mk__state___closed__1);
 l_lean_elaborator_mk__state___closed__2 = _init_l_lean_elaborator_mk__state___closed__2();
lean::mark_persistent(l_lean_elaborator_mk__state___closed__2);
 l_lean_elaborator_mk__state___closed__3 = _init_l_lean_elaborator_mk__state___closed__3();
lean::mark_persistent(l_lean_elaborator_mk__state___closed__3);
 l_lean_elaborator_mk__state___closed__4 = _init_l_lean_elaborator_mk__state___closed__4();
lean::mark_persistent(l_lean_elaborator_mk__state___closed__4);
 l_lean_elaborator_mk__state___closed__5 = _init_l_lean_elaborator_mk__state___closed__5();
lean::mark_persistent(l_lean_elaborator_mk__state___closed__5);
 l_lean_elaborator_mk__state___closed__6 = _init_l_lean_elaborator_mk__state___closed__6();
lean::mark_persistent(l_lean_elaborator_mk__state___closed__6);
 l_lean_elaborator_max__recursion = _init_l_lean_elaborator_max__recursion();
lean::mark_persistent(l_lean_elaborator_max__recursion);
 l_lean_elaborator_process__command___lambda__1___closed__1 = _init_l_lean_elaborator_process__command___lambda__1___closed__1();
lean::mark_persistent(l_lean_elaborator_process__command___lambda__1___closed__1);
 l_lean_elaborator_process__command___lambda__2___closed__1 = _init_l_lean_elaborator_process__command___lambda__2___closed__1();
lean::mark_persistent(l_lean_elaborator_process__command___lambda__2___closed__1);
 l_lean_elaborator_process__command___lambda__2___closed__2 = _init_l_lean_elaborator_process__command___lambda__2___closed__2();
lean::mark_persistent(l_lean_elaborator_process__command___lambda__2___closed__2);
 l_lean_elaborator_process__command___closed__1 = _init_l_lean_elaborator_process__command___closed__1();
lean::mark_persistent(l_lean_elaborator_process__command___closed__1);
}
