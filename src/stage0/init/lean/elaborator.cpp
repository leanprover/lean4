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
obj* l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_token__map_insert___rarg(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_eoi_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(obj*, obj*);
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(obj*);
obj* l_lean_elaborator_section_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_modify__current__scope___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__4(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_modify__current__scope(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_ordered__rbmap_find___spec__1___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_command_variables;
extern "C" obj* lean_expr_mk_pi(obj*, uint8, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11___boxed(obj*, obj*, obj*, obj*);
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
obj* l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_level__get__app__args___main(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3___closed__1;
obj* l_lean_elaborator_elab__def__like(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___boxed(obj*, obj*, obj*);
obj* l_id___boxed(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3(obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_sort(obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1(obj*);
obj* l_lean_elaborator_attrs__to__pexpr(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_attribute_has__view;
obj* l_lean_elaborator_namespace_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2(obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(obj*);
obj* l_lean_elaborator_match__spec___closed__1;
obj* l_lean_elaborator_resolve__context___main___closed__1;
obj* l_lean_elaborator_init__quot_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_open_elaborate___lambda__1(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___rarg(obj*, obj*);
extern obj* l_lean_parser_level_leading_has__view;
extern obj* l_lean_parser_command_reserve__notation_has__view;
obj* l_lean_elaborator_notation_elaborate___closed__1;
obj* l_list_foldl___main___at_lean_expr_mk__app___spec__1(obj*, obj*);
obj* l_lean_elaborator_current__scope___closed__1;
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19___boxed(obj*, obj*, obj*, obj*);
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
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___boxed(obj*, obj*, obj*, obj*);
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
obj* l_lean_elaborator_include_elaborate(obj*, obj*, obj*, obj*);
uint8 l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_list_filter__map___main___rarg(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_match_has__view;
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_level__get__app__args(obj*, obj*, obj*, obj*);
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__5(obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__9(obj*);
extern obj* l_lean_parser_command_open;
obj* l_lean_elaborator_declaration_elaborate___closed__4;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__config__coe__frontend__config(obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__26;
obj* l_lean_elaborator_declaration_elaborate___lambda__5___closed__1;
obj* l_lean_kvmap_set__string(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14(obj*, obj*);
obj* l_lean_elaborator_elab__def__like___lambda__1(obj*, obj*);
obj* l_lean_parser_term_get__leading___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__9(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3(obj*, obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3___boxed(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__7(obj*);
extern obj* l_lean_expander_error___rarg___lambda__1___closed__1;
obj* l_lean_elaborator_process__command___lambda__1___closed__2;
obj* l_lean_elaborator_notation_elaborate__aux___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__eqns___closed__2;
obj* l_reader__t_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_notation_elaborate__aux___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1(obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__3___boxed(obj*, obj*, obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__state___closed__5;
obj* l_lean_elaborator_universe_elaborate___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__31;
obj* l_lean_elaborator_module_header_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_ordered__rbmap_of__list___spec__7___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_register__notation__macro(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_preresolve___main___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_include_elaborate___spec__1(obj*, obj*);
obj* l_list_enum__from___main___rarg(obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_variables_elaborate___closed__2;
uint8 l_lean_elaborator_match__precedence___main(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__39;
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_view_to__nat___main(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_sort_has__view_x_27___lambda__1___closed__4;
obj* l_lean_elaborator_end_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_open_has__view;
obj* l_lean_elaborator_mk__notation__kind___rarg(obj*);
obj* l_lean_elaborator_resolve__context___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12___boxed(obj*, obj*, obj*, obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__13(obj*, obj*);
extern "C" obj* lean_expr_local(obj*, obj*, obj*, uint8);
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
obj* l_lean_parser_term_simple__binder_view_to__binder__info___main(obj*);
extern obj* l_lean_parser_command_set__option;
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2(obj*, obj*);
obj* l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1___boxed(obj*, obj*);
obj* l_lean_elaborator_section_elaborate___closed__1;
obj* l_lean_elaborator_elab__def__like___closed__1;
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(obj*);
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_expr_mk__annotation___closed__1;
obj* l_list_zip___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__6;
obj* l_lean_elaborator_check_elaborate(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__2;
obj* l_lean_elaborator_elaborator__m_monad;
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_elaborator_declaration_elaborate___closed__2;
obj* l_lean_elaborator_eoi_elaborate___closed__1;
obj* l_lean_elaborator_declaration_elaborate___closed__5;
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
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___boxed(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__9(obj*);
extern obj* l_lean_parser_string__lit_has__view;
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__8___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_pi_has__view;
obj* l_lean_elaborator_export_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2___boxed(obj*);
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_find___rarg(obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
uint8 l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj*, uint8, obj*);
obj* l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_resolve__context___main___lambda__1(obj*, obj*);
extern obj* l_lean_parser_command_universe_has__view;
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
obj* l_state__t_monad__state___rarg(obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__7___boxed(obj*);
extern "C" obj* lean_expr_mk_lambda(obj*, uint8, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_kvmap_set__nat(obj*, obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__11(obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main___closed__4;
obj* l_lean_elaborator_check_elaborate___closed__1;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_command_include;
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__8(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_set__option_elaborate___lambda__1(obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__6(obj*, obj*);
obj* l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_environment_contains___boxed(obj*, obj*);
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
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1(obj*, obj*);
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__32;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_lean_parser_trie_insert___rarg(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_preresolve___main(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___boxed(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind___rarg___closed__1;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__5;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1___boxed(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__3;
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(obj*, obj*);
obj* l_lean_elaborator_expr_mk__annotation(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17___boxed(obj*, obj*);
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
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_name__set_insert___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view;
obj* l_lean_elaborator_to__pexpr___main___closed__4;
obj* l_lean_parser_syntax_get__pos(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4(obj*, obj*, obj*);
extern "C" obj* level_mk_imax(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__15___boxed(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_attribute_elaborate___closed__2;
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5;
obj* l_list_zip__with___main___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_reserve__notation_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_simple__binders__to__pexpr(obj*, obj*, obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(obj*, obj*, obj*);
obj* l_lean_elaborator_is__open__namespace___boxed(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__47;
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(obj*);
obj* l_lean_elaborator_namespace_elaborate___closed__1;
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__parser(obj*, obj*, obj*);
obj* l_lean_elaborator_match__open__spec(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__11;
obj* l_lean_elaborator_level__add___main___boxed(obj*, obj*);
obj* l_lean_elaborator_end_elaborate___closed__4;
obj* l_lean_elaborator_ordered__rbmap_empty(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__16;
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14___boxed(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5(obj*, obj*, obj*, obj*);
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
obj* l_lean_elaborator_end_elaborate___closed__2;
uint8 l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(obj*, uint8, obj*);
obj* l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1___boxed(obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_match__precedence___boxed(obj*, obj*);
extern obj* l_lean_message__log_empty;
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9(obj*);
obj* l_lean_elaborator_register__notation__macro___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_export_elaborate(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__38;
obj* l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(obj*);
uint8 l_lean_elaborator_is__open__namespace___main(obj*, obj*);
obj* l_lean_elaborator_notation_elaborate___lambda__1(obj*, obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_elaborator_elaborator__m_monad__reader;
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
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__6___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3;
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(obj*, obj*, obj*, obj*);
extern "C" obj* level_mk_succ(obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__45;
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__14;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_universe_elaborate___closed__2;
obj* l_lean_elaborator_is__open__namespace___main___boxed(obj*, obj*);
extern obj* l_lean_parser_term_projection_has__view;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_end_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__5___closed__2;
obj* l_lean_elaborator_variables_elaborate___closed__1;
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__12;
obj* l_lean_parser_syntax_to__format___main(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(obj*, obj*, obj*, obj*);
obj* l_lean_name_append___main(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
obj* l_lean_expander_error___at_lean_elaborator_process__command___spec__1___boxed(obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__35;
obj* l_lean_elaborator_to__pexpr___main___closed__25;
obj* l_lean_elaborator_names__to__pexpr(obj*);
obj* l_lean_elaborator_modify__current__scope___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_check_has__view;
obj* l_lean_elaborator_set__option_elaborate(obj*, obj*, obj*, obj*);
obj* l_reader__t_read___rarg(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_no__kind_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_resolve__context___main(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_max__prec;
obj* l_lean_elaborator_notation_elaborate__aux(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__m_lean_parser_monad__rec;
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
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2(obj*, obj*, obj*);
extern obj* l_lean_parser_term_struct__inst_has__view;
extern obj* l_lean_parser_term_lambda_has__view;
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__eqns___closed__1;
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_resolve__context(obj*, obj*, obj*, obj*);
obj* l_except__t_monad___rarg(obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__5(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_let(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_app_has__view;
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2___boxed(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
obj* l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__level___main(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_ident__univs_has__view;
obj* l_lean_elaborator_to__pexpr___main___closed__9;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(obj*);
obj* l_state__t_monad__except___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
obj* l_reader__t_monad__except___rarg(obj*);
extern obj* l_lean_parser_term_sort__app_has__view;
extern obj* l_lean_parser_term_explicit_has__view;
obj* l_fix__1___rarg___lambda__1___boxed(obj*, obj*);
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
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10(obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1;
obj* l_lean_elaborator_end_elaborate___closed__3;
obj* l_lean_format_pretty(obj*, obj*);
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_namespace_has__view;
obj* l_lean_elaborator_preresolve___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__15;
obj* l_lean_elaborator_notation_elaborate___closed__2;
obj* l_lean_elaborator_to__pexpr___main___closed__18;
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_term_inaccessible_has__view;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1(obj*);
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5___boxed(obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__2;
obj* l_lean_elaborator_dummy;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_module_header_elaborate(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_parser_syntax_kind___main(obj*);
obj* l_lean_elaborator_eoi_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__2;
obj* l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___boxed(obj*);
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___lambda__1(obj*, uint8, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1;
obj* l_lean_elaborator_section_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_preresolve(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___rarg(obj*, obj*);
obj* l_lean_elaborator_declaration_elaborate___lambda__2(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
extern obj* l_lean_parser_module_header_has__view;
uint8 l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(uint8, obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__1;
extern obj* l_lean_parser_command_section;
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__9___closed__1;
obj* l_lean_elaborator_to__pexpr___main___closed__21;
uint8 l_lean_name_quick__lt(obj*, obj*);
obj* l_lean_elaborator_end_elaborate___closed__1;
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___boxed(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_struct__inst__item_has__view;
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_match__precedence___main___boxed(obj*, obj*);
extern obj* l_lean_parser_term_borrowed_has__view;
obj* l_lean_parser_term_binders_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_current__scope___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_find(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_mk__state___spec__1;
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_universe;
obj* l_lean_elaborator_to__pexpr___main___closed__19;
obj* l_list_map___main___at_lean_elaborator_ident__univ__params__to__pexpr___spec__1(obj*);
extern obj* l_lean_parser_term_show_has__view;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(obj*, obj*, obj*, obj*);
obj* l_lean_level_of__nat___main(obj*);
extern obj* l_lean_parser_syntax_reprint__lst___main___closed__1;
obj* l_lean_elaborator_declaration_elaborate___lambda__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__22;
obj* l_reader__t_lift___rarg___boxed(obj*, obj*);
obj* l_lean_parser_term_binder__ident_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__8;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__4___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__43;
obj* l_lean_elaborator_attribute_elaborate___closed__1;
uint8 l_lean_elaborator_match__precedence(obj*, obj*);
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
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__7(obj*);
obj* l_lean_elaborator_match__spec(obj*, obj*);
obj* l_lean_expander_mk__notation__transformer(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__30;
obj* l_lean_expr_local___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__eqns(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__14(obj*);
obj* l_lean_elaborator_level__add___main(obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8(obj*, obj*, obj*);
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
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__state(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_kvmap_insert__core___main(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__28;
obj* l_lean_elaborator_to__level___main___closed__3;
extern obj* l_lean_parser_command_end_has__view;
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___boxed(obj*, obj*, obj*, obj*);
obj* l_id_bind___boxed(obj*, obj*);
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
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__2(obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_ordered__rbmap_of__list___spec__6(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_init__quot;
obj* l_lean_elaborator_variables_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__41;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__7___closed__1;
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(obj*);
obj* l_lean_elaborator_ident__univ__params__to__pexpr(obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__10(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbtree_to__list___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_update__parser__config___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_elaborator_process__command___spec__3___boxed(obj*, obj*);
obj* l_lean_elaborator_to__pexpr(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_postprocess__notation__spec(obj*);
obj* l_lean_elaborator_elab__def__like___closed__2;
extern obj* l_lean_parser_command_include_has__view;
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__5(obj*);
extern obj* l_lean_parser_command_namespace;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3___boxed(obj*, obj*, obj*, obj*);
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
extern obj* l_lean_expander_get__opt__type___main___closed__1;
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_level_trailing_has__view;
obj* l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
obj* l_lean_elaborator_attribute_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__29;
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__5(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
extern obj* l_lean_expander_no__expansion___closed__1;
extern "C" obj* lean_expr_mk_bvar(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__40;
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__15(obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18(obj*, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(obj*);
extern "C" obj* lean_expr_mk_mvar(obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_id_monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11(obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_command_elaborate(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_prec__to__nat___main(obj*);
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__6(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_view_value(obj*);
obj* l_lean_elaborator_mk__state___closed__3;
obj* l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__42;
extern "C" uint8 lean_environment_contains(obj*, obj*);
extern obj* l_lean_parser_command_notation_has__view;
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__2(obj*);
obj* l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_check;
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11___boxed(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_id_monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__10(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_export;
obj* l_lean_elaborator_old__elab__command___lambda__1(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_lean_elaborator_to__pexpr___main___closed__44;
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2(obj*, obj*, obj*);
obj* l_lean_elaborator_variables_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
obj* l_lean_elaborator_init__quot_elaborate___closed__1;
obj* l_lean_elaborator_postprocess__notation__spec___closed__1;
obj* l_lean_elaborator_mk__state___closed__1;
extern obj* l_lean_parser_command_set__option_has__view;
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
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg), 2, 0);
return x_0;
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
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; uint8 x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 3);
lean::inc(x_11);
lean::dec(x_2);
x_14 = l_lean_name_quick__lt(x_3, x_7);
if (x_14 == 0)
{
uint8 x_16; 
lean::dec(x_5);
x_16 = l_lean_name_quick__lt(x_7, x_3);
lean::dec(x_7);
if (x_16 == 0)
{
obj* x_19; 
lean::dec(x_11);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_9);
return x_19;
}
else
{
lean::dec(x_9);
x_1 = x_0;
x_2 = x_11;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
x_1 = x_0;
x_2 = x_5;
goto _start;
}
}
}
}
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
x_2 = lean::box(0);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7(x_2, lean::box(0), x_3, x_1);
return x_6;
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
obj* l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___main___at_lean_elaborator_to__level___main___spec__7(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_find___main___at_lean_elaborator_to__level___main___spec__6(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8(obj* x_0, obj* x_1) {
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
x_8 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11(obj* x_0, obj* x_1) {
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
x_8 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14(obj* x_0, obj* x_1) {
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
x_8 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17(obj* x_0, obj* x_1) {
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
x_8 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
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
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean_expr_mk_sort(x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__26() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("struct");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = l_option_get__or__else___main___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__28() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected item in structure instance notation");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__29() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed choice");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__30() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("choice");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
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
x_1 = lean::mk_string("have");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
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
obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; uint8 x_316; obj* x_317; obj* x_318; obj* x_321; obj* x_322; obj* x_323; 
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
x_322 = l_lean_elaborator_to__pexpr___main___closed__25;
x_323 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8(x_322, x_321);
if (lean::obj_tag(x_318) == 0)
{
obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; 
x_324 = l_lean_elaborator_to__pexpr___main___closed__26;
x_325 = l_lean_elaborator_to__pexpr___main___closed__27;
x_326 = l_lean_kvmap_set__name(x_317, x_324, x_325);
x_327 = lean_expr_mk_mdata(x_326, x_323);
if (lean::is_scalar(x_309)) {
 x_328 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_328 = x_309;
}
lean::cnstr_set(x_328, 0, x_327);
lean::cnstr_set(x_328, 1, x_307);
x_15 = x_328;
goto lbl_16;
}
else
{
obj* x_329; obj* x_331; obj* x_332; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_340; obj* x_341; obj* x_342; obj* x_343; 
x_329 = lean::cnstr_get(x_318, 0);
if (lean::is_exclusive(x_318)) {
 x_331 = x_318;
} else {
 lean::inc(x_329);
 lean::dec(x_318);
 x_331 = lean::box(0);
}
x_332 = lean::cnstr_get(x_329, 0);
lean::inc(x_332);
lean::dec(x_329);
x_335 = l_lean_elaborator_mangle__ident(x_332);
if (lean::is_scalar(x_331)) {
 x_336 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_336 = x_331;
}
lean::cnstr_set(x_336, 0, x_335);
x_337 = lean::box(0);
x_338 = l_option_get__or__else___main___rarg(x_336, x_337);
lean::dec(x_336);
x_340 = l_lean_elaborator_to__pexpr___main___closed__26;
x_341 = l_lean_kvmap_set__name(x_317, x_340, x_338);
x_342 = lean_expr_mk_mdata(x_341, x_323);
if (lean::is_scalar(x_309)) {
 x_343 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_343 = x_309;
}
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_307);
x_15 = x_343;
goto lbl_16;
}
}
}
}
else
{
obj* x_344; obj* x_346; 
x_344 = lean::cnstr_get(x_220, 0);
lean::inc(x_344);
x_346 = lean::cnstr_get(x_344, 0);
lean::inc(x_346);
lean::dec(x_344);
if (lean::obj_tag(x_346) == 0)
{
obj* x_349; obj* x_350; obj* x_353; obj* x_354; obj* x_357; obj* x_358; obj* x_359; obj* x_361; 
if (lean::is_exclusive(x_220)) {
 lean::cnstr_release(x_220, 0);
 lean::cnstr_release(x_220, 1);
 x_349 = x_220;
} else {
 lean::dec(x_220);
 x_349 = lean::box(0);
}
x_350 = lean::cnstr_get(x_219, 0);
lean::inc(x_350);
lean::dec(x_219);
x_353 = l_lean_parser_term_struct__inst__item_has__view;
x_354 = lean::cnstr_get(x_353, 1);
lean::inc(x_354);
lean::dec(x_353);
x_357 = lean::apply_1(x_354, x_346);
x_358 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_358, 0, x_357);
x_359 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_2);
x_361 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_358, x_359, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_358);
if (lean::obj_tag(x_361) == 0)
{
obj* x_371; obj* x_373; obj* x_374; 
lean::dec(x_349);
lean::dec(x_350);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_214);
lean::dec(x_210);
x_371 = lean::cnstr_get(x_361, 0);
if (lean::is_exclusive(x_361)) {
 x_373 = x_361;
} else {
 lean::inc(x_371);
 lean::dec(x_361);
 x_373 = lean::box(0);
}
if (lean::is_scalar(x_373)) {
 x_374 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_374 = x_373;
}
lean::cnstr_set(x_374, 0, x_371);
return x_374;
}
else
{
obj* x_375; obj* x_378; obj* x_380; obj* x_385; 
x_375 = lean::cnstr_get(x_361, 0);
lean::inc(x_375);
lean::dec(x_361);
x_378 = lean::cnstr_get(x_375, 0);
lean::inc(x_378);
x_380 = lean::cnstr_get(x_375, 1);
lean::inc(x_380);
lean::dec(x_375);
lean::inc(x_2);
lean::inc(x_0);
x_385 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_214, x_1, x_2, x_380);
if (lean::obj_tag(x_385) == 0)
{
obj* x_393; obj* x_395; obj* x_396; 
lean::dec(x_349);
lean::dec(x_350);
lean::dec(x_8);
lean::dec(x_378);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_393 = lean::cnstr_get(x_385, 0);
if (lean::is_exclusive(x_385)) {
 x_395 = x_385;
} else {
 lean::inc(x_393);
 lean::dec(x_385);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_393);
return x_396;
}
else
{
obj* x_397; obj* x_400; obj* x_402; obj* x_405; obj* x_409; 
x_397 = lean::cnstr_get(x_385, 0);
lean::inc(x_397);
lean::dec(x_385);
x_400 = lean::cnstr_get(x_397, 0);
lean::inc(x_400);
x_402 = lean::cnstr_get(x_397, 1);
lean::inc(x_402);
lean::dec(x_397);
lean::inc(x_2);
lean::inc(x_0);
x_409 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__12(x_0, x_350, x_1, x_2, x_402);
if (lean::obj_tag(x_409) == 0)
{
obj* x_417; obj* x_419; obj* x_420; 
lean::dec(x_349);
lean::dec(x_8);
lean::dec(x_378);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_400);
lean::dec(x_210);
x_417 = lean::cnstr_get(x_409, 0);
if (lean::is_exclusive(x_409)) {
 x_419 = x_409;
} else {
 lean::inc(x_417);
 lean::dec(x_409);
 x_419 = lean::box(0);
}
if (lean::is_scalar(x_419)) {
 x_420 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_420 = x_419;
}
lean::cnstr_set(x_420, 0, x_417);
return x_420;
}
else
{
obj* x_421; obj* x_424; 
x_421 = lean::cnstr_get(x_409, 0);
lean::inc(x_421);
lean::dec(x_409);
x_424 = lean::cnstr_get(x_210, 2);
lean::inc(x_424);
if (lean::obj_tag(x_424) == 0)
{
obj* x_427; obj* x_429; obj* x_431; obj* x_432; 
lean::dec(x_349);
x_427 = lean::cnstr_get(x_421, 0);
x_429 = lean::cnstr_get(x_421, 1);
if (lean::is_exclusive(x_421)) {
 x_431 = x_421;
} else {
 lean::inc(x_427);
 lean::inc(x_429);
 lean::dec(x_421);
 x_431 = lean::box(0);
}
if (lean::is_scalar(x_431)) {
 x_432 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_432 = x_431;
}
lean::cnstr_set(x_432, 0, x_427);
lean::cnstr_set(x_432, 1, x_429);
x_405 = x_432;
goto lbl_406;
}
else
{
obj* x_433; obj* x_435; obj* x_438; obj* x_441; obj* x_445; 
x_433 = lean::cnstr_get(x_421, 0);
lean::inc(x_433);
x_435 = lean::cnstr_get(x_421, 1);
lean::inc(x_435);
lean::dec(x_421);
x_438 = lean::cnstr_get(x_424, 0);
lean::inc(x_438);
lean::dec(x_424);
x_441 = lean::cnstr_get(x_438, 0);
lean::inc(x_441);
lean::dec(x_438);
lean::inc(x_2);
x_445 = l_lean_elaborator_to__pexpr___main(x_441, x_1, x_2, x_435);
if (lean::obj_tag(x_445) == 0)
{
obj* x_454; obj* x_456; obj* x_457; 
lean::dec(x_349);
lean::dec(x_8);
lean::dec(x_378);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_400);
lean::dec(x_433);
lean::dec(x_210);
x_454 = lean::cnstr_get(x_445, 0);
if (lean::is_exclusive(x_445)) {
 x_456 = x_445;
} else {
 lean::inc(x_454);
 lean::dec(x_445);
 x_456 = lean::box(0);
}
if (lean::is_scalar(x_456)) {
 x_457 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_457 = x_456;
}
lean::cnstr_set(x_457, 0, x_454);
return x_457;
}
else
{
obj* x_458; obj* x_461; obj* x_463; obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; 
x_458 = lean::cnstr_get(x_445, 0);
lean::inc(x_458);
lean::dec(x_445);
x_461 = lean::cnstr_get(x_458, 0);
x_463 = lean::cnstr_get(x_458, 1);
if (lean::is_exclusive(x_458)) {
 x_465 = x_458;
} else {
 lean::inc(x_461);
 lean::inc(x_463);
 lean::dec(x_458);
 x_465 = lean::box(0);
}
x_466 = lean::box(0);
if (lean::is_scalar(x_349)) {
 x_467 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_467 = x_349;
}
lean::cnstr_set(x_467, 0, x_461);
lean::cnstr_set(x_467, 1, x_466);
x_468 = l_list_append___rarg(x_433, x_467);
if (lean::is_scalar(x_465)) {
 x_469 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_469 = x_465;
}
lean::cnstr_set(x_469, 0, x_468);
lean::cnstr_set(x_469, 1, x_463);
x_405 = x_469;
goto lbl_406;
}
}
}
lbl_406:
{
obj* x_470; obj* x_472; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; uint8 x_481; obj* x_482; obj* x_483; obj* x_486; obj* x_487; obj* x_488; 
x_470 = lean::cnstr_get(x_405, 0);
x_472 = lean::cnstr_get(x_405, 1);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_set(x_405, 0, lean::box(0));
 lean::cnstr_set(x_405, 1, lean::box(0));
 x_474 = x_405;
} else {
 lean::inc(x_470);
 lean::inc(x_472);
 lean::dec(x_405);
 x_474 = lean::box(0);
}
x_475 = lean::box(0);
x_476 = lean::mk_nat_obj(0u);
x_477 = l_list_length__aux___main___rarg(x_400, x_476);
x_478 = l_lean_elaborator_to__pexpr___main___closed__23;
x_479 = l_lean_kvmap_set__nat(x_475, x_478, x_477);
x_480 = l_lean_elaborator_to__pexpr___main___closed__24;
x_481 = lean::unbox(x_378);
x_482 = l_lean_kvmap_set__bool(x_479, x_480, x_481);
x_483 = lean::cnstr_get(x_210, 1);
lean::inc(x_483);
lean::dec(x_210);
x_486 = l_list_append___rarg(x_400, x_470);
x_487 = l_lean_elaborator_to__pexpr___main___closed__25;
x_488 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11(x_487, x_486);
if (lean::obj_tag(x_483) == 0)
{
obj* x_489; obj* x_490; obj* x_491; obj* x_492; obj* x_493; 
x_489 = l_lean_elaborator_to__pexpr___main___closed__26;
x_490 = l_lean_elaborator_to__pexpr___main___closed__27;
x_491 = l_lean_kvmap_set__name(x_482, x_489, x_490);
x_492 = lean_expr_mk_mdata(x_491, x_488);
if (lean::is_scalar(x_474)) {
 x_493 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_493 = x_474;
}
lean::cnstr_set(x_493, 0, x_492);
lean::cnstr_set(x_493, 1, x_472);
x_15 = x_493;
goto lbl_16;
}
else
{
obj* x_494; obj* x_496; obj* x_497; obj* x_500; obj* x_501; obj* x_502; obj* x_503; obj* x_505; obj* x_506; obj* x_507; obj* x_508; 
x_494 = lean::cnstr_get(x_483, 0);
if (lean::is_exclusive(x_483)) {
 x_496 = x_483;
} else {
 lean::inc(x_494);
 lean::dec(x_483);
 x_496 = lean::box(0);
}
x_497 = lean::cnstr_get(x_494, 0);
lean::inc(x_497);
lean::dec(x_494);
x_500 = l_lean_elaborator_mangle__ident(x_497);
if (lean::is_scalar(x_496)) {
 x_501 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_501 = x_496;
}
lean::cnstr_set(x_501, 0, x_500);
x_502 = lean::box(0);
x_503 = l_option_get__or__else___main___rarg(x_501, x_502);
lean::dec(x_501);
x_505 = l_lean_elaborator_to__pexpr___main___closed__26;
x_506 = l_lean_kvmap_set__name(x_482, x_505, x_503);
x_507 = lean_expr_mk_mdata(x_506, x_488);
if (lean::is_scalar(x_474)) {
 x_508 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_508 = x_474;
}
lean::cnstr_set(x_508, 0, x_507);
lean::cnstr_set(x_508, 1, x_472);
x_15 = x_508;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_509; obj* x_511; 
x_509 = lean::cnstr_get(x_220, 1);
if (lean::is_exclusive(x_220)) {
 lean::cnstr_release(x_220, 0);
 lean::cnstr_set(x_220, 1, lean::box(0));
 x_511 = x_220;
} else {
 lean::inc(x_509);
 lean::dec(x_220);
 x_511 = lean::box(0);
}
if (lean::obj_tag(x_509) == 0)
{
obj* x_513; obj* x_518; 
lean::dec(x_346);
x_513 = lean::cnstr_get(x_219, 0);
lean::inc(x_513);
lean::dec(x_219);
lean::inc(x_2);
lean::inc(x_0);
x_518 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_214, x_1, x_2, x_3);
if (lean::obj_tag(x_518) == 0)
{
obj* x_525; obj* x_527; obj* x_528; 
lean::dec(x_513);
lean::dec(x_511);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_525 = lean::cnstr_get(x_518, 0);
if (lean::is_exclusive(x_518)) {
 x_527 = x_518;
} else {
 lean::inc(x_525);
 lean::dec(x_518);
 x_527 = lean::box(0);
}
if (lean::is_scalar(x_527)) {
 x_528 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_528 = x_527;
}
lean::cnstr_set(x_528, 0, x_525);
return x_528;
}
else
{
obj* x_529; obj* x_532; obj* x_534; obj* x_537; obj* x_541; 
x_529 = lean::cnstr_get(x_518, 0);
lean::inc(x_529);
lean::dec(x_518);
x_532 = lean::cnstr_get(x_529, 0);
lean::inc(x_532);
x_534 = lean::cnstr_get(x_529, 1);
lean::inc(x_534);
lean::dec(x_529);
lean::inc(x_2);
lean::inc(x_0);
x_541 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__15(x_0, x_513, x_1, x_2, x_534);
if (lean::obj_tag(x_541) == 0)
{
obj* x_548; obj* x_550; obj* x_551; 
lean::dec(x_511);
lean::dec(x_532);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_548 = lean::cnstr_get(x_541, 0);
if (lean::is_exclusive(x_541)) {
 x_550 = x_541;
} else {
 lean::inc(x_548);
 lean::dec(x_541);
 x_550 = lean::box(0);
}
if (lean::is_scalar(x_550)) {
 x_551 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_551 = x_550;
}
lean::cnstr_set(x_551, 0, x_548);
return x_551;
}
else
{
obj* x_552; obj* x_555; 
x_552 = lean::cnstr_get(x_541, 0);
lean::inc(x_552);
lean::dec(x_541);
x_555 = lean::cnstr_get(x_210, 2);
lean::inc(x_555);
if (lean::obj_tag(x_555) == 0)
{
obj* x_558; obj* x_560; obj* x_562; obj* x_563; 
lean::dec(x_511);
x_558 = lean::cnstr_get(x_552, 0);
x_560 = lean::cnstr_get(x_552, 1);
if (lean::is_exclusive(x_552)) {
 x_562 = x_552;
} else {
 lean::inc(x_558);
 lean::inc(x_560);
 lean::dec(x_552);
 x_562 = lean::box(0);
}
if (lean::is_scalar(x_562)) {
 x_563 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_563 = x_562;
}
lean::cnstr_set(x_563, 0, x_558);
lean::cnstr_set(x_563, 1, x_560);
x_537 = x_563;
goto lbl_538;
}
else
{
obj* x_564; obj* x_566; obj* x_569; obj* x_572; obj* x_576; 
x_564 = lean::cnstr_get(x_552, 0);
lean::inc(x_564);
x_566 = lean::cnstr_get(x_552, 1);
lean::inc(x_566);
lean::dec(x_552);
x_569 = lean::cnstr_get(x_555, 0);
lean::inc(x_569);
lean::dec(x_555);
x_572 = lean::cnstr_get(x_569, 0);
lean::inc(x_572);
lean::dec(x_569);
lean::inc(x_2);
x_576 = l_lean_elaborator_to__pexpr___main(x_572, x_1, x_2, x_566);
if (lean::obj_tag(x_576) == 0)
{
obj* x_584; obj* x_586; obj* x_587; 
lean::dec(x_564);
lean::dec(x_511);
lean::dec(x_532);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_584 = lean::cnstr_get(x_576, 0);
if (lean::is_exclusive(x_576)) {
 x_586 = x_576;
} else {
 lean::inc(x_584);
 lean::dec(x_576);
 x_586 = lean::box(0);
}
if (lean::is_scalar(x_586)) {
 x_587 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_587 = x_586;
}
lean::cnstr_set(x_587, 0, x_584);
return x_587;
}
else
{
obj* x_588; obj* x_591; obj* x_593; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; 
x_588 = lean::cnstr_get(x_576, 0);
lean::inc(x_588);
lean::dec(x_576);
x_591 = lean::cnstr_get(x_588, 0);
x_593 = lean::cnstr_get(x_588, 1);
if (lean::is_exclusive(x_588)) {
 x_595 = x_588;
} else {
 lean::inc(x_591);
 lean::inc(x_593);
 lean::dec(x_588);
 x_595 = lean::box(0);
}
x_596 = lean::box(0);
if (lean::is_scalar(x_511)) {
 x_597 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_597 = x_511;
}
lean::cnstr_set(x_597, 0, x_591);
lean::cnstr_set(x_597, 1, x_596);
x_598 = l_list_append___rarg(x_564, x_597);
if (lean::is_scalar(x_595)) {
 x_599 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_599 = x_595;
}
lean::cnstr_set(x_599, 0, x_598);
lean::cnstr_set(x_599, 1, x_593);
x_537 = x_599;
goto lbl_538;
}
}
}
lbl_538:
{
obj* x_600; obj* x_602; obj* x_604; obj* x_605; obj* x_606; obj* x_607; obj* x_608; obj* x_609; obj* x_610; uint8 x_611; obj* x_612; obj* x_613; obj* x_616; obj* x_617; obj* x_618; 
x_600 = lean::cnstr_get(x_537, 0);
x_602 = lean::cnstr_get(x_537, 1);
if (lean::is_exclusive(x_537)) {
 lean::cnstr_set(x_537, 0, lean::box(0));
 lean::cnstr_set(x_537, 1, lean::box(0));
 x_604 = x_537;
} else {
 lean::inc(x_600);
 lean::inc(x_602);
 lean::dec(x_537);
 x_604 = lean::box(0);
}
x_605 = lean::box(0);
x_606 = lean::mk_nat_obj(0u);
x_607 = l_list_length__aux___main___rarg(x_532, x_606);
x_608 = l_lean_elaborator_to__pexpr___main___closed__23;
x_609 = l_lean_kvmap_set__nat(x_605, x_608, x_607);
x_610 = l_lean_elaborator_to__pexpr___main___closed__24;
x_611 = 1;
x_612 = l_lean_kvmap_set__bool(x_609, x_610, x_611);
x_613 = lean::cnstr_get(x_210, 1);
lean::inc(x_613);
lean::dec(x_210);
x_616 = l_list_append___rarg(x_532, x_600);
x_617 = l_lean_elaborator_to__pexpr___main___closed__25;
x_618 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14(x_617, x_616);
if (lean::obj_tag(x_613) == 0)
{
obj* x_619; obj* x_620; obj* x_621; obj* x_622; obj* x_623; 
x_619 = l_lean_elaborator_to__pexpr___main___closed__26;
x_620 = l_lean_elaborator_to__pexpr___main___closed__27;
x_621 = l_lean_kvmap_set__name(x_612, x_619, x_620);
x_622 = lean_expr_mk_mdata(x_621, x_618);
if (lean::is_scalar(x_604)) {
 x_623 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_623 = x_604;
}
lean::cnstr_set(x_623, 0, x_622);
lean::cnstr_set(x_623, 1, x_602);
x_15 = x_623;
goto lbl_16;
}
else
{
obj* x_624; obj* x_626; obj* x_627; obj* x_630; obj* x_631; obj* x_632; obj* x_633; obj* x_635; obj* x_636; obj* x_637; obj* x_638; 
x_624 = lean::cnstr_get(x_613, 0);
if (lean::is_exclusive(x_613)) {
 x_626 = x_613;
} else {
 lean::inc(x_624);
 lean::dec(x_613);
 x_626 = lean::box(0);
}
x_627 = lean::cnstr_get(x_624, 0);
lean::inc(x_627);
lean::dec(x_624);
x_630 = l_lean_elaborator_mangle__ident(x_627);
if (lean::is_scalar(x_626)) {
 x_631 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_631 = x_626;
}
lean::cnstr_set(x_631, 0, x_630);
x_632 = lean::box(0);
x_633 = l_option_get__or__else___main___rarg(x_631, x_632);
lean::dec(x_631);
x_635 = l_lean_elaborator_to__pexpr___main___closed__26;
x_636 = l_lean_kvmap_set__name(x_612, x_635, x_633);
x_637 = lean_expr_mk_mdata(x_636, x_618);
if (lean::is_scalar(x_604)) {
 x_638 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_638 = x_604;
}
lean::cnstr_set(x_638, 0, x_637);
lean::cnstr_set(x_638, 1, x_602);
x_15 = x_638;
goto lbl_16;
}
}
}
}
else
{
obj* x_640; obj* x_641; obj* x_644; obj* x_645; obj* x_648; obj* x_649; obj* x_650; obj* x_652; 
lean::dec(x_511);
if (lean::is_exclusive(x_509)) {
 lean::cnstr_release(x_509, 0);
 lean::cnstr_release(x_509, 1);
 x_640 = x_509;
} else {
 lean::dec(x_509);
 x_640 = lean::box(0);
}
x_641 = lean::cnstr_get(x_219, 0);
lean::inc(x_641);
lean::dec(x_219);
x_644 = l_lean_parser_term_struct__inst__item_has__view;
x_645 = lean::cnstr_get(x_644, 1);
lean::inc(x_645);
lean::dec(x_644);
x_648 = lean::apply_1(x_645, x_346);
x_649 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_649, 0, x_648);
x_650 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_2);
x_652 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_649, x_650, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_649);
if (lean::obj_tag(x_652) == 0)
{
obj* x_662; obj* x_664; obj* x_665; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_640);
lean::dec(x_641);
lean::dec(x_214);
lean::dec(x_210);
x_662 = lean::cnstr_get(x_652, 0);
if (lean::is_exclusive(x_652)) {
 x_664 = x_652;
} else {
 lean::inc(x_662);
 lean::dec(x_652);
 x_664 = lean::box(0);
}
if (lean::is_scalar(x_664)) {
 x_665 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_665 = x_664;
}
lean::cnstr_set(x_665, 0, x_662);
return x_665;
}
else
{
obj* x_666; obj* x_669; obj* x_671; obj* x_676; 
x_666 = lean::cnstr_get(x_652, 0);
lean::inc(x_666);
lean::dec(x_652);
x_669 = lean::cnstr_get(x_666, 0);
lean::inc(x_669);
x_671 = lean::cnstr_get(x_666, 1);
lean::inc(x_671);
lean::dec(x_666);
lean::inc(x_2);
lean::inc(x_0);
x_676 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_214, x_1, x_2, x_671);
if (lean::obj_tag(x_676) == 0)
{
obj* x_684; obj* x_686; obj* x_687; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_669);
lean::dec(x_640);
lean::dec(x_641);
lean::dec(x_210);
x_684 = lean::cnstr_get(x_676, 0);
if (lean::is_exclusive(x_676)) {
 x_686 = x_676;
} else {
 lean::inc(x_684);
 lean::dec(x_676);
 x_686 = lean::box(0);
}
if (lean::is_scalar(x_686)) {
 x_687 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_687 = x_686;
}
lean::cnstr_set(x_687, 0, x_684);
return x_687;
}
else
{
obj* x_688; obj* x_691; obj* x_693; obj* x_696; obj* x_700; 
x_688 = lean::cnstr_get(x_676, 0);
lean::inc(x_688);
lean::dec(x_676);
x_691 = lean::cnstr_get(x_688, 0);
lean::inc(x_691);
x_693 = lean::cnstr_get(x_688, 1);
lean::inc(x_693);
lean::dec(x_688);
lean::inc(x_2);
lean::inc(x_0);
x_700 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__18(x_0, x_641, x_1, x_2, x_693);
if (lean::obj_tag(x_700) == 0)
{
obj* x_708; obj* x_710; obj* x_711; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_669);
lean::dec(x_691);
lean::dec(x_640);
lean::dec(x_210);
x_708 = lean::cnstr_get(x_700, 0);
if (lean::is_exclusive(x_700)) {
 x_710 = x_700;
} else {
 lean::inc(x_708);
 lean::dec(x_700);
 x_710 = lean::box(0);
}
if (lean::is_scalar(x_710)) {
 x_711 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_711 = x_710;
}
lean::cnstr_set(x_711, 0, x_708);
return x_711;
}
else
{
obj* x_712; obj* x_715; 
x_712 = lean::cnstr_get(x_700, 0);
lean::inc(x_712);
lean::dec(x_700);
x_715 = lean::cnstr_get(x_210, 2);
lean::inc(x_715);
if (lean::obj_tag(x_715) == 0)
{
obj* x_718; obj* x_720; obj* x_722; obj* x_723; 
lean::dec(x_640);
x_718 = lean::cnstr_get(x_712, 0);
x_720 = lean::cnstr_get(x_712, 1);
if (lean::is_exclusive(x_712)) {
 x_722 = x_712;
} else {
 lean::inc(x_718);
 lean::inc(x_720);
 lean::dec(x_712);
 x_722 = lean::box(0);
}
if (lean::is_scalar(x_722)) {
 x_723 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_723 = x_722;
}
lean::cnstr_set(x_723, 0, x_718);
lean::cnstr_set(x_723, 1, x_720);
x_696 = x_723;
goto lbl_697;
}
else
{
obj* x_724; obj* x_726; obj* x_729; obj* x_732; obj* x_736; 
x_724 = lean::cnstr_get(x_712, 0);
lean::inc(x_724);
x_726 = lean::cnstr_get(x_712, 1);
lean::inc(x_726);
lean::dec(x_712);
x_729 = lean::cnstr_get(x_715, 0);
lean::inc(x_729);
lean::dec(x_715);
x_732 = lean::cnstr_get(x_729, 0);
lean::inc(x_732);
lean::dec(x_729);
lean::inc(x_2);
x_736 = l_lean_elaborator_to__pexpr___main(x_732, x_1, x_2, x_726);
if (lean::obj_tag(x_736) == 0)
{
obj* x_745; obj* x_747; obj* x_748; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_669);
lean::dec(x_691);
lean::dec(x_640);
lean::dec(x_724);
lean::dec(x_210);
x_745 = lean::cnstr_get(x_736, 0);
if (lean::is_exclusive(x_736)) {
 x_747 = x_736;
} else {
 lean::inc(x_745);
 lean::dec(x_736);
 x_747 = lean::box(0);
}
if (lean::is_scalar(x_747)) {
 x_748 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_748 = x_747;
}
lean::cnstr_set(x_748, 0, x_745);
return x_748;
}
else
{
obj* x_749; obj* x_752; obj* x_754; obj* x_756; obj* x_757; obj* x_758; obj* x_759; obj* x_760; 
x_749 = lean::cnstr_get(x_736, 0);
lean::inc(x_749);
lean::dec(x_736);
x_752 = lean::cnstr_get(x_749, 0);
x_754 = lean::cnstr_get(x_749, 1);
if (lean::is_exclusive(x_749)) {
 x_756 = x_749;
} else {
 lean::inc(x_752);
 lean::inc(x_754);
 lean::dec(x_749);
 x_756 = lean::box(0);
}
x_757 = lean::box(0);
if (lean::is_scalar(x_640)) {
 x_758 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_758 = x_640;
}
lean::cnstr_set(x_758, 0, x_752);
lean::cnstr_set(x_758, 1, x_757);
x_759 = l_list_append___rarg(x_724, x_758);
if (lean::is_scalar(x_756)) {
 x_760 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_760 = x_756;
}
lean::cnstr_set(x_760, 0, x_759);
lean::cnstr_set(x_760, 1, x_754);
x_696 = x_760;
goto lbl_697;
}
}
}
lbl_697:
{
obj* x_761; obj* x_763; obj* x_765; obj* x_766; obj* x_767; obj* x_768; obj* x_769; obj* x_770; obj* x_771; uint8 x_772; obj* x_773; obj* x_774; obj* x_777; obj* x_778; obj* x_779; 
x_761 = lean::cnstr_get(x_696, 0);
x_763 = lean::cnstr_get(x_696, 1);
if (lean::is_exclusive(x_696)) {
 lean::cnstr_set(x_696, 0, lean::box(0));
 lean::cnstr_set(x_696, 1, lean::box(0));
 x_765 = x_696;
} else {
 lean::inc(x_761);
 lean::inc(x_763);
 lean::dec(x_696);
 x_765 = lean::box(0);
}
x_766 = lean::box(0);
x_767 = lean::mk_nat_obj(0u);
x_768 = l_list_length__aux___main___rarg(x_691, x_767);
x_769 = l_lean_elaborator_to__pexpr___main___closed__23;
x_770 = l_lean_kvmap_set__nat(x_766, x_769, x_768);
x_771 = l_lean_elaborator_to__pexpr___main___closed__24;
x_772 = lean::unbox(x_669);
x_773 = l_lean_kvmap_set__bool(x_770, x_771, x_772);
x_774 = lean::cnstr_get(x_210, 1);
lean::inc(x_774);
lean::dec(x_210);
x_777 = l_list_append___rarg(x_691, x_761);
x_778 = l_lean_elaborator_to__pexpr___main___closed__25;
x_779 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17(x_778, x_777);
if (lean::obj_tag(x_774) == 0)
{
obj* x_780; obj* x_781; obj* x_782; obj* x_783; obj* x_784; 
x_780 = l_lean_elaborator_to__pexpr___main___closed__26;
x_781 = l_lean_elaborator_to__pexpr___main___closed__27;
x_782 = l_lean_kvmap_set__name(x_773, x_780, x_781);
x_783 = lean_expr_mk_mdata(x_782, x_779);
if (lean::is_scalar(x_765)) {
 x_784 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_784 = x_765;
}
lean::cnstr_set(x_784, 0, x_783);
lean::cnstr_set(x_784, 1, x_763);
x_15 = x_784;
goto lbl_16;
}
else
{
obj* x_785; obj* x_787; obj* x_788; obj* x_791; obj* x_792; obj* x_793; obj* x_794; obj* x_796; obj* x_797; obj* x_798; obj* x_799; 
x_785 = lean::cnstr_get(x_774, 0);
if (lean::is_exclusive(x_774)) {
 x_787 = x_774;
} else {
 lean::inc(x_785);
 lean::dec(x_774);
 x_787 = lean::box(0);
}
x_788 = lean::cnstr_get(x_785, 0);
lean::inc(x_788);
lean::dec(x_785);
x_791 = l_lean_elaborator_mangle__ident(x_788);
if (lean::is_scalar(x_787)) {
 x_792 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_792 = x_787;
}
lean::cnstr_set(x_792, 0, x_791);
x_793 = lean::box(0);
x_794 = l_option_get__or__else___main___rarg(x_792, x_793);
lean::dec(x_792);
x_796 = l_lean_elaborator_to__pexpr___main___closed__26;
x_797 = l_lean_kvmap_set__name(x_773, x_796, x_794);
x_798 = lean_expr_mk_mdata(x_797, x_779);
if (lean::is_scalar(x_765)) {
 x_799 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_799 = x_765;
}
lean::cnstr_set(x_799, 0, x_798);
lean::cnstr_set(x_799, 1, x_763);
x_15 = x_799;
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
obj* x_802; 
lean::inc(x_2);
lean::inc(x_10);
x_802 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_802) == 0)
{
obj* x_807; obj* x_809; obj* x_810; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_2);
x_807 = lean::cnstr_get(x_802, 0);
if (lean::is_exclusive(x_802)) {
 x_809 = x_802;
} else {
 lean::inc(x_807);
 lean::dec(x_802);
 x_809 = lean::box(0);
}
if (lean::is_scalar(x_809)) {
 x_810 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_810 = x_809;
}
lean::cnstr_set(x_810, 0, x_807);
return x_810;
}
else
{
obj* x_811; obj* x_814; obj* x_816; obj* x_818; obj* x_819; 
x_811 = lean::cnstr_get(x_802, 0);
lean::inc(x_811);
lean::dec(x_802);
x_814 = lean::cnstr_get(x_811, 0);
x_816 = lean::cnstr_get(x_811, 1);
if (lean::is_exclusive(x_811)) {
 lean::cnstr_set(x_811, 0, lean::box(0));
 lean::cnstr_set(x_811, 1, lean::box(0));
 x_818 = x_811;
} else {
 lean::inc(x_814);
 lean::inc(x_816);
 lean::dec(x_811);
 x_818 = lean::box(0);
}
x_819 = l_list_reverse___rarg(x_814);
if (lean::obj_tag(x_819) == 0)
{
obj* x_823; obj* x_824; obj* x_826; 
lean::dec(x_818);
lean::dec(x_10);
lean::inc(x_0);
x_823 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_823, 0, x_0);
x_824 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_2);
x_826 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_823, x_824, x_1, x_2, x_816);
lean::dec(x_816);
lean::dec(x_823);
if (lean::obj_tag(x_826) == 0)
{
obj* x_832; obj* x_834; obj* x_835; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_832 = lean::cnstr_get(x_826, 0);
if (lean::is_exclusive(x_826)) {
 x_834 = x_826;
} else {
 lean::inc(x_832);
 lean::dec(x_826);
 x_834 = lean::box(0);
}
if (lean::is_scalar(x_834)) {
 x_835 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_835 = x_834;
}
lean::cnstr_set(x_835, 0, x_832);
return x_835;
}
else
{
obj* x_836; 
x_836 = lean::cnstr_get(x_826, 0);
lean::inc(x_836);
lean::dec(x_826);
x_15 = x_836;
goto lbl_16;
}
}
else
{
obj* x_839; obj* x_841; obj* x_844; obj* x_845; obj* x_846; obj* x_848; obj* x_849; obj* x_850; obj* x_851; obj* x_853; obj* x_854; 
x_839 = lean::cnstr_get(x_819, 0);
lean::inc(x_839);
x_841 = lean::cnstr_get(x_819, 1);
lean::inc(x_841);
lean::dec(x_819);
x_844 = lean::box(0);
x_845 = lean::mk_nat_obj(0u);
x_846 = l_list_length__aux___main___rarg(x_10, x_845);
lean::dec(x_10);
x_848 = l_lean_elaborator_to__pexpr___main___closed__30;
x_849 = l_lean_kvmap_set__nat(x_844, x_848, x_846);
x_850 = l_list_reverse___rarg(x_841);
x_851 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__20(x_839, x_850);
lean::dec(x_839);
x_853 = lean_expr_mk_mdata(x_849, x_851);
if (lean::is_scalar(x_818)) {
 x_854 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_854 = x_818;
}
lean::cnstr_set(x_854, 0, x_853);
lean::cnstr_set(x_854, 1, x_816);
x_15 = x_854;
goto lbl_16;
}
}
}
}
else
{
obj* x_857; obj* x_858; obj* x_862; obj* x_863; obj* x_864; obj* x_865; obj* x_867; obj* x_868; 
lean::dec(x_8);
lean::dec(x_10);
x_857 = l_lean_parser_string__lit_has__view;
x_858 = lean::cnstr_get(x_857, 0);
lean::inc(x_858);
lean::dec(x_857);
lean::inc(x_0);
x_862 = lean::apply_1(x_858, x_0);
x_863 = l_lean_parser_string__lit_view_value(x_862);
x_864 = l_lean_elaborator_to__pexpr___main___closed__31;
x_865 = l_option_get__or__else___main___rarg(x_863, x_864);
lean::dec(x_863);
x_867 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_867, 0, x_865);
x_868 = lean_expr_mk_lit(x_867);
if (x_20 == 0)
{
obj* x_869; 
x_869 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_869) == 0)
{
obj* x_872; obj* x_873; 
lean::dec(x_2);
x_872 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_872, 0, x_868);
lean::cnstr_set(x_872, 1, x_3);
x_873 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_873, 0, x_872);
return x_873;
}
else
{
obj* x_874; obj* x_877; obj* x_880; obj* x_883; obj* x_884; obj* x_885; obj* x_887; obj* x_888; obj* x_889; obj* x_892; obj* x_893; obj* x_894; obj* x_895; obj* x_896; 
x_874 = lean::cnstr_get(x_869, 0);
lean::inc(x_874);
lean::dec(x_869);
x_877 = lean::cnstr_get(x_2, 0);
lean::inc(x_877);
lean::dec(x_2);
x_880 = lean::cnstr_get(x_877, 2);
lean::inc(x_880);
lean::dec(x_877);
x_883 = l_lean_file__map_to__position(x_880, x_874);
x_884 = lean::box(0);
x_885 = lean::cnstr_get(x_883, 1);
lean::inc(x_885);
x_887 = l_lean_elaborator_to__pexpr___main___closed__3;
x_888 = l_lean_kvmap_set__nat(x_884, x_887, x_885);
x_889 = lean::cnstr_get(x_883, 0);
lean::inc(x_889);
lean::dec(x_883);
x_892 = l_lean_elaborator_to__pexpr___main___closed__4;
x_893 = l_lean_kvmap_set__nat(x_888, x_892, x_889);
x_894 = lean_expr_mk_mdata(x_893, x_868);
x_895 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_895, 0, x_894);
lean::cnstr_set(x_895, 1, x_3);
x_896 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_896, 0, x_895);
return x_896;
}
}
else
{
obj* x_899; obj* x_900; 
lean::dec(x_0);
lean::dec(x_2);
x_899 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_899, 0, x_868);
lean::cnstr_set(x_899, 1, x_3);
x_900 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_900, 0, x_899);
return x_900;
}
}
}
else
{
obj* x_903; obj* x_904; obj* x_908; obj* x_909; obj* x_910; obj* x_911; 
lean::dec(x_8);
lean::dec(x_10);
x_903 = l_lean_parser_number_has__view;
x_904 = lean::cnstr_get(x_903, 0);
lean::inc(x_904);
lean::dec(x_903);
lean::inc(x_0);
x_908 = lean::apply_1(x_904, x_0);
x_909 = l_lean_parser_number_view_to__nat___main(x_908);
x_910 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_910, 0, x_909);
x_911 = lean_expr_mk_lit(x_910);
if (x_20 == 0)
{
obj* x_912; 
x_912 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_912) == 0)
{
obj* x_915; obj* x_916; 
lean::dec(x_2);
x_915 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_915, 0, x_911);
lean::cnstr_set(x_915, 1, x_3);
x_916 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_916, 0, x_915);
return x_916;
}
else
{
obj* x_917; obj* x_920; obj* x_923; obj* x_926; obj* x_927; obj* x_928; obj* x_930; obj* x_931; obj* x_932; obj* x_935; obj* x_936; obj* x_937; obj* x_938; obj* x_939; 
x_917 = lean::cnstr_get(x_912, 0);
lean::inc(x_917);
lean::dec(x_912);
x_920 = lean::cnstr_get(x_2, 0);
lean::inc(x_920);
lean::dec(x_2);
x_923 = lean::cnstr_get(x_920, 2);
lean::inc(x_923);
lean::dec(x_920);
x_926 = l_lean_file__map_to__position(x_923, x_917);
x_927 = lean::box(0);
x_928 = lean::cnstr_get(x_926, 1);
lean::inc(x_928);
x_930 = l_lean_elaborator_to__pexpr___main___closed__3;
x_931 = l_lean_kvmap_set__nat(x_927, x_930, x_928);
x_932 = lean::cnstr_get(x_926, 0);
lean::inc(x_932);
lean::dec(x_926);
x_935 = l_lean_elaborator_to__pexpr___main___closed__4;
x_936 = l_lean_kvmap_set__nat(x_931, x_935, x_932);
x_937 = lean_expr_mk_mdata(x_936, x_911);
x_938 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_938, 0, x_937);
lean::cnstr_set(x_938, 1, x_3);
x_939 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_939, 0, x_938);
return x_939;
}
}
else
{
obj* x_942; obj* x_943; 
lean::dec(x_0);
lean::dec(x_2);
x_942 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_942, 0, x_911);
lean::cnstr_set(x_942, 1, x_3);
x_943 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_943, 0, x_942);
return x_943;
}
}
}
else
{
obj* x_946; obj* x_947; obj* x_951; obj* x_952; obj* x_956; 
lean::dec(x_8);
lean::dec(x_10);
x_946 = l_lean_parser_term_borrowed_has__view;
x_947 = lean::cnstr_get(x_946, 0);
lean::inc(x_947);
lean::dec(x_946);
lean::inc(x_0);
x_951 = lean::apply_1(x_947, x_0);
x_952 = lean::cnstr_get(x_951, 1);
lean::inc(x_952);
lean::dec(x_951);
lean::inc(x_2);
x_956 = l_lean_elaborator_to__pexpr___main(x_952, x_1, x_2, x_3);
if (lean::obj_tag(x_956) == 0)
{
obj* x_959; obj* x_961; obj* x_962; 
lean::dec(x_0);
lean::dec(x_2);
x_959 = lean::cnstr_get(x_956, 0);
if (lean::is_exclusive(x_956)) {
 x_961 = x_956;
} else {
 lean::inc(x_959);
 lean::dec(x_956);
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
obj* x_963; obj* x_965; obj* x_966; obj* x_968; obj* x_970; obj* x_971; obj* x_972; 
x_963 = lean::cnstr_get(x_956, 0);
if (lean::is_exclusive(x_956)) {
 lean::cnstr_set(x_956, 0, lean::box(0));
 x_965 = x_956;
} else {
 lean::inc(x_963);
 lean::dec(x_956);
 x_965 = lean::box(0);
}
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
x_971 = l_lean_elaborator_to__pexpr___main___closed__32;
x_972 = l_lean_elaborator_expr_mk__annotation(x_971, x_966);
if (x_20 == 0)
{
obj* x_973; 
x_973 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_973) == 0)
{
obj* x_976; obj* x_977; 
lean::dec(x_2);
if (lean::is_scalar(x_970)) {
 x_976 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_976 = x_970;
}
lean::cnstr_set(x_976, 0, x_972);
lean::cnstr_set(x_976, 1, x_968);
if (lean::is_scalar(x_965)) {
 x_977 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_977 = x_965;
}
lean::cnstr_set(x_977, 0, x_976);
return x_977;
}
else
{
obj* x_978; obj* x_981; obj* x_984; obj* x_987; obj* x_988; obj* x_989; obj* x_991; obj* x_992; obj* x_993; obj* x_996; obj* x_997; obj* x_998; obj* x_999; obj* x_1000; 
x_978 = lean::cnstr_get(x_973, 0);
lean::inc(x_978);
lean::dec(x_973);
x_981 = lean::cnstr_get(x_2, 0);
lean::inc(x_981);
lean::dec(x_2);
x_984 = lean::cnstr_get(x_981, 2);
lean::inc(x_984);
lean::dec(x_981);
x_987 = l_lean_file__map_to__position(x_984, x_978);
x_988 = lean::box(0);
x_989 = lean::cnstr_get(x_987, 1);
lean::inc(x_989);
x_991 = l_lean_elaborator_to__pexpr___main___closed__3;
x_992 = l_lean_kvmap_set__nat(x_988, x_991, x_989);
x_993 = lean::cnstr_get(x_987, 0);
lean::inc(x_993);
lean::dec(x_987);
x_996 = l_lean_elaborator_to__pexpr___main___closed__4;
x_997 = l_lean_kvmap_set__nat(x_992, x_996, x_993);
x_998 = lean_expr_mk_mdata(x_997, x_972);
if (lean::is_scalar(x_970)) {
 x_999 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_999 = x_970;
}
lean::cnstr_set(x_999, 0, x_998);
lean::cnstr_set(x_999, 1, x_968);
if (lean::is_scalar(x_965)) {
 x_1000 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1000 = x_965;
}
lean::cnstr_set(x_1000, 0, x_999);
return x_1000;
}
}
else
{
obj* x_1003; obj* x_1004; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_970)) {
 x_1003 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1003 = x_970;
}
lean::cnstr_set(x_1003, 0, x_972);
lean::cnstr_set(x_1003, 1, x_968);
if (lean::is_scalar(x_965)) {
 x_1004 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1004 = x_965;
}
lean::cnstr_set(x_1004, 0, x_1003);
return x_1004;
}
}
}
}
else
{
obj* x_1007; obj* x_1008; obj* x_1012; obj* x_1013; obj* x_1017; 
lean::dec(x_8);
lean::dec(x_10);
x_1007 = l_lean_parser_term_inaccessible_has__view;
x_1008 = lean::cnstr_get(x_1007, 0);
lean::inc(x_1008);
lean::dec(x_1007);
lean::inc(x_0);
x_1012 = lean::apply_1(x_1008, x_0);
x_1013 = lean::cnstr_get(x_1012, 1);
lean::inc(x_1013);
lean::dec(x_1012);
lean::inc(x_2);
x_1017 = l_lean_elaborator_to__pexpr___main(x_1013, x_1, x_2, x_3);
if (lean::obj_tag(x_1017) == 0)
{
obj* x_1020; obj* x_1022; obj* x_1023; 
lean::dec(x_0);
lean::dec(x_2);
x_1020 = lean::cnstr_get(x_1017, 0);
if (lean::is_exclusive(x_1017)) {
 x_1022 = x_1017;
} else {
 lean::inc(x_1020);
 lean::dec(x_1017);
 x_1022 = lean::box(0);
}
if (lean::is_scalar(x_1022)) {
 x_1023 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1023 = x_1022;
}
lean::cnstr_set(x_1023, 0, x_1020);
return x_1023;
}
else
{
obj* x_1024; obj* x_1026; obj* x_1027; obj* x_1029; obj* x_1031; obj* x_1032; obj* x_1033; 
x_1024 = lean::cnstr_get(x_1017, 0);
if (lean::is_exclusive(x_1017)) {
 lean::cnstr_set(x_1017, 0, lean::box(0));
 x_1026 = x_1017;
} else {
 lean::inc(x_1024);
 lean::dec(x_1017);
 x_1026 = lean::box(0);
}
x_1027 = lean::cnstr_get(x_1024, 0);
x_1029 = lean::cnstr_get(x_1024, 1);
if (lean::is_exclusive(x_1024)) {
 lean::cnstr_set(x_1024, 0, lean::box(0));
 lean::cnstr_set(x_1024, 1, lean::box(0));
 x_1031 = x_1024;
} else {
 lean::inc(x_1027);
 lean::inc(x_1029);
 lean::dec(x_1024);
 x_1031 = lean::box(0);
}
x_1032 = l_lean_elaborator_to__pexpr___main___closed__33;
x_1033 = l_lean_elaborator_expr_mk__annotation(x_1032, x_1027);
if (x_20 == 0)
{
obj* x_1034; 
x_1034 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1034) == 0)
{
obj* x_1037; obj* x_1038; 
lean::dec(x_2);
if (lean::is_scalar(x_1031)) {
 x_1037 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1037 = x_1031;
}
lean::cnstr_set(x_1037, 0, x_1033);
lean::cnstr_set(x_1037, 1, x_1029);
if (lean::is_scalar(x_1026)) {
 x_1038 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1038 = x_1026;
}
lean::cnstr_set(x_1038, 0, x_1037);
return x_1038;
}
else
{
obj* x_1039; obj* x_1042; obj* x_1045; obj* x_1048; obj* x_1049; obj* x_1050; obj* x_1052; obj* x_1053; obj* x_1054; obj* x_1057; obj* x_1058; obj* x_1059; obj* x_1060; obj* x_1061; 
x_1039 = lean::cnstr_get(x_1034, 0);
lean::inc(x_1039);
lean::dec(x_1034);
x_1042 = lean::cnstr_get(x_2, 0);
lean::inc(x_1042);
lean::dec(x_2);
x_1045 = lean::cnstr_get(x_1042, 2);
lean::inc(x_1045);
lean::dec(x_1042);
x_1048 = l_lean_file__map_to__position(x_1045, x_1039);
x_1049 = lean::box(0);
x_1050 = lean::cnstr_get(x_1048, 1);
lean::inc(x_1050);
x_1052 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1053 = l_lean_kvmap_set__nat(x_1049, x_1052, x_1050);
x_1054 = lean::cnstr_get(x_1048, 0);
lean::inc(x_1054);
lean::dec(x_1048);
x_1057 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1058 = l_lean_kvmap_set__nat(x_1053, x_1057, x_1054);
x_1059 = lean_expr_mk_mdata(x_1058, x_1033);
if (lean::is_scalar(x_1031)) {
 x_1060 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1060 = x_1031;
}
lean::cnstr_set(x_1060, 0, x_1059);
lean::cnstr_set(x_1060, 1, x_1029);
if (lean::is_scalar(x_1026)) {
 x_1061 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1061 = x_1026;
}
lean::cnstr_set(x_1061, 0, x_1060);
return x_1061;
}
}
else
{
obj* x_1064; obj* x_1065; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1031)) {
 x_1064 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1064 = x_1031;
}
lean::cnstr_set(x_1064, 0, x_1033);
lean::cnstr_set(x_1064, 1, x_1029);
if (lean::is_scalar(x_1026)) {
 x_1065 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1065 = x_1026;
}
lean::cnstr_set(x_1065, 0, x_1064);
return x_1065;
}
}
}
}
else
{
obj* x_1068; obj* x_1069; obj* x_1073; obj* x_1074; obj* x_1076; obj* x_1077; obj* x_1080; obj* x_1083; 
lean::dec(x_8);
lean::dec(x_10);
x_1068 = l_lean_parser_term_explicit_has__view;
x_1069 = lean::cnstr_get(x_1068, 0);
lean::inc(x_1069);
lean::dec(x_1068);
lean::inc(x_0);
x_1073 = lean::apply_1(x_1069, x_0);
x_1074 = lean::cnstr_get(x_1073, 0);
lean::inc(x_1074);
x_1076 = l_lean_parser_ident__univs_has__view;
x_1077 = lean::cnstr_get(x_1076, 1);
lean::inc(x_1077);
lean::dec(x_1076);
x_1080 = lean::cnstr_get(x_1073, 1);
lean::inc(x_1080);
lean::dec(x_1073);
x_1083 = lean::apply_1(x_1077, x_1080);
if (lean::obj_tag(x_1074) == 0)
{
obj* x_1086; 
lean::dec(x_1074);
lean::inc(x_2);
x_1086 = l_lean_elaborator_to__pexpr___main(x_1083, x_1, x_2, x_3);
if (lean::obj_tag(x_1086) == 0)
{
obj* x_1089; obj* x_1091; obj* x_1092; 
lean::dec(x_0);
lean::dec(x_2);
x_1089 = lean::cnstr_get(x_1086, 0);
if (lean::is_exclusive(x_1086)) {
 x_1091 = x_1086;
} else {
 lean::inc(x_1089);
 lean::dec(x_1086);
 x_1091 = lean::box(0);
}
if (lean::is_scalar(x_1091)) {
 x_1092 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1092 = x_1091;
}
lean::cnstr_set(x_1092, 0, x_1089);
return x_1092;
}
else
{
obj* x_1093; obj* x_1095; obj* x_1096; obj* x_1098; obj* x_1100; obj* x_1101; obj* x_1102; 
x_1093 = lean::cnstr_get(x_1086, 0);
if (lean::is_exclusive(x_1086)) {
 lean::cnstr_set(x_1086, 0, lean::box(0));
 x_1095 = x_1086;
} else {
 lean::inc(x_1093);
 lean::dec(x_1086);
 x_1095 = lean::box(0);
}
x_1096 = lean::cnstr_get(x_1093, 0);
x_1098 = lean::cnstr_get(x_1093, 1);
if (lean::is_exclusive(x_1093)) {
 lean::cnstr_set(x_1093, 0, lean::box(0));
 lean::cnstr_set(x_1093, 1, lean::box(0));
 x_1100 = x_1093;
} else {
 lean::inc(x_1096);
 lean::inc(x_1098);
 lean::dec(x_1093);
 x_1100 = lean::box(0);
}
x_1101 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
x_1102 = l_lean_elaborator_expr_mk__annotation(x_1101, x_1096);
if (x_20 == 0)
{
obj* x_1103; 
x_1103 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1103) == 0)
{
obj* x_1106; obj* x_1107; 
lean::dec(x_2);
if (lean::is_scalar(x_1100)) {
 x_1106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1106 = x_1100;
}
lean::cnstr_set(x_1106, 0, x_1102);
lean::cnstr_set(x_1106, 1, x_1098);
if (lean::is_scalar(x_1095)) {
 x_1107 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1107 = x_1095;
}
lean::cnstr_set(x_1107, 0, x_1106);
return x_1107;
}
else
{
obj* x_1108; obj* x_1111; obj* x_1114; obj* x_1117; obj* x_1118; obj* x_1119; obj* x_1121; obj* x_1122; obj* x_1123; obj* x_1126; obj* x_1127; obj* x_1128; obj* x_1129; obj* x_1130; 
x_1108 = lean::cnstr_get(x_1103, 0);
lean::inc(x_1108);
lean::dec(x_1103);
x_1111 = lean::cnstr_get(x_2, 0);
lean::inc(x_1111);
lean::dec(x_2);
x_1114 = lean::cnstr_get(x_1111, 2);
lean::inc(x_1114);
lean::dec(x_1111);
x_1117 = l_lean_file__map_to__position(x_1114, x_1108);
x_1118 = lean::box(0);
x_1119 = lean::cnstr_get(x_1117, 1);
lean::inc(x_1119);
x_1121 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1122 = l_lean_kvmap_set__nat(x_1118, x_1121, x_1119);
x_1123 = lean::cnstr_get(x_1117, 0);
lean::inc(x_1123);
lean::dec(x_1117);
x_1126 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1127 = l_lean_kvmap_set__nat(x_1122, x_1126, x_1123);
x_1128 = lean_expr_mk_mdata(x_1127, x_1102);
if (lean::is_scalar(x_1100)) {
 x_1129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1129 = x_1100;
}
lean::cnstr_set(x_1129, 0, x_1128);
lean::cnstr_set(x_1129, 1, x_1098);
if (lean::is_scalar(x_1095)) {
 x_1130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1130 = x_1095;
}
lean::cnstr_set(x_1130, 0, x_1129);
return x_1130;
}
}
else
{
obj* x_1133; obj* x_1134; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1100)) {
 x_1133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1133 = x_1100;
}
lean::cnstr_set(x_1133, 0, x_1102);
lean::cnstr_set(x_1133, 1, x_1098);
if (lean::is_scalar(x_1095)) {
 x_1134 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1134 = x_1095;
}
lean::cnstr_set(x_1134, 0, x_1133);
return x_1134;
}
}
}
else
{
obj* x_1137; 
lean::dec(x_1074);
lean::inc(x_2);
x_1137 = l_lean_elaborator_to__pexpr___main(x_1083, x_1, x_2, x_3);
if (lean::obj_tag(x_1137) == 0)
{
obj* x_1140; obj* x_1142; obj* x_1143; 
lean::dec(x_0);
lean::dec(x_2);
x_1140 = lean::cnstr_get(x_1137, 0);
if (lean::is_exclusive(x_1137)) {
 x_1142 = x_1137;
} else {
 lean::inc(x_1140);
 lean::dec(x_1137);
 x_1142 = lean::box(0);
}
if (lean::is_scalar(x_1142)) {
 x_1143 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1143 = x_1142;
}
lean::cnstr_set(x_1143, 0, x_1140);
return x_1143;
}
else
{
obj* x_1144; obj* x_1146; obj* x_1147; obj* x_1149; obj* x_1151; obj* x_1152; obj* x_1153; 
x_1144 = lean::cnstr_get(x_1137, 0);
if (lean::is_exclusive(x_1137)) {
 lean::cnstr_set(x_1137, 0, lean::box(0));
 x_1146 = x_1137;
} else {
 lean::inc(x_1144);
 lean::dec(x_1137);
 x_1146 = lean::box(0);
}
x_1147 = lean::cnstr_get(x_1144, 0);
x_1149 = lean::cnstr_get(x_1144, 1);
if (lean::is_exclusive(x_1144)) {
 lean::cnstr_set(x_1144, 0, lean::box(0));
 lean::cnstr_set(x_1144, 1, lean::box(0));
 x_1151 = x_1144;
} else {
 lean::inc(x_1147);
 lean::inc(x_1149);
 lean::dec(x_1144);
 x_1151 = lean::box(0);
}
x_1152 = l_lean_elaborator_to__pexpr___main___closed__34;
x_1153 = l_lean_elaborator_expr_mk__annotation(x_1152, x_1147);
if (x_20 == 0)
{
obj* x_1154; 
x_1154 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1154) == 0)
{
obj* x_1157; obj* x_1158; 
lean::dec(x_2);
if (lean::is_scalar(x_1151)) {
 x_1157 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1157 = x_1151;
}
lean::cnstr_set(x_1157, 0, x_1153);
lean::cnstr_set(x_1157, 1, x_1149);
if (lean::is_scalar(x_1146)) {
 x_1158 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1158 = x_1146;
}
lean::cnstr_set(x_1158, 0, x_1157);
return x_1158;
}
else
{
obj* x_1159; obj* x_1162; obj* x_1165; obj* x_1168; obj* x_1169; obj* x_1170; obj* x_1172; obj* x_1173; obj* x_1174; obj* x_1177; obj* x_1178; obj* x_1179; obj* x_1180; obj* x_1181; 
x_1159 = lean::cnstr_get(x_1154, 0);
lean::inc(x_1159);
lean::dec(x_1154);
x_1162 = lean::cnstr_get(x_2, 0);
lean::inc(x_1162);
lean::dec(x_2);
x_1165 = lean::cnstr_get(x_1162, 2);
lean::inc(x_1165);
lean::dec(x_1162);
x_1168 = l_lean_file__map_to__position(x_1165, x_1159);
x_1169 = lean::box(0);
x_1170 = lean::cnstr_get(x_1168, 1);
lean::inc(x_1170);
x_1172 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1173 = l_lean_kvmap_set__nat(x_1169, x_1172, x_1170);
x_1174 = lean::cnstr_get(x_1168, 0);
lean::inc(x_1174);
lean::dec(x_1168);
x_1177 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1178 = l_lean_kvmap_set__nat(x_1173, x_1177, x_1174);
x_1179 = lean_expr_mk_mdata(x_1178, x_1153);
if (lean::is_scalar(x_1151)) {
 x_1180 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1180 = x_1151;
}
lean::cnstr_set(x_1180, 0, x_1179);
lean::cnstr_set(x_1180, 1, x_1149);
if (lean::is_scalar(x_1146)) {
 x_1181 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1181 = x_1146;
}
lean::cnstr_set(x_1181, 0, x_1180);
return x_1181;
}
}
else
{
obj* x_1184; obj* x_1185; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1151)) {
 x_1184 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1184 = x_1151;
}
lean::cnstr_set(x_1184, 0, x_1153);
lean::cnstr_set(x_1184, 1, x_1149);
if (lean::is_scalar(x_1146)) {
 x_1185 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1185 = x_1146;
}
lean::cnstr_set(x_1185, 0, x_1184);
return x_1185;
}
}
}
}
}
else
{
obj* x_1188; obj* x_1189; obj* x_1193; obj* x_1194; 
lean::dec(x_8);
lean::dec(x_10);
x_1188 = l_lean_parser_term_projection_has__view;
x_1189 = lean::cnstr_get(x_1188, 0);
lean::inc(x_1189);
lean::dec(x_1188);
lean::inc(x_0);
x_1193 = lean::apply_1(x_1189, x_0);
x_1194 = lean::cnstr_get(x_1193, 2);
lean::inc(x_1194);
if (lean::obj_tag(x_1194) == 0)
{
obj* x_1196; obj* x_1199; obj* x_1203; 
x_1196 = lean::cnstr_get(x_1193, 0);
lean::inc(x_1196);
lean::dec(x_1193);
x_1199 = lean::cnstr_get(x_1194, 0);
lean::inc(x_1199);
lean::dec(x_1194);
lean::inc(x_2);
x_1203 = l_lean_elaborator_to__pexpr___main(x_1196, x_1, x_2, x_3);
if (lean::obj_tag(x_1203) == 0)
{
obj* x_1207; obj* x_1209; obj* x_1210; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1199);
x_1207 = lean::cnstr_get(x_1203, 0);
if (lean::is_exclusive(x_1203)) {
 x_1209 = x_1203;
} else {
 lean::inc(x_1207);
 lean::dec(x_1203);
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
obj* x_1211; obj* x_1213; obj* x_1214; obj* x_1216; obj* x_1218; obj* x_1219; obj* x_1222; obj* x_1223; obj* x_1224; obj* x_1225; obj* x_1226; 
x_1211 = lean::cnstr_get(x_1203, 0);
if (lean::is_exclusive(x_1203)) {
 lean::cnstr_set(x_1203, 0, lean::box(0));
 x_1213 = x_1203;
} else {
 lean::inc(x_1211);
 lean::dec(x_1203);
 x_1213 = lean::box(0);
}
x_1214 = lean::cnstr_get(x_1211, 0);
x_1216 = lean::cnstr_get(x_1211, 1);
if (lean::is_exclusive(x_1211)) {
 lean::cnstr_set(x_1211, 0, lean::box(0));
 lean::cnstr_set(x_1211, 1, lean::box(0));
 x_1218 = x_1211;
} else {
 lean::inc(x_1214);
 lean::inc(x_1216);
 lean::dec(x_1211);
 x_1218 = lean::box(0);
}
x_1219 = lean::cnstr_get(x_1199, 2);
lean::inc(x_1219);
lean::dec(x_1199);
x_1222 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1222, 0, x_1219);
x_1223 = lean::box(0);
x_1224 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1225 = l_lean_kvmap_insert__core___main(x_1223, x_1224, x_1222);
x_1226 = lean_expr_mk_mdata(x_1225, x_1214);
if (x_20 == 0)
{
obj* x_1227; 
x_1227 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1227) == 0)
{
obj* x_1230; obj* x_1231; 
lean::dec(x_2);
if (lean::is_scalar(x_1218)) {
 x_1230 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1230 = x_1218;
}
lean::cnstr_set(x_1230, 0, x_1226);
lean::cnstr_set(x_1230, 1, x_1216);
if (lean::is_scalar(x_1213)) {
 x_1231 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1231 = x_1213;
}
lean::cnstr_set(x_1231, 0, x_1230);
return x_1231;
}
else
{
obj* x_1232; obj* x_1235; obj* x_1238; obj* x_1241; obj* x_1242; obj* x_1244; obj* x_1245; obj* x_1246; obj* x_1249; obj* x_1250; obj* x_1251; obj* x_1252; obj* x_1253; 
x_1232 = lean::cnstr_get(x_1227, 0);
lean::inc(x_1232);
lean::dec(x_1227);
x_1235 = lean::cnstr_get(x_2, 0);
lean::inc(x_1235);
lean::dec(x_2);
x_1238 = lean::cnstr_get(x_1235, 2);
lean::inc(x_1238);
lean::dec(x_1235);
x_1241 = l_lean_file__map_to__position(x_1238, x_1232);
x_1242 = lean::cnstr_get(x_1241, 1);
lean::inc(x_1242);
x_1244 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1245 = l_lean_kvmap_set__nat(x_1223, x_1244, x_1242);
x_1246 = lean::cnstr_get(x_1241, 0);
lean::inc(x_1246);
lean::dec(x_1241);
x_1249 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1250 = l_lean_kvmap_set__nat(x_1245, x_1249, x_1246);
x_1251 = lean_expr_mk_mdata(x_1250, x_1226);
if (lean::is_scalar(x_1218)) {
 x_1252 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1252 = x_1218;
}
lean::cnstr_set(x_1252, 0, x_1251);
lean::cnstr_set(x_1252, 1, x_1216);
if (lean::is_scalar(x_1213)) {
 x_1253 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1253 = x_1213;
}
lean::cnstr_set(x_1253, 0, x_1252);
return x_1253;
}
}
else
{
obj* x_1256; obj* x_1257; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1218)) {
 x_1256 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1256 = x_1218;
}
lean::cnstr_set(x_1256, 0, x_1226);
lean::cnstr_set(x_1256, 1, x_1216);
if (lean::is_scalar(x_1213)) {
 x_1257 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1257 = x_1213;
}
lean::cnstr_set(x_1257, 0, x_1256);
return x_1257;
}
}
}
else
{
obj* x_1258; obj* x_1261; obj* x_1265; 
x_1258 = lean::cnstr_get(x_1193, 0);
lean::inc(x_1258);
lean::dec(x_1193);
x_1261 = lean::cnstr_get(x_1194, 0);
lean::inc(x_1261);
lean::dec(x_1194);
lean::inc(x_2);
x_1265 = l_lean_elaborator_to__pexpr___main(x_1258, x_1, x_2, x_3);
if (lean::obj_tag(x_1265) == 0)
{
obj* x_1269; obj* x_1271; obj* x_1272; 
lean::dec(x_1261);
lean::dec(x_0);
lean::dec(x_2);
x_1269 = lean::cnstr_get(x_1265, 0);
if (lean::is_exclusive(x_1265)) {
 x_1271 = x_1265;
} else {
 lean::inc(x_1269);
 lean::dec(x_1265);
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
obj* x_1273; obj* x_1275; obj* x_1276; obj* x_1278; obj* x_1280; obj* x_1281; obj* x_1282; obj* x_1283; obj* x_1284; obj* x_1285; obj* x_1286; 
x_1273 = lean::cnstr_get(x_1265, 0);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_set(x_1265, 0, lean::box(0));
 x_1275 = x_1265;
} else {
 lean::inc(x_1273);
 lean::dec(x_1265);
 x_1275 = lean::box(0);
}
x_1276 = lean::cnstr_get(x_1273, 0);
x_1278 = lean::cnstr_get(x_1273, 1);
if (lean::is_exclusive(x_1273)) {
 lean::cnstr_set(x_1273, 0, lean::box(0));
 lean::cnstr_set(x_1273, 1, lean::box(0));
 x_1280 = x_1273;
} else {
 lean::inc(x_1276);
 lean::inc(x_1278);
 lean::dec(x_1273);
 x_1280 = lean::box(0);
}
x_1281 = l_lean_parser_number_view_to__nat___main(x_1261);
x_1282 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1282, 0, x_1281);
x_1283 = lean::box(0);
x_1284 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1285 = l_lean_kvmap_insert__core___main(x_1283, x_1284, x_1282);
x_1286 = lean_expr_mk_mdata(x_1285, x_1276);
if (x_20 == 0)
{
obj* x_1287; 
x_1287 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1287) == 0)
{
obj* x_1290; obj* x_1291; 
lean::dec(x_2);
if (lean::is_scalar(x_1280)) {
 x_1290 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1290 = x_1280;
}
lean::cnstr_set(x_1290, 0, x_1286);
lean::cnstr_set(x_1290, 1, x_1278);
if (lean::is_scalar(x_1275)) {
 x_1291 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1291 = x_1275;
}
lean::cnstr_set(x_1291, 0, x_1290);
return x_1291;
}
else
{
obj* x_1292; obj* x_1295; obj* x_1298; obj* x_1301; obj* x_1302; obj* x_1304; obj* x_1305; obj* x_1306; obj* x_1309; obj* x_1310; obj* x_1311; obj* x_1312; obj* x_1313; 
x_1292 = lean::cnstr_get(x_1287, 0);
lean::inc(x_1292);
lean::dec(x_1287);
x_1295 = lean::cnstr_get(x_2, 0);
lean::inc(x_1295);
lean::dec(x_2);
x_1298 = lean::cnstr_get(x_1295, 2);
lean::inc(x_1298);
lean::dec(x_1295);
x_1301 = l_lean_file__map_to__position(x_1298, x_1292);
x_1302 = lean::cnstr_get(x_1301, 1);
lean::inc(x_1302);
x_1304 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1305 = l_lean_kvmap_set__nat(x_1283, x_1304, x_1302);
x_1306 = lean::cnstr_get(x_1301, 0);
lean::inc(x_1306);
lean::dec(x_1301);
x_1309 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1310 = l_lean_kvmap_set__nat(x_1305, x_1309, x_1306);
x_1311 = lean_expr_mk_mdata(x_1310, x_1286);
if (lean::is_scalar(x_1280)) {
 x_1312 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1312 = x_1280;
}
lean::cnstr_set(x_1312, 0, x_1311);
lean::cnstr_set(x_1312, 1, x_1278);
if (lean::is_scalar(x_1275)) {
 x_1313 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1313 = x_1275;
}
lean::cnstr_set(x_1313, 0, x_1312);
return x_1313;
}
}
else
{
obj* x_1316; obj* x_1317; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1280)) {
 x_1316 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1316 = x_1280;
}
lean::cnstr_set(x_1316, 0, x_1286);
lean::cnstr_set(x_1316, 1, x_1278);
if (lean::is_scalar(x_1275)) {
 x_1317 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1317 = x_1275;
}
lean::cnstr_set(x_1317, 0, x_1316);
return x_1317;
}
}
}
}
}
else
{
obj* x_1319; obj* x_1320; obj* x_1324; obj* x_1325; 
lean::dec(x_10);
x_1319 = l_lean_parser_term_let_has__view;
x_1320 = lean::cnstr_get(x_1319, 0);
lean::inc(x_1320);
lean::dec(x_1319);
lean::inc(x_0);
x_1324 = lean::apply_1(x_1320, x_0);
x_1325 = lean::cnstr_get(x_1324, 1);
lean::inc(x_1325);
if (lean::obj_tag(x_1325) == 0)
{
obj* x_1327; obj* x_1330; 
x_1327 = lean::cnstr_get(x_1325, 0);
lean::inc(x_1327);
lean::dec(x_1325);
x_1330 = lean::cnstr_get(x_1327, 1);
lean::inc(x_1330);
if (lean::obj_tag(x_1330) == 0)
{
obj* x_1332; 
x_1332 = lean::cnstr_get(x_1327, 2);
lean::inc(x_1332);
if (lean::obj_tag(x_1332) == 0)
{
obj* x_1337; obj* x_1338; obj* x_1340; 
lean::dec(x_1327);
lean::dec(x_1324);
lean::inc(x_0);
x_1337 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1337, 0, x_0);
x_1338 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_2);
x_1340 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_1337, x_1338, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1337);
if (lean::obj_tag(x_1340) == 0)
{
obj* x_1346; obj* x_1348; obj* x_1349; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1346 = lean::cnstr_get(x_1340, 0);
if (lean::is_exclusive(x_1340)) {
 x_1348 = x_1340;
} else {
 lean::inc(x_1346);
 lean::dec(x_1340);
 x_1348 = lean::box(0);
}
if (lean::is_scalar(x_1348)) {
 x_1349 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1349 = x_1348;
}
lean::cnstr_set(x_1349, 0, x_1346);
return x_1349;
}
else
{
obj* x_1350; 
x_1350 = lean::cnstr_get(x_1340, 0);
lean::inc(x_1350);
lean::dec(x_1340);
x_15 = x_1350;
goto lbl_16;
}
}
else
{
obj* x_1353; obj* x_1356; obj* x_1359; obj* x_1363; 
x_1353 = lean::cnstr_get(x_1327, 0);
lean::inc(x_1353);
lean::dec(x_1327);
x_1356 = lean::cnstr_get(x_1332, 0);
lean::inc(x_1356);
lean::dec(x_1332);
x_1359 = lean::cnstr_get(x_1356, 1);
lean::inc(x_1359);
lean::dec(x_1356);
lean::inc(x_2);
x_1363 = l_lean_elaborator_to__pexpr___main(x_1359, x_1, x_2, x_3);
if (lean::obj_tag(x_1363) == 0)
{
obj* x_1369; obj* x_1371; obj* x_1372; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1353);
lean::dec(x_1324);
x_1369 = lean::cnstr_get(x_1363, 0);
if (lean::is_exclusive(x_1363)) {
 x_1371 = x_1363;
} else {
 lean::inc(x_1369);
 lean::dec(x_1363);
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
obj* x_1373; obj* x_1376; obj* x_1378; obj* x_1381; obj* x_1384; 
x_1373 = lean::cnstr_get(x_1363, 0);
lean::inc(x_1373);
lean::dec(x_1363);
x_1376 = lean::cnstr_get(x_1373, 0);
lean::inc(x_1376);
x_1378 = lean::cnstr_get(x_1373, 1);
lean::inc(x_1378);
lean::dec(x_1373);
x_1381 = lean::cnstr_get(x_1324, 3);
lean::inc(x_1381);
lean::inc(x_2);
x_1384 = l_lean_elaborator_to__pexpr___main(x_1381, x_1, x_2, x_1378);
if (lean::obj_tag(x_1384) == 0)
{
obj* x_1391; obj* x_1393; obj* x_1394; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1376);
lean::dec(x_1353);
lean::dec(x_1324);
x_1391 = lean::cnstr_get(x_1384, 0);
if (lean::is_exclusive(x_1384)) {
 x_1393 = x_1384;
} else {
 lean::inc(x_1391);
 lean::dec(x_1384);
 x_1393 = lean::box(0);
}
if (lean::is_scalar(x_1393)) {
 x_1394 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1394 = x_1393;
}
lean::cnstr_set(x_1394, 0, x_1391);
return x_1394;
}
else
{
obj* x_1395; obj* x_1398; obj* x_1400; obj* x_1403; obj* x_1407; 
x_1395 = lean::cnstr_get(x_1384, 0);
lean::inc(x_1395);
lean::dec(x_1384);
x_1398 = lean::cnstr_get(x_1395, 0);
lean::inc(x_1398);
x_1400 = lean::cnstr_get(x_1395, 1);
lean::inc(x_1400);
lean::dec(x_1395);
x_1403 = lean::cnstr_get(x_1324, 5);
lean::inc(x_1403);
lean::dec(x_1324);
lean::inc(x_2);
x_1407 = l_lean_elaborator_to__pexpr___main(x_1403, x_1, x_2, x_1400);
if (lean::obj_tag(x_1407) == 0)
{
obj* x_1414; obj* x_1416; obj* x_1417; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1376);
lean::dec(x_1353);
lean::dec(x_1398);
x_1414 = lean::cnstr_get(x_1407, 0);
if (lean::is_exclusive(x_1407)) {
 x_1416 = x_1407;
} else {
 lean::inc(x_1414);
 lean::dec(x_1407);
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
obj* x_1418; obj* x_1421; obj* x_1423; obj* x_1425; obj* x_1426; obj* x_1427; obj* x_1428; 
x_1418 = lean::cnstr_get(x_1407, 0);
lean::inc(x_1418);
lean::dec(x_1407);
x_1421 = lean::cnstr_get(x_1418, 0);
x_1423 = lean::cnstr_get(x_1418, 1);
if (lean::is_exclusive(x_1418)) {
 x_1425 = x_1418;
} else {
 lean::inc(x_1421);
 lean::inc(x_1423);
 lean::dec(x_1418);
 x_1425 = lean::box(0);
}
x_1426 = l_lean_elaborator_mangle__ident(x_1353);
x_1427 = lean_expr_mk_let(x_1426, x_1376, x_1398, x_1421);
if (lean::is_scalar(x_1425)) {
 x_1428 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1428 = x_1425;
}
lean::cnstr_set(x_1428, 0, x_1427);
lean::cnstr_set(x_1428, 1, x_1423);
x_15 = x_1428;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1433; obj* x_1434; obj* x_1436; 
lean::dec(x_1330);
lean::dec(x_1327);
lean::dec(x_1324);
lean::inc(x_0);
x_1433 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1433, 0, x_0);
x_1434 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_2);
x_1436 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_1433, x_1434, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1433);
if (lean::obj_tag(x_1436) == 0)
{
obj* x_1442; obj* x_1444; obj* x_1445; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1442 = lean::cnstr_get(x_1436, 0);
if (lean::is_exclusive(x_1436)) {
 x_1444 = x_1436;
} else {
 lean::inc(x_1442);
 lean::dec(x_1436);
 x_1444 = lean::box(0);
}
if (lean::is_scalar(x_1444)) {
 x_1445 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1445 = x_1444;
}
lean::cnstr_set(x_1445, 0, x_1442);
return x_1445;
}
else
{
obj* x_1446; 
x_1446 = lean::cnstr_get(x_1436, 0);
lean::inc(x_1446);
lean::dec(x_1436);
x_15 = x_1446;
goto lbl_16;
}
}
}
else
{
obj* x_1452; obj* x_1453; obj* x_1455; 
lean::dec(x_1324);
lean::dec(x_1325);
lean::inc(x_0);
x_1452 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1452, 0, x_0);
x_1453 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_2);
x_1455 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_1452, x_1453, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1452);
if (lean::obj_tag(x_1455) == 0)
{
obj* x_1461; obj* x_1463; obj* x_1464; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1461 = lean::cnstr_get(x_1455, 0);
if (lean::is_exclusive(x_1455)) {
 x_1463 = x_1455;
} else {
 lean::inc(x_1461);
 lean::dec(x_1455);
 x_1463 = lean::box(0);
}
if (lean::is_scalar(x_1463)) {
 x_1464 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1464 = x_1463;
}
lean::cnstr_set(x_1464, 0, x_1461);
return x_1464;
}
else
{
obj* x_1465; 
x_1465 = lean::cnstr_get(x_1455, 0);
lean::inc(x_1465);
lean::dec(x_1455);
x_15 = x_1465;
goto lbl_16;
}
}
}
}
else
{
obj* x_1470; obj* x_1471; obj* x_1475; obj* x_1476; obj* x_1479; 
lean::dec(x_8);
lean::dec(x_10);
x_1470 = l_lean_parser_term_show_has__view;
x_1471 = lean::cnstr_get(x_1470, 0);
lean::inc(x_1471);
lean::dec(x_1470);
lean::inc(x_0);
x_1475 = lean::apply_1(x_1471, x_0);
x_1476 = lean::cnstr_get(x_1475, 1);
lean::inc(x_1476);
lean::inc(x_2);
x_1479 = l_lean_elaborator_to__pexpr___main(x_1476, x_1, x_2, x_3);
if (lean::obj_tag(x_1479) == 0)
{
obj* x_1483; obj* x_1485; obj* x_1486; 
lean::dec(x_1475);
lean::dec(x_0);
lean::dec(x_2);
x_1483 = lean::cnstr_get(x_1479, 0);
if (lean::is_exclusive(x_1479)) {
 x_1485 = x_1479;
} else {
 lean::inc(x_1483);
 lean::dec(x_1479);
 x_1485 = lean::box(0);
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
obj* x_1487; obj* x_1490; obj* x_1492; obj* x_1495; obj* x_1498; obj* x_1502; 
x_1487 = lean::cnstr_get(x_1479, 0);
lean::inc(x_1487);
lean::dec(x_1479);
x_1490 = lean::cnstr_get(x_1487, 0);
lean::inc(x_1490);
x_1492 = lean::cnstr_get(x_1487, 1);
lean::inc(x_1492);
lean::dec(x_1487);
x_1495 = lean::cnstr_get(x_1475, 3);
lean::inc(x_1495);
lean::dec(x_1475);
x_1498 = lean::cnstr_get(x_1495, 1);
lean::inc(x_1498);
lean::dec(x_1495);
lean::inc(x_2);
x_1502 = l_lean_elaborator_to__pexpr___main(x_1498, x_1, x_2, x_1492);
if (lean::obj_tag(x_1502) == 0)
{
obj* x_1506; obj* x_1508; obj* x_1509; 
lean::dec(x_1490);
lean::dec(x_0);
lean::dec(x_2);
x_1506 = lean::cnstr_get(x_1502, 0);
if (lean::is_exclusive(x_1502)) {
 x_1508 = x_1502;
} else {
 lean::inc(x_1506);
 lean::dec(x_1502);
 x_1508 = lean::box(0);
}
if (lean::is_scalar(x_1508)) {
 x_1509 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1509 = x_1508;
}
lean::cnstr_set(x_1509, 0, x_1506);
return x_1509;
}
else
{
obj* x_1510; obj* x_1512; obj* x_1513; obj* x_1515; obj* x_1517; obj* x_1518; uint8 x_1519; obj* x_1520; obj* x_1521; obj* x_1522; obj* x_1523; obj* x_1524; 
x_1510 = lean::cnstr_get(x_1502, 0);
if (lean::is_exclusive(x_1502)) {
 lean::cnstr_set(x_1502, 0, lean::box(0));
 x_1512 = x_1502;
} else {
 lean::inc(x_1510);
 lean::dec(x_1502);
 x_1512 = lean::box(0);
}
x_1513 = lean::cnstr_get(x_1510, 0);
x_1515 = lean::cnstr_get(x_1510, 1);
if (lean::is_exclusive(x_1510)) {
 lean::cnstr_set(x_1510, 0, lean::box(0));
 lean::cnstr_set(x_1510, 1, lean::box(0));
 x_1517 = x_1510;
} else {
 lean::inc(x_1513);
 lean::inc(x_1515);
 lean::dec(x_1510);
 x_1517 = lean::box(0);
}
x_1518 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1519 = 0;
x_1520 = l_lean_elaborator_to__pexpr___main___closed__38;
x_1521 = lean_expr_mk_lambda(x_1518, x_1519, x_1490, x_1520);
x_1522 = lean_expr_mk_app(x_1521, x_1513);
x_1523 = l_lean_elaborator_to__pexpr___main___closed__39;
x_1524 = l_lean_elaborator_expr_mk__annotation(x_1523, x_1522);
if (x_20 == 0)
{
obj* x_1525; 
x_1525 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1525) == 0)
{
obj* x_1528; obj* x_1529; 
lean::dec(x_2);
if (lean::is_scalar(x_1517)) {
 x_1528 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1528 = x_1517;
}
lean::cnstr_set(x_1528, 0, x_1524);
lean::cnstr_set(x_1528, 1, x_1515);
if (lean::is_scalar(x_1512)) {
 x_1529 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1529 = x_1512;
}
lean::cnstr_set(x_1529, 0, x_1528);
return x_1529;
}
else
{
obj* x_1530; obj* x_1533; obj* x_1536; obj* x_1539; obj* x_1540; obj* x_1541; obj* x_1543; obj* x_1544; obj* x_1545; obj* x_1548; obj* x_1549; obj* x_1550; obj* x_1551; obj* x_1552; 
x_1530 = lean::cnstr_get(x_1525, 0);
lean::inc(x_1530);
lean::dec(x_1525);
x_1533 = lean::cnstr_get(x_2, 0);
lean::inc(x_1533);
lean::dec(x_2);
x_1536 = lean::cnstr_get(x_1533, 2);
lean::inc(x_1536);
lean::dec(x_1533);
x_1539 = l_lean_file__map_to__position(x_1536, x_1530);
x_1540 = lean::box(0);
x_1541 = lean::cnstr_get(x_1539, 1);
lean::inc(x_1541);
x_1543 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1544 = l_lean_kvmap_set__nat(x_1540, x_1543, x_1541);
x_1545 = lean::cnstr_get(x_1539, 0);
lean::inc(x_1545);
lean::dec(x_1539);
x_1548 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1549 = l_lean_kvmap_set__nat(x_1544, x_1548, x_1545);
x_1550 = lean_expr_mk_mdata(x_1549, x_1524);
if (lean::is_scalar(x_1517)) {
 x_1551 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1551 = x_1517;
}
lean::cnstr_set(x_1551, 0, x_1550);
lean::cnstr_set(x_1551, 1, x_1515);
if (lean::is_scalar(x_1512)) {
 x_1552 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1552 = x_1512;
}
lean::cnstr_set(x_1552, 0, x_1551);
return x_1552;
}
}
else
{
obj* x_1555; obj* x_1556; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1517)) {
 x_1555 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1555 = x_1517;
}
lean::cnstr_set(x_1555, 0, x_1524);
lean::cnstr_set(x_1555, 1, x_1515);
if (lean::is_scalar(x_1512)) {
 x_1556 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1556 = x_1512;
}
lean::cnstr_set(x_1556, 0, x_1555);
return x_1556;
}
}
}
}
}
else
{
obj* x_1558; obj* x_1559; obj* x_1563; obj* x_1564; 
lean::dec(x_10);
x_1558 = l_lean_parser_term_have_has__view;
x_1559 = lean::cnstr_get(x_1558, 0);
lean::inc(x_1559);
lean::dec(x_1558);
lean::inc(x_0);
x_1563 = lean::apply_1(x_1559, x_0);
x_1564 = lean::cnstr_get(x_1563, 1);
lean::inc(x_1564);
if (lean::obj_tag(x_1564) == 0)
{
obj* x_1566; obj* x_1568; obj* x_1571; 
x_1566 = lean::cnstr_get(x_1563, 2);
lean::inc(x_1566);
x_1568 = lean::cnstr_get(x_1563, 5);
lean::inc(x_1568);
lean::inc(x_2);
x_1571 = l_lean_elaborator_to__pexpr___main(x_1566, x_1, x_2, x_3);
if (lean::obj_tag(x_1571) == 0)
{
obj* x_1577; obj* x_1579; obj* x_1580; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1568);
lean::dec(x_1563);
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
obj* x_1581; obj* x_1584; obj* x_1586; obj* x_1590; 
x_1581 = lean::cnstr_get(x_1571, 0);
lean::inc(x_1581);
lean::dec(x_1571);
x_1584 = lean::cnstr_get(x_1581, 0);
lean::inc(x_1584);
x_1586 = lean::cnstr_get(x_1581, 1);
lean::inc(x_1586);
lean::dec(x_1581);
lean::inc(x_2);
x_1590 = l_lean_elaborator_to__pexpr___main(x_1568, x_1, x_2, x_1586);
if (lean::obj_tag(x_1590) == 0)
{
obj* x_1596; obj* x_1598; obj* x_1599; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1563);
lean::dec(x_1584);
x_1596 = lean::cnstr_get(x_1590, 0);
if (lean::is_exclusive(x_1590)) {
 x_1598 = x_1590;
} else {
 lean::inc(x_1596);
 lean::dec(x_1590);
 x_1598 = lean::box(0);
}
if (lean::is_scalar(x_1598)) {
 x_1599 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1599 = x_1598;
}
lean::cnstr_set(x_1599, 0, x_1596);
return x_1599;
}
else
{
obj* x_1600; obj* x_1603; obj* x_1605; obj* x_1608; uint8 x_1609; obj* x_1610; obj* x_1611; 
x_1600 = lean::cnstr_get(x_1590, 0);
lean::inc(x_1600);
lean::dec(x_1590);
x_1603 = lean::cnstr_get(x_1600, 0);
lean::inc(x_1603);
x_1605 = lean::cnstr_get(x_1600, 1);
lean::inc(x_1605);
lean::dec(x_1600);
x_1608 = l_lean_elaborator_to__pexpr___main___closed__40;
x_1609 = 0;
x_1610 = lean_expr_mk_lambda(x_1608, x_1609, x_1584, x_1603);
x_1611 = lean::cnstr_get(x_1563, 3);
lean::inc(x_1611);
lean::dec(x_1563);
if (lean::obj_tag(x_1611) == 0)
{
obj* x_1614; obj* x_1617; obj* x_1621; 
x_1614 = lean::cnstr_get(x_1611, 0);
lean::inc(x_1614);
lean::dec(x_1611);
x_1617 = lean::cnstr_get(x_1614, 1);
lean::inc(x_1617);
lean::dec(x_1614);
lean::inc(x_2);
x_1621 = l_lean_elaborator_to__pexpr___main(x_1617, x_1, x_2, x_1605);
if (lean::obj_tag(x_1621) == 0)
{
obj* x_1626; obj* x_1628; obj* x_1629; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1610);
x_1626 = lean::cnstr_get(x_1621, 0);
if (lean::is_exclusive(x_1621)) {
 x_1628 = x_1621;
} else {
 lean::inc(x_1626);
 lean::dec(x_1621);
 x_1628 = lean::box(0);
}
if (lean::is_scalar(x_1628)) {
 x_1629 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1629 = x_1628;
}
lean::cnstr_set(x_1629, 0, x_1626);
return x_1629;
}
else
{
obj* x_1630; obj* x_1633; obj* x_1635; obj* x_1637; obj* x_1638; obj* x_1639; obj* x_1640; obj* x_1641; 
x_1630 = lean::cnstr_get(x_1621, 0);
lean::inc(x_1630);
lean::dec(x_1621);
x_1633 = lean::cnstr_get(x_1630, 0);
x_1635 = lean::cnstr_get(x_1630, 1);
if (lean::is_exclusive(x_1630)) {
 x_1637 = x_1630;
} else {
 lean::inc(x_1633);
 lean::inc(x_1635);
 lean::dec(x_1630);
 x_1637 = lean::box(0);
}
x_1638 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1639 = l_lean_elaborator_expr_mk__annotation(x_1638, x_1610);
x_1640 = lean_expr_mk_app(x_1639, x_1633);
if (lean::is_scalar(x_1637)) {
 x_1641 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1641 = x_1637;
}
lean::cnstr_set(x_1641, 0, x_1640);
lean::cnstr_set(x_1641, 1, x_1635);
x_15 = x_1641;
goto lbl_16;
}
}
else
{
obj* x_1642; obj* x_1645; obj* x_1648; obj* x_1652; 
x_1642 = lean::cnstr_get(x_1611, 0);
lean::inc(x_1642);
lean::dec(x_1611);
x_1645 = lean::cnstr_get(x_1642, 1);
lean::inc(x_1645);
lean::dec(x_1642);
x_1648 = lean::cnstr_get(x_1645, 1);
lean::inc(x_1648);
lean::dec(x_1645);
lean::inc(x_2);
x_1652 = l_lean_elaborator_to__pexpr___main(x_1648, x_1, x_2, x_1605);
if (lean::obj_tag(x_1652) == 0)
{
obj* x_1657; obj* x_1659; obj* x_1660; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1610);
x_1657 = lean::cnstr_get(x_1652, 0);
if (lean::is_exclusive(x_1652)) {
 x_1659 = x_1652;
} else {
 lean::inc(x_1657);
 lean::dec(x_1652);
 x_1659 = lean::box(0);
}
if (lean::is_scalar(x_1659)) {
 x_1660 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1660 = x_1659;
}
lean::cnstr_set(x_1660, 0, x_1657);
return x_1660;
}
else
{
obj* x_1661; obj* x_1664; obj* x_1666; obj* x_1668; obj* x_1669; obj* x_1670; obj* x_1671; obj* x_1672; 
x_1661 = lean::cnstr_get(x_1652, 0);
lean::inc(x_1661);
lean::dec(x_1652);
x_1664 = lean::cnstr_get(x_1661, 0);
x_1666 = lean::cnstr_get(x_1661, 1);
if (lean::is_exclusive(x_1661)) {
 x_1668 = x_1661;
} else {
 lean::inc(x_1664);
 lean::inc(x_1666);
 lean::dec(x_1661);
 x_1668 = lean::box(0);
}
x_1669 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1670 = l_lean_elaborator_expr_mk__annotation(x_1669, x_1610);
x_1671 = lean_expr_mk_app(x_1670, x_1664);
if (lean::is_scalar(x_1668)) {
 x_1672 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1672 = x_1668;
}
lean::cnstr_set(x_1672, 0, x_1671);
lean::cnstr_set(x_1672, 1, x_1666);
x_15 = x_1672;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1673; obj* x_1675; obj* x_1677; obj* x_1679; obj* x_1681; 
x_1673 = lean::cnstr_get(x_1563, 2);
lean::inc(x_1673);
x_1675 = lean::cnstr_get(x_1563, 5);
lean::inc(x_1675);
x_1677 = lean::cnstr_get(x_1564, 0);
if (lean::is_exclusive(x_1564)) {
 lean::cnstr_set(x_1564, 0, lean::box(0));
 x_1679 = x_1564;
} else {
 lean::inc(x_1677);
 lean::dec(x_1564);
 x_1679 = lean::box(0);
}
lean::inc(x_2);
x_1681 = l_lean_elaborator_to__pexpr___main(x_1673, x_1, x_2, x_3);
if (lean::obj_tag(x_1681) == 0)
{
obj* x_1689; obj* x_1691; obj* x_1692; 
lean::dec(x_1677);
lean::dec(x_1679);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1563);
lean::dec(x_1675);
x_1689 = lean::cnstr_get(x_1681, 0);
if (lean::is_exclusive(x_1681)) {
 x_1691 = x_1681;
} else {
 lean::inc(x_1689);
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
obj* x_1693; obj* x_1696; obj* x_1698; obj* x_1702; 
x_1693 = lean::cnstr_get(x_1681, 0);
lean::inc(x_1693);
lean::dec(x_1681);
x_1696 = lean::cnstr_get(x_1693, 0);
lean::inc(x_1696);
x_1698 = lean::cnstr_get(x_1693, 1);
lean::inc(x_1698);
lean::dec(x_1693);
lean::inc(x_2);
x_1702 = l_lean_elaborator_to__pexpr___main(x_1675, x_1, x_2, x_1698);
if (lean::obj_tag(x_1702) == 0)
{
obj* x_1710; obj* x_1712; obj* x_1713; 
lean::dec(x_1677);
lean::dec(x_1679);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1563);
lean::dec(x_1696);
x_1710 = lean::cnstr_get(x_1702, 0);
if (lean::is_exclusive(x_1702)) {
 x_1712 = x_1702;
} else {
 lean::inc(x_1710);
 lean::dec(x_1702);
 x_1712 = lean::box(0);
}
if (lean::is_scalar(x_1712)) {
 x_1713 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1713 = x_1712;
}
lean::cnstr_set(x_1713, 0, x_1710);
return x_1713;
}
else
{
obj* x_1714; obj* x_1717; obj* x_1719; obj* x_1722; obj* x_1725; obj* x_1726; obj* x_1727; obj* x_1728; uint8 x_1730; obj* x_1731; obj* x_1732; 
x_1714 = lean::cnstr_get(x_1702, 0);
lean::inc(x_1714);
lean::dec(x_1702);
x_1717 = lean::cnstr_get(x_1714, 0);
lean::inc(x_1717);
x_1719 = lean::cnstr_get(x_1714, 1);
lean::inc(x_1719);
lean::dec(x_1714);
x_1722 = lean::cnstr_get(x_1677, 0);
lean::inc(x_1722);
lean::dec(x_1677);
x_1725 = l_lean_elaborator_mangle__ident(x_1722);
if (lean::is_scalar(x_1679)) {
 x_1726 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1726 = x_1679;
}
lean::cnstr_set(x_1726, 0, x_1725);
x_1727 = l_lean_elaborator_to__pexpr___main___closed__37;
x_1728 = l_option_get__or__else___main___rarg(x_1726, x_1727);
lean::dec(x_1726);
x_1730 = 0;
x_1731 = lean_expr_mk_lambda(x_1728, x_1730, x_1696, x_1717);
x_1732 = lean::cnstr_get(x_1563, 3);
lean::inc(x_1732);
lean::dec(x_1563);
if (lean::obj_tag(x_1732) == 0)
{
obj* x_1735; obj* x_1738; obj* x_1742; 
x_1735 = lean::cnstr_get(x_1732, 0);
lean::inc(x_1735);
lean::dec(x_1732);
x_1738 = lean::cnstr_get(x_1735, 1);
lean::inc(x_1738);
lean::dec(x_1735);
lean::inc(x_2);
x_1742 = l_lean_elaborator_to__pexpr___main(x_1738, x_1, x_2, x_1719);
if (lean::obj_tag(x_1742) == 0)
{
obj* x_1747; obj* x_1749; obj* x_1750; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1731);
x_1747 = lean::cnstr_get(x_1742, 0);
if (lean::is_exclusive(x_1742)) {
 x_1749 = x_1742;
} else {
 lean::inc(x_1747);
 lean::dec(x_1742);
 x_1749 = lean::box(0);
}
if (lean::is_scalar(x_1749)) {
 x_1750 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1750 = x_1749;
}
lean::cnstr_set(x_1750, 0, x_1747);
return x_1750;
}
else
{
obj* x_1751; obj* x_1754; obj* x_1756; obj* x_1758; obj* x_1759; obj* x_1760; obj* x_1761; obj* x_1762; 
x_1751 = lean::cnstr_get(x_1742, 0);
lean::inc(x_1751);
lean::dec(x_1742);
x_1754 = lean::cnstr_get(x_1751, 0);
x_1756 = lean::cnstr_get(x_1751, 1);
if (lean::is_exclusive(x_1751)) {
 x_1758 = x_1751;
} else {
 lean::inc(x_1754);
 lean::inc(x_1756);
 lean::dec(x_1751);
 x_1758 = lean::box(0);
}
x_1759 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1760 = l_lean_elaborator_expr_mk__annotation(x_1759, x_1731);
x_1761 = lean_expr_mk_app(x_1760, x_1754);
if (lean::is_scalar(x_1758)) {
 x_1762 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1762 = x_1758;
}
lean::cnstr_set(x_1762, 0, x_1761);
lean::cnstr_set(x_1762, 1, x_1756);
x_15 = x_1762;
goto lbl_16;
}
}
else
{
obj* x_1763; obj* x_1766; obj* x_1769; obj* x_1773; 
x_1763 = lean::cnstr_get(x_1732, 0);
lean::inc(x_1763);
lean::dec(x_1732);
x_1766 = lean::cnstr_get(x_1763, 1);
lean::inc(x_1766);
lean::dec(x_1763);
x_1769 = lean::cnstr_get(x_1766, 1);
lean::inc(x_1769);
lean::dec(x_1766);
lean::inc(x_2);
x_1773 = l_lean_elaborator_to__pexpr___main(x_1769, x_1, x_2, x_1719);
if (lean::obj_tag(x_1773) == 0)
{
obj* x_1778; obj* x_1780; obj* x_1781; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1731);
x_1778 = lean::cnstr_get(x_1773, 0);
if (lean::is_exclusive(x_1773)) {
 x_1780 = x_1773;
} else {
 lean::inc(x_1778);
 lean::dec(x_1773);
 x_1780 = lean::box(0);
}
if (lean::is_scalar(x_1780)) {
 x_1781 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1781 = x_1780;
}
lean::cnstr_set(x_1781, 0, x_1778);
return x_1781;
}
else
{
obj* x_1782; obj* x_1785; obj* x_1787; obj* x_1789; obj* x_1790; obj* x_1791; obj* x_1792; obj* x_1793; 
x_1782 = lean::cnstr_get(x_1773, 0);
lean::inc(x_1782);
lean::dec(x_1773);
x_1785 = lean::cnstr_get(x_1782, 0);
x_1787 = lean::cnstr_get(x_1782, 1);
if (lean::is_exclusive(x_1782)) {
 x_1789 = x_1782;
} else {
 lean::inc(x_1785);
 lean::inc(x_1787);
 lean::dec(x_1782);
 x_1789 = lean::box(0);
}
x_1790 = l_lean_elaborator_to__pexpr___main___closed__41;
x_1791 = l_lean_elaborator_expr_mk__annotation(x_1790, x_1731);
x_1792 = lean_expr_mk_app(x_1791, x_1785);
if (lean::is_scalar(x_1789)) {
 x_1793 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1793 = x_1789;
}
lean::cnstr_set(x_1793, 0, x_1792);
lean::cnstr_set(x_1793, 1, x_1787);
x_15 = x_1793;
goto lbl_16;
}
}
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
obj* x_1796; 
x_1796 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1796) == 0)
{
obj* x_1799; obj* x_1800; obj* x_1801; 
lean::dec(x_2);
x_1799 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1800 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1800, 0, x_1799);
lean::cnstr_set(x_1800, 1, x_3);
x_1801 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1801, 0, x_1800);
return x_1801;
}
else
{
obj* x_1802; obj* x_1805; obj* x_1808; obj* x_1811; obj* x_1812; obj* x_1813; obj* x_1815; obj* x_1816; obj* x_1817; obj* x_1820; obj* x_1821; obj* x_1822; obj* x_1823; obj* x_1824; obj* x_1825; 
x_1802 = lean::cnstr_get(x_1796, 0);
lean::inc(x_1802);
lean::dec(x_1796);
x_1805 = lean::cnstr_get(x_2, 0);
lean::inc(x_1805);
lean::dec(x_2);
x_1808 = lean::cnstr_get(x_1805, 2);
lean::inc(x_1808);
lean::dec(x_1805);
x_1811 = l_lean_file__map_to__position(x_1808, x_1802);
x_1812 = lean::box(0);
x_1813 = lean::cnstr_get(x_1811, 1);
lean::inc(x_1813);
x_1815 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1816 = l_lean_kvmap_set__nat(x_1812, x_1815, x_1813);
x_1817 = lean::cnstr_get(x_1811, 0);
lean::inc(x_1817);
lean::dec(x_1811);
x_1820 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1821 = l_lean_kvmap_set__nat(x_1816, x_1820, x_1817);
x_1822 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1823 = lean_expr_mk_mdata(x_1821, x_1822);
x_1824 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1824, 0, x_1823);
lean::cnstr_set(x_1824, 1, x_3);
x_1825 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1825, 0, x_1824);
return x_1825;
}
}
else
{
obj* x_1828; obj* x_1829; obj* x_1830; 
lean::dec(x_0);
lean::dec(x_2);
x_1828 = l_lean_elaborator_to__pexpr___main___closed__42;
x_1829 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1829, 0, x_1828);
lean::cnstr_set(x_1829, 1, x_3);
x_1830 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1830, 0, x_1829);
return x_1830;
}
}
}
else
{
obj* x_1833; obj* x_1834; obj* x_1838; obj* x_1839; obj* x_1842; obj* x_1843; obj* x_1844; obj* x_1846; 
lean::dec(x_8);
lean::dec(x_10);
x_1833 = l_lean_parser_term_anonymous__constructor_has__view;
x_1834 = lean::cnstr_get(x_1833, 0);
lean::inc(x_1834);
lean::dec(x_1833);
lean::inc(x_0);
x_1838 = lean::apply_1(x_1834, x_0);
x_1839 = lean::cnstr_get(x_1838, 1);
lean::inc(x_1839);
lean::dec(x_1838);
x_1842 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_1839);
x_1843 = l_lean_expander_get__opt__type___main___closed__1;
x_1844 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_1843, x_1842);
lean::inc(x_2);
x_1846 = l_lean_elaborator_to__pexpr___main(x_1844, x_1, x_2, x_3);
if (lean::obj_tag(x_1846) == 0)
{
obj* x_1849; obj* x_1851; obj* x_1852; 
lean::dec(x_0);
lean::dec(x_2);
x_1849 = lean::cnstr_get(x_1846, 0);
if (lean::is_exclusive(x_1846)) {
 x_1851 = x_1846;
} else {
 lean::inc(x_1849);
 lean::dec(x_1846);
 x_1851 = lean::box(0);
}
if (lean::is_scalar(x_1851)) {
 x_1852 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1852 = x_1851;
}
lean::cnstr_set(x_1852, 0, x_1849);
return x_1852;
}
else
{
obj* x_1853; obj* x_1855; obj* x_1856; obj* x_1858; obj* x_1860; obj* x_1861; obj* x_1862; 
x_1853 = lean::cnstr_get(x_1846, 0);
if (lean::is_exclusive(x_1846)) {
 lean::cnstr_set(x_1846, 0, lean::box(0));
 x_1855 = x_1846;
} else {
 lean::inc(x_1853);
 lean::dec(x_1846);
 x_1855 = lean::box(0);
}
x_1856 = lean::cnstr_get(x_1853, 0);
x_1858 = lean::cnstr_get(x_1853, 1);
if (lean::is_exclusive(x_1853)) {
 lean::cnstr_set(x_1853, 0, lean::box(0));
 lean::cnstr_set(x_1853, 1, lean::box(0));
 x_1860 = x_1853;
} else {
 lean::inc(x_1856);
 lean::inc(x_1858);
 lean::dec(x_1853);
 x_1860 = lean::box(0);
}
x_1861 = l_lean_elaborator_to__pexpr___main___closed__43;
x_1862 = l_lean_elaborator_expr_mk__annotation(x_1861, x_1856);
if (x_20 == 0)
{
obj* x_1863; 
x_1863 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1863) == 0)
{
obj* x_1866; obj* x_1867; 
lean::dec(x_2);
if (lean::is_scalar(x_1860)) {
 x_1866 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1866 = x_1860;
}
lean::cnstr_set(x_1866, 0, x_1862);
lean::cnstr_set(x_1866, 1, x_1858);
if (lean::is_scalar(x_1855)) {
 x_1867 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1867 = x_1855;
}
lean::cnstr_set(x_1867, 0, x_1866);
return x_1867;
}
else
{
obj* x_1868; obj* x_1871; obj* x_1874; obj* x_1877; obj* x_1878; obj* x_1879; obj* x_1881; obj* x_1882; obj* x_1883; obj* x_1886; obj* x_1887; obj* x_1888; obj* x_1889; obj* x_1890; 
x_1868 = lean::cnstr_get(x_1863, 0);
lean::inc(x_1868);
lean::dec(x_1863);
x_1871 = lean::cnstr_get(x_2, 0);
lean::inc(x_1871);
lean::dec(x_2);
x_1874 = lean::cnstr_get(x_1871, 2);
lean::inc(x_1874);
lean::dec(x_1871);
x_1877 = l_lean_file__map_to__position(x_1874, x_1868);
x_1878 = lean::box(0);
x_1879 = lean::cnstr_get(x_1877, 1);
lean::inc(x_1879);
x_1881 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1882 = l_lean_kvmap_set__nat(x_1878, x_1881, x_1879);
x_1883 = lean::cnstr_get(x_1877, 0);
lean::inc(x_1883);
lean::dec(x_1877);
x_1886 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1887 = l_lean_kvmap_set__nat(x_1882, x_1886, x_1883);
x_1888 = lean_expr_mk_mdata(x_1887, x_1862);
if (lean::is_scalar(x_1860)) {
 x_1889 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1889 = x_1860;
}
lean::cnstr_set(x_1889, 0, x_1888);
lean::cnstr_set(x_1889, 1, x_1858);
if (lean::is_scalar(x_1855)) {
 x_1890 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1890 = x_1855;
}
lean::cnstr_set(x_1890, 0, x_1889);
return x_1890;
}
}
else
{
obj* x_1893; obj* x_1894; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1860)) {
 x_1893 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1893 = x_1860;
}
lean::cnstr_set(x_1893, 0, x_1862);
lean::cnstr_set(x_1893, 1, x_1858);
if (lean::is_scalar(x_1855)) {
 x_1894 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1894 = x_1855;
}
lean::cnstr_set(x_1894, 0, x_1893);
return x_1894;
}
}
}
}
else
{
obj* x_1897; obj* x_1898; obj* x_1902; obj* x_1903; obj* x_1904; obj* x_1907; obj* x_1909; 
lean::dec(x_8);
lean::dec(x_10);
x_1897 = l_lean_parser_term_sort__app_has__view;
x_1898 = lean::cnstr_get(x_1897, 0);
lean::inc(x_1898);
lean::dec(x_1897);
lean::inc(x_0);
x_1902 = lean::apply_1(x_1898, x_0);
x_1903 = l_lean_parser_term_sort_has__view;
x_1904 = lean::cnstr_get(x_1903, 0);
lean::inc(x_1904);
lean::dec(x_1903);
x_1907 = lean::cnstr_get(x_1902, 0);
lean::inc(x_1907);
x_1909 = lean::apply_1(x_1904, x_1907);
if (lean::obj_tag(x_1909) == 0)
{
obj* x_1911; obj* x_1915; 
lean::dec(x_1909);
x_1911 = lean::cnstr_get(x_1902, 1);
lean::inc(x_1911);
lean::dec(x_1902);
lean::inc(x_2);
x_1915 = l_lean_elaborator_to__level___main(x_1911, x_1, x_2, x_3);
if (lean::obj_tag(x_1915) == 0)
{
obj* x_1918; obj* x_1920; obj* x_1921; 
lean::dec(x_0);
lean::dec(x_2);
x_1918 = lean::cnstr_get(x_1915, 0);
if (lean::is_exclusive(x_1915)) {
 x_1920 = x_1915;
} else {
 lean::inc(x_1918);
 lean::dec(x_1915);
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
obj* x_1922; obj* x_1924; obj* x_1925; obj* x_1927; obj* x_1929; obj* x_1930; 
x_1922 = lean::cnstr_get(x_1915, 0);
if (lean::is_exclusive(x_1915)) {
 lean::cnstr_set(x_1915, 0, lean::box(0));
 x_1924 = x_1915;
} else {
 lean::inc(x_1922);
 lean::dec(x_1915);
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
x_1930 = lean_expr_mk_sort(x_1925);
if (x_20 == 0)
{
obj* x_1931; 
x_1931 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1931) == 0)
{
obj* x_1934; obj* x_1935; 
lean::dec(x_2);
if (lean::is_scalar(x_1929)) {
 x_1934 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1934 = x_1929;
}
lean::cnstr_set(x_1934, 0, x_1930);
lean::cnstr_set(x_1934, 1, x_1927);
if (lean::is_scalar(x_1924)) {
 x_1935 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1935 = x_1924;
}
lean::cnstr_set(x_1935, 0, x_1934);
return x_1935;
}
else
{
obj* x_1936; obj* x_1939; obj* x_1942; obj* x_1945; obj* x_1946; obj* x_1947; obj* x_1949; obj* x_1950; obj* x_1951; obj* x_1954; obj* x_1955; obj* x_1956; obj* x_1957; obj* x_1958; 
x_1936 = lean::cnstr_get(x_1931, 0);
lean::inc(x_1936);
lean::dec(x_1931);
x_1939 = lean::cnstr_get(x_2, 0);
lean::inc(x_1939);
lean::dec(x_2);
x_1942 = lean::cnstr_get(x_1939, 2);
lean::inc(x_1942);
lean::dec(x_1939);
x_1945 = l_lean_file__map_to__position(x_1942, x_1936);
x_1946 = lean::box(0);
x_1947 = lean::cnstr_get(x_1945, 1);
lean::inc(x_1947);
x_1949 = l_lean_elaborator_to__pexpr___main___closed__3;
x_1950 = l_lean_kvmap_set__nat(x_1946, x_1949, x_1947);
x_1951 = lean::cnstr_get(x_1945, 0);
lean::inc(x_1951);
lean::dec(x_1945);
x_1954 = l_lean_elaborator_to__pexpr___main___closed__4;
x_1955 = l_lean_kvmap_set__nat(x_1950, x_1954, x_1951);
x_1956 = lean_expr_mk_mdata(x_1955, x_1930);
if (lean::is_scalar(x_1929)) {
 x_1957 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1957 = x_1929;
}
lean::cnstr_set(x_1957, 0, x_1956);
lean::cnstr_set(x_1957, 1, x_1927);
if (lean::is_scalar(x_1924)) {
 x_1958 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1958 = x_1924;
}
lean::cnstr_set(x_1958, 0, x_1957);
return x_1958;
}
}
else
{
obj* x_1961; obj* x_1962; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1929)) {
 x_1961 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1961 = x_1929;
}
lean::cnstr_set(x_1961, 0, x_1930);
lean::cnstr_set(x_1961, 1, x_1927);
if (lean::is_scalar(x_1924)) {
 x_1962 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1962 = x_1924;
}
lean::cnstr_set(x_1962, 0, x_1961);
return x_1962;
}
}
}
else
{
obj* x_1964; obj* x_1968; 
lean::dec(x_1909);
x_1964 = lean::cnstr_get(x_1902, 1);
lean::inc(x_1964);
lean::dec(x_1902);
lean::inc(x_2);
x_1968 = l_lean_elaborator_to__level___main(x_1964, x_1, x_2, x_3);
if (lean::obj_tag(x_1968) == 0)
{
obj* x_1971; obj* x_1973; obj* x_1974; 
lean::dec(x_0);
lean::dec(x_2);
x_1971 = lean::cnstr_get(x_1968, 0);
if (lean::is_exclusive(x_1968)) {
 x_1973 = x_1968;
} else {
 lean::inc(x_1971);
 lean::dec(x_1968);
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
obj* x_1975; obj* x_1977; obj* x_1978; obj* x_1980; obj* x_1982; obj* x_1983; obj* x_1984; 
x_1975 = lean::cnstr_get(x_1968, 0);
if (lean::is_exclusive(x_1968)) {
 lean::cnstr_set(x_1968, 0, lean::box(0));
 x_1977 = x_1968;
} else {
 lean::inc(x_1975);
 lean::dec(x_1968);
 x_1977 = lean::box(0);
}
x_1978 = lean::cnstr_get(x_1975, 0);
x_1980 = lean::cnstr_get(x_1975, 1);
if (lean::is_exclusive(x_1975)) {
 lean::cnstr_set(x_1975, 0, lean::box(0));
 lean::cnstr_set(x_1975, 1, lean::box(0));
 x_1982 = x_1975;
} else {
 lean::inc(x_1978);
 lean::inc(x_1980);
 lean::dec(x_1975);
 x_1982 = lean::box(0);
}
x_1983 = level_mk_succ(x_1978);
x_1984 = lean_expr_mk_sort(x_1983);
if (x_20 == 0)
{
obj* x_1985; 
x_1985 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1985) == 0)
{
obj* x_1988; obj* x_1989; 
lean::dec(x_2);
if (lean::is_scalar(x_1982)) {
 x_1988 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1988 = x_1982;
}
lean::cnstr_set(x_1988, 0, x_1984);
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
obj* x_1990; obj* x_1993; obj* x_1996; obj* x_1999; obj* x_2000; obj* x_2001; obj* x_2003; obj* x_2004; obj* x_2005; obj* x_2008; obj* x_2009; obj* x_2010; obj* x_2011; obj* x_2012; 
x_1990 = lean::cnstr_get(x_1985, 0);
lean::inc(x_1990);
lean::dec(x_1985);
x_1993 = lean::cnstr_get(x_2, 0);
lean::inc(x_1993);
lean::dec(x_2);
x_1996 = lean::cnstr_get(x_1993, 2);
lean::inc(x_1996);
lean::dec(x_1993);
x_1999 = l_lean_file__map_to__position(x_1996, x_1990);
x_2000 = lean::box(0);
x_2001 = lean::cnstr_get(x_1999, 1);
lean::inc(x_2001);
x_2003 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2004 = l_lean_kvmap_set__nat(x_2000, x_2003, x_2001);
x_2005 = lean::cnstr_get(x_1999, 0);
lean::inc(x_2005);
lean::dec(x_1999);
x_2008 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2009 = l_lean_kvmap_set__nat(x_2004, x_2008, x_2005);
x_2010 = lean_expr_mk_mdata(x_2009, x_1984);
if (lean::is_scalar(x_1982)) {
 x_2011 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2011 = x_1982;
}
lean::cnstr_set(x_2011, 0, x_2010);
lean::cnstr_set(x_2011, 1, x_1980);
if (lean::is_scalar(x_1977)) {
 x_2012 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2012 = x_1977;
}
lean::cnstr_set(x_2012, 0, x_2011);
return x_2012;
}
}
else
{
obj* x_2015; obj* x_2016; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1982)) {
 x_2015 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2015 = x_1982;
}
lean::cnstr_set(x_2015, 0, x_1984);
lean::cnstr_set(x_2015, 1, x_1980);
if (lean::is_scalar(x_1977)) {
 x_2016 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2016 = x_1977;
}
lean::cnstr_set(x_2016, 0, x_2015);
return x_2016;
}
}
}
}
}
else
{
obj* x_2019; obj* x_2020; obj* x_2024; 
lean::dec(x_8);
lean::dec(x_10);
x_2019 = l_lean_parser_term_sort_has__view;
x_2020 = lean::cnstr_get(x_2019, 0);
lean::inc(x_2020);
lean::dec(x_2019);
lean::inc(x_0);
x_2024 = lean::apply_1(x_2020, x_0);
if (lean::obj_tag(x_2024) == 0)
{
lean::dec(x_2024);
if (x_20 == 0)
{
obj* x_2026; 
x_2026 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2026) == 0)
{
obj* x_2029; obj* x_2030; obj* x_2031; 
lean::dec(x_2);
x_2029 = l_lean_elaborator_to__pexpr___main___closed__25;
x_2030 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2030, 0, x_2029);
lean::cnstr_set(x_2030, 1, x_3);
x_2031 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2031, 0, x_2030);
return x_2031;
}
else
{
obj* x_2032; obj* x_2035; obj* x_2038; obj* x_2041; obj* x_2042; obj* x_2043; obj* x_2045; obj* x_2046; obj* x_2047; obj* x_2050; obj* x_2051; obj* x_2052; obj* x_2053; obj* x_2054; obj* x_2055; 
x_2032 = lean::cnstr_get(x_2026, 0);
lean::inc(x_2032);
lean::dec(x_2026);
x_2035 = lean::cnstr_get(x_2, 0);
lean::inc(x_2035);
lean::dec(x_2);
x_2038 = lean::cnstr_get(x_2035, 2);
lean::inc(x_2038);
lean::dec(x_2035);
x_2041 = l_lean_file__map_to__position(x_2038, x_2032);
x_2042 = lean::box(0);
x_2043 = lean::cnstr_get(x_2041, 1);
lean::inc(x_2043);
x_2045 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2046 = l_lean_kvmap_set__nat(x_2042, x_2045, x_2043);
x_2047 = lean::cnstr_get(x_2041, 0);
lean::inc(x_2047);
lean::dec(x_2041);
x_2050 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2051 = l_lean_kvmap_set__nat(x_2046, x_2050, x_2047);
x_2052 = l_lean_elaborator_to__pexpr___main___closed__25;
x_2053 = lean_expr_mk_mdata(x_2051, x_2052);
x_2054 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2054, 0, x_2053);
lean::cnstr_set(x_2054, 1, x_3);
x_2055 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2055, 0, x_2054);
return x_2055;
}
}
else
{
obj* x_2058; obj* x_2059; obj* x_2060; 
lean::dec(x_0);
lean::dec(x_2);
x_2058 = l_lean_elaborator_to__pexpr___main___closed__25;
x_2059 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2059, 0, x_2058);
lean::cnstr_set(x_2059, 1, x_3);
x_2060 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2060, 0, x_2059);
return x_2060;
}
}
else
{
lean::dec(x_2024);
if (x_20 == 0)
{
obj* x_2062; 
x_2062 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2062) == 0)
{
obj* x_2065; obj* x_2066; obj* x_2067; 
lean::dec(x_2);
x_2065 = l_lean_elaborator_to__pexpr___main___closed__44;
x_2066 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2066, 0, x_2065);
lean::cnstr_set(x_2066, 1, x_3);
x_2067 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2067, 0, x_2066);
return x_2067;
}
else
{
obj* x_2068; obj* x_2071; obj* x_2074; obj* x_2077; obj* x_2078; obj* x_2079; obj* x_2081; obj* x_2082; obj* x_2083; obj* x_2086; obj* x_2087; obj* x_2088; obj* x_2089; obj* x_2090; obj* x_2091; 
x_2068 = lean::cnstr_get(x_2062, 0);
lean::inc(x_2068);
lean::dec(x_2062);
x_2071 = lean::cnstr_get(x_2, 0);
lean::inc(x_2071);
lean::dec(x_2);
x_2074 = lean::cnstr_get(x_2071, 2);
lean::inc(x_2074);
lean::dec(x_2071);
x_2077 = l_lean_file__map_to__position(x_2074, x_2068);
x_2078 = lean::box(0);
x_2079 = lean::cnstr_get(x_2077, 1);
lean::inc(x_2079);
x_2081 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2082 = l_lean_kvmap_set__nat(x_2078, x_2081, x_2079);
x_2083 = lean::cnstr_get(x_2077, 0);
lean::inc(x_2083);
lean::dec(x_2077);
x_2086 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2087 = l_lean_kvmap_set__nat(x_2082, x_2086, x_2083);
x_2088 = l_lean_elaborator_to__pexpr___main___closed__44;
x_2089 = lean_expr_mk_mdata(x_2087, x_2088);
x_2090 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2090, 0, x_2089);
lean::cnstr_set(x_2090, 1, x_3);
x_2091 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2091, 0, x_2090);
return x_2091;
}
}
else
{
obj* x_2094; obj* x_2095; obj* x_2096; 
lean::dec(x_0);
lean::dec(x_2);
x_2094 = l_lean_elaborator_to__pexpr___main___closed__44;
x_2095 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2095, 0, x_2094);
lean::cnstr_set(x_2095, 1, x_3);
x_2096 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2096, 0, x_2095);
return x_2096;
}
}
}
}
else
{
obj* x_2098; obj* x_2099; obj* x_2103; obj* x_2104; 
lean::dec(x_10);
x_2098 = l_lean_parser_term_pi_has__view;
x_2099 = lean::cnstr_get(x_2098, 0);
lean::inc(x_2099);
lean::dec(x_2098);
lean::inc(x_0);
x_2103 = lean::apply_1(x_2099, x_0);
x_2104 = lean::cnstr_get(x_2103, 1);
lean::inc(x_2104);
if (lean::obj_tag(x_2104) == 0)
{
obj* x_2109; obj* x_2110; obj* x_2112; 
lean::dec(x_2104);
lean::dec(x_2103);
lean::inc(x_0);
x_2109 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2109, 0, x_0);
x_2110 = l_lean_elaborator_to__pexpr___main___closed__45;
lean::inc(x_2);
x_2112 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_2109, x_2110, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2109);
if (lean::obj_tag(x_2112) == 0)
{
obj* x_2118; obj* x_2120; obj* x_2121; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2118 = lean::cnstr_get(x_2112, 0);
if (lean::is_exclusive(x_2112)) {
 x_2120 = x_2112;
} else {
 lean::inc(x_2118);
 lean::dec(x_2112);
 x_2120 = lean::box(0);
}
if (lean::is_scalar(x_2120)) {
 x_2121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2121 = x_2120;
}
lean::cnstr_set(x_2121, 0, x_2118);
return x_2121;
}
else
{
obj* x_2122; 
x_2122 = lean::cnstr_get(x_2112, 0);
lean::inc(x_2122);
lean::dec(x_2112);
x_15 = x_2122;
goto lbl_16;
}
}
else
{
obj* x_2125; obj* x_2128; obj* x_2129; obj* x_2131; obj* x_2134; obj* x_2136; obj* x_2140; 
x_2125 = lean::cnstr_get(x_2104, 0);
lean::inc(x_2125);
lean::dec(x_2104);
x_2128 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_2125);
x_2129 = lean::cnstr_get(x_2128, 1);
lean::inc(x_2129);
x_2131 = lean::cnstr_get(x_2128, 0);
lean::inc(x_2131);
lean::dec(x_2128);
x_2134 = lean::cnstr_get(x_2129, 0);
lean::inc(x_2134);
x_2136 = lean::cnstr_get(x_2129, 1);
lean::inc(x_2136);
lean::dec(x_2129);
lean::inc(x_2);
x_2140 = l_lean_elaborator_to__pexpr___main(x_2136, x_1, x_2, x_3);
if (lean::obj_tag(x_2140) == 0)
{
obj* x_2147; obj* x_2149; obj* x_2150; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2134);
lean::dec(x_2131);
lean::dec(x_2103);
x_2147 = lean::cnstr_get(x_2140, 0);
if (lean::is_exclusive(x_2140)) {
 x_2149 = x_2140;
} else {
 lean::inc(x_2147);
 lean::dec(x_2140);
 x_2149 = lean::box(0);
}
if (lean::is_scalar(x_2149)) {
 x_2150 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2150 = x_2149;
}
lean::cnstr_set(x_2150, 0, x_2147);
return x_2150;
}
else
{
obj* x_2151; obj* x_2154; obj* x_2156; obj* x_2159; obj* x_2163; 
x_2151 = lean::cnstr_get(x_2140, 0);
lean::inc(x_2151);
lean::dec(x_2140);
x_2154 = lean::cnstr_get(x_2151, 0);
lean::inc(x_2154);
x_2156 = lean::cnstr_get(x_2151, 1);
lean::inc(x_2156);
lean::dec(x_2151);
x_2159 = lean::cnstr_get(x_2103, 3);
lean::inc(x_2159);
lean::dec(x_2103);
lean::inc(x_2);
x_2163 = l_lean_elaborator_to__pexpr___main(x_2159, x_1, x_2, x_2156);
if (lean::obj_tag(x_2163) == 0)
{
obj* x_2170; obj* x_2172; obj* x_2173; 
lean::dec(x_2154);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2134);
lean::dec(x_2131);
x_2170 = lean::cnstr_get(x_2163, 0);
if (lean::is_exclusive(x_2163)) {
 x_2172 = x_2163;
} else {
 lean::inc(x_2170);
 lean::dec(x_2163);
 x_2172 = lean::box(0);
}
if (lean::is_scalar(x_2172)) {
 x_2173 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2173 = x_2172;
}
lean::cnstr_set(x_2173, 0, x_2170);
return x_2173;
}
else
{
obj* x_2174; obj* x_2177; obj* x_2179; obj* x_2181; obj* x_2182; uint8 x_2183; obj* x_2184; obj* x_2185; 
x_2174 = lean::cnstr_get(x_2163, 0);
lean::inc(x_2174);
lean::dec(x_2163);
x_2177 = lean::cnstr_get(x_2174, 0);
x_2179 = lean::cnstr_get(x_2174, 1);
if (lean::is_exclusive(x_2174)) {
 x_2181 = x_2174;
} else {
 lean::inc(x_2177);
 lean::inc(x_2179);
 lean::dec(x_2174);
 x_2181 = lean::box(0);
}
x_2182 = l_lean_elaborator_mangle__ident(x_2134);
x_2183 = lean::unbox(x_2131);
x_2184 = lean_expr_mk_pi(x_2182, x_2183, x_2154, x_2177);
if (lean::is_scalar(x_2181)) {
 x_2185 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2185 = x_2181;
}
lean::cnstr_set(x_2185, 0, x_2184);
lean::cnstr_set(x_2185, 1, x_2179);
x_15 = x_2185;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2187; obj* x_2188; obj* x_2192; obj* x_2193; 
lean::dec(x_10);
x_2187 = l_lean_parser_term_lambda_has__view;
x_2188 = lean::cnstr_get(x_2187, 0);
lean::inc(x_2188);
lean::dec(x_2187);
lean::inc(x_0);
x_2192 = lean::apply_1(x_2188, x_0);
x_2193 = lean::cnstr_get(x_2192, 1);
lean::inc(x_2193);
if (lean::obj_tag(x_2193) == 0)
{
obj* x_2198; obj* x_2199; obj* x_2201; 
lean::dec(x_2192);
lean::dec(x_2193);
lean::inc(x_0);
x_2198 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2198, 0, x_0);
x_2199 = l_lean_elaborator_to__pexpr___main___closed__46;
lean::inc(x_2);
x_2201 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_2198, x_2199, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2198);
if (lean::obj_tag(x_2201) == 0)
{
obj* x_2207; obj* x_2209; obj* x_2210; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2207 = lean::cnstr_get(x_2201, 0);
if (lean::is_exclusive(x_2201)) {
 x_2209 = x_2201;
} else {
 lean::inc(x_2207);
 lean::dec(x_2201);
 x_2209 = lean::box(0);
}
if (lean::is_scalar(x_2209)) {
 x_2210 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2210 = x_2209;
}
lean::cnstr_set(x_2210, 0, x_2207);
return x_2210;
}
else
{
obj* x_2211; 
x_2211 = lean::cnstr_get(x_2201, 0);
lean::inc(x_2211);
lean::dec(x_2201);
x_15 = x_2211;
goto lbl_16;
}
}
else
{
obj* x_2214; obj* x_2217; obj* x_2218; obj* x_2220; obj* x_2223; obj* x_2225; obj* x_2229; 
x_2214 = lean::cnstr_get(x_2193, 0);
lean::inc(x_2214);
lean::dec(x_2193);
x_2217 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_2214);
x_2218 = lean::cnstr_get(x_2217, 1);
lean::inc(x_2218);
x_2220 = lean::cnstr_get(x_2217, 0);
lean::inc(x_2220);
lean::dec(x_2217);
x_2223 = lean::cnstr_get(x_2218, 0);
lean::inc(x_2223);
x_2225 = lean::cnstr_get(x_2218, 1);
lean::inc(x_2225);
lean::dec(x_2218);
lean::inc(x_2);
x_2229 = l_lean_elaborator_to__pexpr___main(x_2225, x_1, x_2, x_3);
if (lean::obj_tag(x_2229) == 0)
{
obj* x_2236; obj* x_2238; obj* x_2239; 
lean::dec(x_2192);
lean::dec(x_2223);
lean::dec(x_2220);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2236 = lean::cnstr_get(x_2229, 0);
if (lean::is_exclusive(x_2229)) {
 x_2238 = x_2229;
} else {
 lean::inc(x_2236);
 lean::dec(x_2229);
 x_2238 = lean::box(0);
}
if (lean::is_scalar(x_2238)) {
 x_2239 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2239 = x_2238;
}
lean::cnstr_set(x_2239, 0, x_2236);
return x_2239;
}
else
{
obj* x_2240; obj* x_2243; obj* x_2245; obj* x_2248; obj* x_2252; 
x_2240 = lean::cnstr_get(x_2229, 0);
lean::inc(x_2240);
lean::dec(x_2229);
x_2243 = lean::cnstr_get(x_2240, 0);
lean::inc(x_2243);
x_2245 = lean::cnstr_get(x_2240, 1);
lean::inc(x_2245);
lean::dec(x_2240);
x_2248 = lean::cnstr_get(x_2192, 3);
lean::inc(x_2248);
lean::dec(x_2192);
lean::inc(x_2);
x_2252 = l_lean_elaborator_to__pexpr___main(x_2248, x_1, x_2, x_2245);
if (lean::obj_tag(x_2252) == 0)
{
obj* x_2259; obj* x_2261; obj* x_2262; 
lean::dec(x_2223);
lean::dec(x_2220);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2243);
x_2259 = lean::cnstr_get(x_2252, 0);
if (lean::is_exclusive(x_2252)) {
 x_2261 = x_2252;
} else {
 lean::inc(x_2259);
 lean::dec(x_2252);
 x_2261 = lean::box(0);
}
if (lean::is_scalar(x_2261)) {
 x_2262 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2262 = x_2261;
}
lean::cnstr_set(x_2262, 0, x_2259);
return x_2262;
}
else
{
obj* x_2263; obj* x_2266; obj* x_2268; obj* x_2270; obj* x_2271; uint8 x_2272; obj* x_2273; obj* x_2274; 
x_2263 = lean::cnstr_get(x_2252, 0);
lean::inc(x_2263);
lean::dec(x_2252);
x_2266 = lean::cnstr_get(x_2263, 0);
x_2268 = lean::cnstr_get(x_2263, 1);
if (lean::is_exclusive(x_2263)) {
 x_2270 = x_2263;
} else {
 lean::inc(x_2266);
 lean::inc(x_2268);
 lean::dec(x_2263);
 x_2270 = lean::box(0);
}
x_2271 = l_lean_elaborator_mangle__ident(x_2223);
x_2272 = lean::unbox(x_2220);
x_2273 = lean_expr_mk_lambda(x_2271, x_2272, x_2243, x_2266);
if (lean::is_scalar(x_2270)) {
 x_2274 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2274 = x_2270;
}
lean::cnstr_set(x_2274, 0, x_2273);
lean::cnstr_set(x_2274, 1, x_2268);
x_15 = x_2274;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2277; obj* x_2278; obj* x_2282; obj* x_2283; obj* x_2286; 
lean::dec(x_8);
lean::dec(x_10);
x_2277 = l_lean_parser_term_app_has__view;
x_2278 = lean::cnstr_get(x_2277, 0);
lean::inc(x_2278);
lean::dec(x_2277);
lean::inc(x_0);
x_2282 = lean::apply_1(x_2278, x_0);
x_2283 = lean::cnstr_get(x_2282, 0);
lean::inc(x_2283);
lean::inc(x_2);
x_2286 = l_lean_elaborator_to__pexpr___main(x_2283, x_1, x_2, x_3);
if (lean::obj_tag(x_2286) == 0)
{
obj* x_2290; obj* x_2292; obj* x_2293; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2282);
x_2290 = lean::cnstr_get(x_2286, 0);
if (lean::is_exclusive(x_2286)) {
 x_2292 = x_2286;
} else {
 lean::inc(x_2290);
 lean::dec(x_2286);
 x_2292 = lean::box(0);
}
if (lean::is_scalar(x_2292)) {
 x_2293 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2293 = x_2292;
}
lean::cnstr_set(x_2293, 0, x_2290);
return x_2293;
}
else
{
obj* x_2294; obj* x_2297; obj* x_2299; obj* x_2302; obj* x_2306; 
x_2294 = lean::cnstr_get(x_2286, 0);
lean::inc(x_2294);
lean::dec(x_2286);
x_2297 = lean::cnstr_get(x_2294, 0);
lean::inc(x_2297);
x_2299 = lean::cnstr_get(x_2294, 1);
lean::inc(x_2299);
lean::dec(x_2294);
x_2302 = lean::cnstr_get(x_2282, 1);
lean::inc(x_2302);
lean::dec(x_2282);
lean::inc(x_2);
x_2306 = l_lean_elaborator_to__pexpr___main(x_2302, x_1, x_2, x_2299);
if (lean::obj_tag(x_2306) == 0)
{
obj* x_2310; obj* x_2312; obj* x_2313; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2297);
x_2310 = lean::cnstr_get(x_2306, 0);
if (lean::is_exclusive(x_2306)) {
 x_2312 = x_2306;
} else {
 lean::inc(x_2310);
 lean::dec(x_2306);
 x_2312 = lean::box(0);
}
if (lean::is_scalar(x_2312)) {
 x_2313 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2313 = x_2312;
}
lean::cnstr_set(x_2313, 0, x_2310);
return x_2313;
}
else
{
obj* x_2314; obj* x_2316; obj* x_2317; obj* x_2319; obj* x_2321; obj* x_2322; 
x_2314 = lean::cnstr_get(x_2306, 0);
if (lean::is_exclusive(x_2306)) {
 lean::cnstr_set(x_2306, 0, lean::box(0));
 x_2316 = x_2306;
} else {
 lean::inc(x_2314);
 lean::dec(x_2306);
 x_2316 = lean::box(0);
}
x_2317 = lean::cnstr_get(x_2314, 0);
x_2319 = lean::cnstr_get(x_2314, 1);
if (lean::is_exclusive(x_2314)) {
 lean::cnstr_set(x_2314, 0, lean::box(0));
 lean::cnstr_set(x_2314, 1, lean::box(0));
 x_2321 = x_2314;
} else {
 lean::inc(x_2317);
 lean::inc(x_2319);
 lean::dec(x_2314);
 x_2321 = lean::box(0);
}
x_2322 = lean_expr_mk_app(x_2297, x_2317);
if (x_20 == 0)
{
obj* x_2323; 
x_2323 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2323) == 0)
{
obj* x_2326; obj* x_2327; 
lean::dec(x_2);
if (lean::is_scalar(x_2321)) {
 x_2326 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2326 = x_2321;
}
lean::cnstr_set(x_2326, 0, x_2322);
lean::cnstr_set(x_2326, 1, x_2319);
if (lean::is_scalar(x_2316)) {
 x_2327 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2327 = x_2316;
}
lean::cnstr_set(x_2327, 0, x_2326);
return x_2327;
}
else
{
obj* x_2328; obj* x_2331; obj* x_2334; obj* x_2337; obj* x_2338; obj* x_2339; obj* x_2341; obj* x_2342; obj* x_2343; obj* x_2346; obj* x_2347; obj* x_2348; obj* x_2349; obj* x_2350; 
x_2328 = lean::cnstr_get(x_2323, 0);
lean::inc(x_2328);
lean::dec(x_2323);
x_2331 = lean::cnstr_get(x_2, 0);
lean::inc(x_2331);
lean::dec(x_2);
x_2334 = lean::cnstr_get(x_2331, 2);
lean::inc(x_2334);
lean::dec(x_2331);
x_2337 = l_lean_file__map_to__position(x_2334, x_2328);
x_2338 = lean::box(0);
x_2339 = lean::cnstr_get(x_2337, 1);
lean::inc(x_2339);
x_2341 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2342 = l_lean_kvmap_set__nat(x_2338, x_2341, x_2339);
x_2343 = lean::cnstr_get(x_2337, 0);
lean::inc(x_2343);
lean::dec(x_2337);
x_2346 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2347 = l_lean_kvmap_set__nat(x_2342, x_2346, x_2343);
x_2348 = lean_expr_mk_mdata(x_2347, x_2322);
if (lean::is_scalar(x_2321)) {
 x_2349 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2349 = x_2321;
}
lean::cnstr_set(x_2349, 0, x_2348);
lean::cnstr_set(x_2349, 1, x_2319);
if (lean::is_scalar(x_2316)) {
 x_2350 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2350 = x_2316;
}
lean::cnstr_set(x_2350, 0, x_2349);
return x_2350;
}
}
else
{
obj* x_2353; obj* x_2354; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2321)) {
 x_2353 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2353 = x_2321;
}
lean::cnstr_set(x_2353, 0, x_2322);
lean::cnstr_set(x_2353, 1, x_2319);
if (lean::is_scalar(x_2316)) {
 x_2354 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2354 = x_2316;
}
lean::cnstr_set(x_2354, 0, x_2353);
return x_2354;
}
}
}
}
}
else
{
obj* x_2356; obj* x_2357; obj* x_2361; obj* x_2362; 
lean::dec(x_10);
x_2356 = l_lean_parser_ident__univs_has__view;
x_2357 = lean::cnstr_get(x_2356, 0);
lean::inc(x_2357);
lean::dec(x_2356);
lean::inc(x_0);
x_2361 = lean::apply_1(x_2357, x_0);
x_2362 = lean::cnstr_get(x_2361, 1);
lean::inc(x_2362);
if (lean::obj_tag(x_2362) == 0)
{
obj* x_2364; obj* x_2368; obj* x_2369; obj* x_2370; obj* x_2371; obj* x_2374; obj* x_2375; obj* x_2376; obj* x_2377; obj* x_2378; obj* x_2379; uint8 x_2380; 
x_2364 = lean::cnstr_get(x_2361, 0);
lean::inc(x_2364);
lean::dec(x_2361);
lean::inc(x_2364);
x_2368 = l_lean_elaborator_mangle__ident(x_2364);
x_2369 = lean::box(0);
x_2370 = lean_expr_mk_const(x_2368, x_2369);
x_2371 = lean::cnstr_get(x_2364, 3);
lean::inc(x_2371);
lean::dec(x_2364);
x_2374 = lean::mk_nat_obj(0u);
x_2375 = l_list_enum__from___main___rarg(x_2374, x_2371);
x_2376 = l_lean_elaborator_to__pexpr___main___closed__47;
x_2377 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(x_2376, x_2375);
x_2378 = lean_expr_mk_mdata(x_2377, x_2370);
x_2379 = l_lean_elaborator_to__pexpr___main___closed__2;
x_2380 = lean_name_dec_eq(x_8, x_2379);
lean::dec(x_8);
if (x_2380 == 0)
{
obj* x_2382; 
x_2382 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2382) == 0)
{
obj* x_2385; obj* x_2386; 
lean::dec(x_2);
x_2385 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2385, 0, x_2378);
lean::cnstr_set(x_2385, 1, x_3);
x_2386 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2386, 0, x_2385);
return x_2386;
}
else
{
obj* x_2387; obj* x_2390; obj* x_2393; obj* x_2396; obj* x_2397; obj* x_2399; obj* x_2400; obj* x_2401; obj* x_2404; obj* x_2405; obj* x_2406; obj* x_2407; obj* x_2408; 
x_2387 = lean::cnstr_get(x_2382, 0);
lean::inc(x_2387);
lean::dec(x_2382);
x_2390 = lean::cnstr_get(x_2, 0);
lean::inc(x_2390);
lean::dec(x_2);
x_2393 = lean::cnstr_get(x_2390, 2);
lean::inc(x_2393);
lean::dec(x_2390);
x_2396 = l_lean_file__map_to__position(x_2393, x_2387);
x_2397 = lean::cnstr_get(x_2396, 1);
lean::inc(x_2397);
x_2399 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2400 = l_lean_kvmap_set__nat(x_2369, x_2399, x_2397);
x_2401 = lean::cnstr_get(x_2396, 0);
lean::inc(x_2401);
lean::dec(x_2396);
x_2404 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2405 = l_lean_kvmap_set__nat(x_2400, x_2404, x_2401);
x_2406 = lean_expr_mk_mdata(x_2405, x_2378);
x_2407 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2407, 0, x_2406);
lean::cnstr_set(x_2407, 1, x_3);
x_2408 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2408, 0, x_2407);
return x_2408;
}
}
else
{
obj* x_2411; obj* x_2412; 
lean::dec(x_0);
lean::dec(x_2);
x_2411 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2411, 0, x_2378);
lean::cnstr_set(x_2411, 1, x_3);
x_2412 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2412, 0, x_2411);
return x_2412;
}
}
else
{
obj* x_2413; obj* x_2416; obj* x_2419; obj* x_2423; 
x_2413 = lean::cnstr_get(x_2361, 0);
lean::inc(x_2413);
lean::dec(x_2361);
x_2416 = lean::cnstr_get(x_2362, 0);
lean::inc(x_2416);
lean::dec(x_2362);
x_2419 = lean::cnstr_get(x_2416, 1);
lean::inc(x_2419);
lean::dec(x_2416);
lean::inc(x_2);
x_2423 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_2419, x_1, x_2, x_3);
if (lean::obj_tag(x_2423) == 0)
{
obj* x_2428; obj* x_2430; obj* x_2431; 
lean::dec(x_2413);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2428 = lean::cnstr_get(x_2423, 0);
if (lean::is_exclusive(x_2423)) {
 x_2430 = x_2423;
} else {
 lean::inc(x_2428);
 lean::dec(x_2423);
 x_2430 = lean::box(0);
}
if (lean::is_scalar(x_2430)) {
 x_2431 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2431 = x_2430;
}
lean::cnstr_set(x_2431, 0, x_2428);
return x_2431;
}
else
{
obj* x_2432; obj* x_2434; obj* x_2435; obj* x_2437; obj* x_2439; obj* x_2441; obj* x_2442; obj* x_2443; obj* x_2446; obj* x_2447; obj* x_2448; obj* x_2449; obj* x_2450; obj* x_2451; uint8 x_2452; 
x_2432 = lean::cnstr_get(x_2423, 0);
if (lean::is_exclusive(x_2423)) {
 lean::cnstr_set(x_2423, 0, lean::box(0));
 x_2434 = x_2423;
} else {
 lean::inc(x_2432);
 lean::dec(x_2423);
 x_2434 = lean::box(0);
}
x_2435 = lean::cnstr_get(x_2432, 0);
x_2437 = lean::cnstr_get(x_2432, 1);
if (lean::is_exclusive(x_2432)) {
 lean::cnstr_set(x_2432, 0, lean::box(0));
 lean::cnstr_set(x_2432, 1, lean::box(0));
 x_2439 = x_2432;
} else {
 lean::inc(x_2435);
 lean::inc(x_2437);
 lean::dec(x_2432);
 x_2439 = lean::box(0);
}
lean::inc(x_2413);
x_2441 = l_lean_elaborator_mangle__ident(x_2413);
x_2442 = lean_expr_mk_const(x_2441, x_2435);
x_2443 = lean::cnstr_get(x_2413, 3);
lean::inc(x_2443);
lean::dec(x_2413);
x_2446 = lean::mk_nat_obj(0u);
x_2447 = l_list_enum__from___main___rarg(x_2446, x_2443);
x_2448 = l_lean_elaborator_to__pexpr___main___closed__47;
x_2449 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(x_2448, x_2447);
x_2450 = lean_expr_mk_mdata(x_2449, x_2442);
x_2451 = l_lean_elaborator_to__pexpr___main___closed__2;
x_2452 = lean_name_dec_eq(x_8, x_2451);
lean::dec(x_8);
if (x_2452 == 0)
{
obj* x_2454; obj* x_2455; 
x_2454 = lean::box(0);
x_2455 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2455) == 0)
{
obj* x_2458; obj* x_2459; 
lean::dec(x_2);
if (lean::is_scalar(x_2439)) {
 x_2458 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2458 = x_2439;
}
lean::cnstr_set(x_2458, 0, x_2450);
lean::cnstr_set(x_2458, 1, x_2437);
if (lean::is_scalar(x_2434)) {
 x_2459 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2459 = x_2434;
}
lean::cnstr_set(x_2459, 0, x_2458);
return x_2459;
}
else
{
obj* x_2460; obj* x_2463; obj* x_2466; obj* x_2469; obj* x_2470; obj* x_2472; obj* x_2473; obj* x_2474; obj* x_2477; obj* x_2478; obj* x_2479; obj* x_2480; obj* x_2481; 
x_2460 = lean::cnstr_get(x_2455, 0);
lean::inc(x_2460);
lean::dec(x_2455);
x_2463 = lean::cnstr_get(x_2, 0);
lean::inc(x_2463);
lean::dec(x_2);
x_2466 = lean::cnstr_get(x_2463, 2);
lean::inc(x_2466);
lean::dec(x_2463);
x_2469 = l_lean_file__map_to__position(x_2466, x_2460);
x_2470 = lean::cnstr_get(x_2469, 1);
lean::inc(x_2470);
x_2472 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2473 = l_lean_kvmap_set__nat(x_2454, x_2472, x_2470);
x_2474 = lean::cnstr_get(x_2469, 0);
lean::inc(x_2474);
lean::dec(x_2469);
x_2477 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2478 = l_lean_kvmap_set__nat(x_2473, x_2477, x_2474);
x_2479 = lean_expr_mk_mdata(x_2478, x_2450);
if (lean::is_scalar(x_2439)) {
 x_2480 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2480 = x_2439;
}
lean::cnstr_set(x_2480, 0, x_2479);
lean::cnstr_set(x_2480, 1, x_2437);
if (lean::is_scalar(x_2434)) {
 x_2481 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2481 = x_2434;
}
lean::cnstr_set(x_2481, 0, x_2480);
return x_2481;
}
}
else
{
obj* x_2484; obj* x_2485; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2439)) {
 x_2484 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2484 = x_2439;
}
lean::cnstr_set(x_2484, 0, x_2450);
lean::cnstr_set(x_2484, 1, x_2437);
if (lean::is_scalar(x_2434)) {
 x_2485 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2485 = x_2434;
}
lean::cnstr_set(x_2485, 0, x_2484);
return x_2485;
}
}
}
}
lbl_14:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_2489; obj* x_2491; obj* x_2492; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2489 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_2491 = x_13;
} else {
 lean::inc(x_2489);
 lean::dec(x_13);
 x_2491 = lean::box(0);
}
if (lean::is_scalar(x_2491)) {
 x_2492 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2492 = x_2491;
}
lean::cnstr_set(x_2492, 0, x_2489);
return x_2492;
}
else
{
obj* x_2493; obj* x_2495; obj* x_2496; obj* x_2498; obj* x_2500; obj* x_2501; uint8 x_2502; 
x_2493 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_2495 = x_13;
} else {
 lean::inc(x_2493);
 lean::dec(x_13);
 x_2495 = lean::box(0);
}
x_2496 = lean::cnstr_get(x_2493, 0);
x_2498 = lean::cnstr_get(x_2493, 1);
if (lean::is_exclusive(x_2493)) {
 lean::cnstr_set(x_2493, 0, lean::box(0));
 lean::cnstr_set(x_2493, 1, lean::box(0));
 x_2500 = x_2493;
} else {
 lean::inc(x_2496);
 lean::inc(x_2498);
 lean::dec(x_2493);
 x_2500 = lean::box(0);
}
x_2501 = l_lean_elaborator_to__pexpr___main___closed__2;
x_2502 = lean_name_dec_eq(x_8, x_2501);
lean::dec(x_8);
if (x_2502 == 0)
{
obj* x_2504; 
x_2504 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2504) == 0)
{
obj* x_2507; obj* x_2508; 
lean::dec(x_2);
if (lean::is_scalar(x_2500)) {
 x_2507 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2507 = x_2500;
}
lean::cnstr_set(x_2507, 0, x_2496);
lean::cnstr_set(x_2507, 1, x_2498);
if (lean::is_scalar(x_2495)) {
 x_2508 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2508 = x_2495;
}
lean::cnstr_set(x_2508, 0, x_2507);
return x_2508;
}
else
{
obj* x_2509; obj* x_2512; obj* x_2515; obj* x_2518; obj* x_2519; obj* x_2520; obj* x_2522; obj* x_2523; obj* x_2524; obj* x_2527; obj* x_2528; obj* x_2529; obj* x_2530; obj* x_2531; 
x_2509 = lean::cnstr_get(x_2504, 0);
lean::inc(x_2509);
lean::dec(x_2504);
x_2512 = lean::cnstr_get(x_2, 0);
lean::inc(x_2512);
lean::dec(x_2);
x_2515 = lean::cnstr_get(x_2512, 2);
lean::inc(x_2515);
lean::dec(x_2512);
x_2518 = l_lean_file__map_to__position(x_2515, x_2509);
x_2519 = lean::box(0);
x_2520 = lean::cnstr_get(x_2518, 1);
lean::inc(x_2520);
x_2522 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2523 = l_lean_kvmap_set__nat(x_2519, x_2522, x_2520);
x_2524 = lean::cnstr_get(x_2518, 0);
lean::inc(x_2524);
lean::dec(x_2518);
x_2527 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2528 = l_lean_kvmap_set__nat(x_2523, x_2527, x_2524);
x_2529 = lean_expr_mk_mdata(x_2528, x_2496);
if (lean::is_scalar(x_2500)) {
 x_2530 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2530 = x_2500;
}
lean::cnstr_set(x_2530, 0, x_2529);
lean::cnstr_set(x_2530, 1, x_2498);
if (lean::is_scalar(x_2495)) {
 x_2531 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2531 = x_2495;
}
lean::cnstr_set(x_2531, 0, x_2530);
return x_2531;
}
}
else
{
obj* x_2534; obj* x_2535; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2500)) {
 x_2534 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2534 = x_2500;
}
lean::cnstr_set(x_2534, 0, x_2496);
lean::cnstr_set(x_2534, 1, x_2498);
if (lean::is_scalar(x_2495)) {
 x_2535 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2535 = x_2495;
}
lean::cnstr_set(x_2535, 0, x_2534);
return x_2535;
}
}
}
lbl_16:
{
obj* x_2536; obj* x_2538; obj* x_2540; obj* x_2541; uint8 x_2542; 
x_2536 = lean::cnstr_get(x_15, 0);
x_2538 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_2540 = x_15;
} else {
 lean::inc(x_2536);
 lean::inc(x_2538);
 lean::dec(x_15);
 x_2540 = lean::box(0);
}
x_2541 = l_lean_elaborator_to__pexpr___main___closed__2;
x_2542 = lean_name_dec_eq(x_8, x_2541);
lean::dec(x_8);
if (x_2542 == 0)
{
obj* x_2544; 
x_2544 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2544) == 0)
{
obj* x_2547; obj* x_2548; 
lean::dec(x_2);
if (lean::is_scalar(x_2540)) {
 x_2547 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2547 = x_2540;
}
lean::cnstr_set(x_2547, 0, x_2536);
lean::cnstr_set(x_2547, 1, x_2538);
x_2548 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2548, 0, x_2547);
return x_2548;
}
else
{
obj* x_2549; obj* x_2552; obj* x_2555; obj* x_2558; obj* x_2559; obj* x_2560; obj* x_2562; obj* x_2563; obj* x_2564; obj* x_2567; obj* x_2568; obj* x_2569; obj* x_2570; obj* x_2571; 
x_2549 = lean::cnstr_get(x_2544, 0);
lean::inc(x_2549);
lean::dec(x_2544);
x_2552 = lean::cnstr_get(x_2, 0);
lean::inc(x_2552);
lean::dec(x_2);
x_2555 = lean::cnstr_get(x_2552, 2);
lean::inc(x_2555);
lean::dec(x_2552);
x_2558 = l_lean_file__map_to__position(x_2555, x_2549);
x_2559 = lean::box(0);
x_2560 = lean::cnstr_get(x_2558, 1);
lean::inc(x_2560);
x_2562 = l_lean_elaborator_to__pexpr___main___closed__3;
x_2563 = l_lean_kvmap_set__nat(x_2559, x_2562, x_2560);
x_2564 = lean::cnstr_get(x_2558, 0);
lean::inc(x_2564);
lean::dec(x_2558);
x_2567 = l_lean_elaborator_to__pexpr___main___closed__4;
x_2568 = l_lean_kvmap_set__nat(x_2563, x_2567, x_2564);
x_2569 = lean_expr_mk_mdata(x_2568, x_2536);
if (lean::is_scalar(x_2540)) {
 x_2570 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2570 = x_2540;
}
lean::cnstr_set(x_2570, 0, x_2569);
lean::cnstr_set(x_2570, 1, x_2538);
x_2571 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2571, 0, x_2570);
return x_2571;
}
}
else
{
obj* x_2574; obj* x_2575; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2540)) {
 x_2574 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2574 = x_2540;
}
lean::cnstr_set(x_2574, 0, x_2536);
lean::cnstr_set(x_2574, 1, x_2538);
x_2575 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2575, 0, x_2574);
return x_2575;
}
}
}
default:
{
obj* x_2576; 
x_2576 = lean::box(0);
x_4 = x_2576;
goto lbl_5;
}
}
lbl_5:
{
obj* x_2579; obj* x_2580; obj* x_2581; obj* x_2582; obj* x_2583; obj* x_2584; obj* x_2586; 
lean::dec(x_4);
lean::inc(x_0);
x_2579 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2579, 0, x_0);
x_2580 = l_lean_parser_syntax_to__format___main(x_0);
x_2581 = lean::mk_nat_obj(80u);
x_2582 = l_lean_format_pretty(x_2580, x_2581);
x_2583 = l_lean_elaborator_to__pexpr___main___closed__1;
x_2584 = lean::string_append(x_2583, x_2582);
lean::dec(x_2582);
x_2586 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_2579, x_2584, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2579);
return x_2586;
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_17 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(x_0, x_10, x_2, x_16);
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
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__7(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
return x_1;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(x_0, x_1, x_8, x_10);
x_1 = x_13;
x_2 = x_5;
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
x_3 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8(x_1, x_2, x_0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_17 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12(x_0, x_10, x_2, x_16);
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
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__15(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_ordered__rbmap_empty___closed__1;
return x_1;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10(x_0, x_1, x_8, x_10);
x_1 = x_13;
x_2 = x_5;
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
x_3 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16(x_1, x_2, x_0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19(x_0, x_1, x_2, x_3);
return x_4;
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
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__17(x_4);
x_9 = lean::box(0);
x_10 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19(x_7, x_8, x_2, x_9);
return x_10;
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
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__7___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__7(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__8(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__13(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__14(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__12(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__11(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__10(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__15___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__15(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__16(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__20(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__21(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__19(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__18(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
x_1 = lean::mk_string("unsafe");
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
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_fix__1___rarg___lambda__1___boxed), 2, 1);
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
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_18; 
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
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::inc(x_3);
x_18 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_15, x_2, x_3, x_4);
if (lean::obj_tag(x_18) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_12);
x_24 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_26 = x_18;
} else {
 lean::inc(x_24);
 lean::dec(x_18);
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
obj* x_28; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_40; 
x_28 = lean::cnstr_get(x_18, 0);
lean::inc(x_28);
lean::dec(x_18);
x_31 = lean::cnstr_get(x_28, 0);
x_33 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_set(x_28, 0, lean::box(0));
 lean::cnstr_set(x_28, 1, lean::box(0));
 x_35 = x_28;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_28);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_10, 3);
lean::inc(x_36);
lean::dec(x_10);
lean::inc(x_3);
x_40 = l_lean_elaborator_to__pexpr___main(x_36, x_2, x_3, x_33);
if (lean::obj_tag(x_40) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_35);
lean::dec(x_31);
x_47 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_49 = x_40;
} else {
 lean::inc(x_47);
 lean::dec(x_40);
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
obj* x_51; obj* x_54; obj* x_56; obj* x_58; obj* x_60; 
x_51 = lean::cnstr_get(x_40, 0);
lean::inc(x_51);
lean::dec(x_40);
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
lean::inc(x_0);
x_60 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_0, x_12, x_2, x_3, x_56);
if (lean::obj_tag(x_60) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_35);
lean::dec(x_31);
lean::dec(x_54);
lean::dec(x_58);
x_67 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_69 = x_60;
} else {
 lean::inc(x_67);
 lean::dec(x_60);
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
obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_71 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_73 = x_60;
} else {
 lean::inc(x_71);
 lean::dec(x_60);
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
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_31);
lean::cnstr_set(x_79, 1, x_54);
if (lean::is_scalar(x_58)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_58;
}
lean::cnstr_set(x_80, 0, x_0);
lean::cnstr_set(x_80, 1, x_79);
if (lean::is_scalar(x_14)) {
 x_81 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_81 = x_14;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_74);
if (lean::is_scalar(x_35)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_35;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_76);
if (lean::is_scalar(x_73)) {
 x_83 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_83 = x_73;
}
lean::cnstr_set(x_83, 0, x_82);
return x_83;
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
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
x_3 = lean::box(0);
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 2);
lean::inc(x_12);
lean::dec(x_0);
lean::inc(x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_2);
x_17 = l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6(x_3, x_10, x_1, x_16);
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
lean::dec(x_23);
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
obj* x_189; obj* x_192; obj* x_196; 
lean::dec(x_170);
lean::dec(x_175);
lean::dec(x_166);
x_189 = lean::cnstr_get(x_25, 0);
lean::inc(x_189);
lean::dec(x_25);
x_192 = lean::cnstr_get(x_189, 1);
lean::inc(x_192);
lean::dec(x_189);
lean::inc(x_5);
x_196 = l_lean_elaborator_to__pexpr___main(x_192, x_4, x_5, x_168);
if (lean::obj_tag(x_196) == 0)
{
obj* x_204; obj* x_206; obj* x_207; 
lean::dec(x_183);
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_51);
lean::dec(x_171);
x_204 = lean::cnstr_get(x_196, 0);
if (lean::is_exclusive(x_196)) {
 x_206 = x_196;
} else {
 lean::inc(x_204);
 lean::dec(x_196);
 x_206 = lean::box(0);
}
if (lean::is_scalar(x_206)) {
 x_207 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_207 = x_206;
}
lean::cnstr_set(x_207, 0, x_204);
return x_207;
}
else
{
obj* x_208; 
x_208 = lean::cnstr_get(x_196, 0);
lean::inc(x_208);
lean::dec(x_196);
x_184 = x_208;
goto lbl_185;
}
}
case 1:
{
obj* x_213; obj* x_214; 
lean::dec(x_175);
lean::dec(x_25);
x_213 = l_lean_elaborator_mk__eqns(x_166, x_56);
if (lean::is_scalar(x_170)) {
 x_214 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_214 = x_170;
}
lean::cnstr_set(x_214, 0, x_213);
lean::cnstr_set(x_214, 1, x_168);
x_184 = x_214;
goto lbl_185;
}
default:
{
obj* x_216; obj* x_220; 
lean::dec(x_170);
x_216 = lean::cnstr_get(x_25, 0);
lean::inc(x_216);
lean::dec(x_25);
lean::inc(x_5);
x_220 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_175, x_216, x_4, x_5, x_168);
if (lean::obj_tag(x_220) == 0)
{
obj* x_229; obj* x_231; obj* x_232; 
lean::dec(x_183);
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_51);
lean::dec(x_166);
lean::dec(x_171);
x_229 = lean::cnstr_get(x_220, 0);
if (lean::is_exclusive(x_220)) {
 x_231 = x_220;
} else {
 lean::inc(x_229);
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
obj* x_233; obj* x_236; obj* x_238; obj* x_240; obj* x_241; obj* x_242; 
x_233 = lean::cnstr_get(x_220, 0);
lean::inc(x_233);
lean::dec(x_220);
x_236 = lean::cnstr_get(x_233, 0);
x_238 = lean::cnstr_get(x_233, 1);
if (lean::is_exclusive(x_233)) {
 x_240 = x_233;
} else {
 lean::inc(x_236);
 lean::inc(x_238);
 lean::dec(x_233);
 x_240 = lean::box(0);
}
x_241 = l_lean_elaborator_mk__eqns(x_166, x_236);
if (lean::is_scalar(x_240)) {
 x_242 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_242 = x_240;
}
lean::cnstr_set(x_242, 0, x_241);
lean::cnstr_set(x_242, 1, x_238);
x_184 = x_242;
goto lbl_185;
}
}
}
lbl_185:
{
obj* x_243; obj* x_245; obj* x_249; 
x_243 = lean::cnstr_get(x_184, 0);
lean::inc(x_243);
x_245 = lean::cnstr_get(x_184, 1);
lean::inc(x_245);
lean::dec(x_184);
lean::inc(x_5);
x_249 = l_lean_elaborator_simple__binders__to__pexpr(x_31, x_4, x_5, x_245);
if (lean::obj_tag(x_249) == 0)
{
obj* x_257; obj* x_259; obj* x_260; 
lean::dec(x_243);
lean::dec(x_183);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_51);
lean::dec(x_171);
x_257 = lean::cnstr_get(x_249, 0);
if (lean::is_exclusive(x_249)) {
 x_259 = x_249;
} else {
 lean::inc(x_257);
 lean::dec(x_249);
 x_259 = lean::box(0);
}
if (lean::is_scalar(x_259)) {
 x_260 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_260 = x_259;
}
lean::cnstr_set(x_260, 0, x_257);
return x_260;
}
else
{
obj* x_261; obj* x_264; obj* x_266; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; 
x_261 = lean::cnstr_get(x_249, 0);
lean::inc(x_261);
lean::dec(x_249);
x_264 = lean::cnstr_get(x_261, 0);
lean::inc(x_264);
x_266 = lean::cnstr_get(x_261, 1);
lean::inc(x_266);
lean::dec(x_261);
x_269 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_269, 0, x_243);
lean::cnstr_set(x_269, 1, x_56);
x_270 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_270, 0, x_264);
lean::cnstr_set(x_270, 1, x_269);
x_271 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_271, 0, x_183);
lean::cnstr_set(x_271, 1, x_270);
x_272 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_272, 0, x_171);
lean::cnstr_set(x_272, 1, x_271);
x_273 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_273, 0, x_58);
lean::cnstr_set(x_273, 1, x_272);
x_274 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_274, 0, x_51);
lean::cnstr_set(x_274, 1, x_273);
x_275 = l_lean_expr_mk__capp(x_182, x_274);
x_276 = l_lean_elaborator_elab__def__like___closed__2;
x_277 = lean_expr_mk_mdata(x_276, x_275);
x_278 = l_lean_elaborator_old__elab__command(x_0, x_277, x_4, x_5, x_266);
lean::dec(x_0);
return x_278;
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
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__7(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_elab__def__like___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_elab__def__like___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_insert___main___at_lean_elaborator_elab__def__like___spec__5(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
x_4 = lean::mk_string("axiom");
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
case 3:
{
obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_17);
x_27 = lean::cnstr_get(x_11, 0);
lean::inc(x_27);
lean::dec(x_11);
x_30 = lean::mk_nat_obj(0u);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___boxed), 7, 4);
lean::closure_set(x_31, 0, x_0);
lean::closure_set(x_31, 1, x_27);
lean::closure_set(x_31, 2, x_14);
lean::closure_set(x_31, 3, x_30);
x_32 = l_lean_elaborator_locally(x_31, x_1, x_2, x_3);
return x_32;
}
case 4:
{
obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_17);
x_34 = lean::cnstr_get(x_11, 0);
lean::inc(x_34);
lean::dec(x_11);
x_37 = lean::mk_nat_obj(2u);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___boxed), 7, 4);
lean::closure_set(x_38, 0, x_0);
lean::closure_set(x_38, 1, x_34);
lean::closure_set(x_38, 2, x_14);
lean::closure_set(x_38, 3, x_37);
x_39 = l_lean_elaborator_locally(x_38, x_1, x_2, x_3);
return x_39;
}
default:
{
obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_17);
x_41 = lean::cnstr_get(x_11, 0);
lean::inc(x_41);
lean::dec(x_11);
x_44 = lean::mk_nat_obj(6u);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___boxed), 7, 4);
lean::closure_set(x_45, 0, x_0);
lean::closure_set(x_45, 1, x_41);
lean::closure_set(x_45, 2, x_14);
lean::closure_set(x_45, 3, x_44);
x_46 = l_lean_elaborator_locally(x_45, x_1, x_2, x_3);
return x_46;
}
}
}
case 1:
{
obj* x_47; obj* x_50; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_63; obj* x_66; obj* x_67; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_47 = lean::cnstr_get(x_12, 0);
lean::inc(x_47);
lean::dec(x_12);
x_50 = lean::cnstr_get(x_11, 0);
lean::inc(x_50);
lean::dec(x_11);
x_53 = lean::box(0);
x_54 = lean::cnstr_get(x_47, 1);
lean::inc(x_54);
x_56 = l_lean_elaborator_declaration_elaborate___closed__1;
x_57 = l_option_get__or__else___main___rarg(x_54, x_56);
lean::dec(x_54);
x_59 = lean::cnstr_get(x_47, 2);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_59, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_59, 1);
lean::inc(x_63);
lean::dec(x_59);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_63);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_61);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::cnstr_get(x_47, 3);
lean::inc(x_68);
lean::dec(x_47);
x_71 = l_lean_elaborator_declaration_elaborate___closed__2;
x_72 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_53);
lean::cnstr_set(x_72, 2, x_57);
lean::cnstr_set(x_72, 3, x_67);
lean::cnstr_set(x_72, 4, x_68);
x_73 = lean::mk_nat_obj(4u);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___boxed), 7, 4);
lean::closure_set(x_74, 0, x_0);
lean::closure_set(x_74, 1, x_50);
lean::closure_set(x_74, 2, x_72);
lean::closure_set(x_74, 3, x_73);
x_75 = l_lean_elaborator_locally(x_74, x_1, x_2, x_3);
return x_75;
}
case 2:
{
obj* x_76; obj* x_79; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_76 = lean::cnstr_get(x_12, 0);
lean::inc(x_76);
lean::dec(x_12);
x_79 = lean::cnstr_get(x_11, 0);
lean::inc(x_79);
lean::dec(x_11);
x_82 = lean::box(0);
x_83 = lean::cnstr_get(x_76, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_83, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_83, 1);
lean::inc(x_87);
lean::dec(x_83);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_85);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::cnstr_get(x_76, 2);
lean::inc(x_92);
lean::dec(x_76);
x_95 = l_lean_elaborator_declaration_elaborate___closed__2;
x_96 = l_lean_elaborator_declaration_elaborate___closed__1;
x_97 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_97, 0, x_95);
lean::cnstr_set(x_97, 1, x_82);
lean::cnstr_set(x_97, 2, x_96);
lean::cnstr_set(x_97, 3, x_91);
lean::cnstr_set(x_97, 4, x_92);
x_98 = lean::mk_nat_obj(3u);
x_99 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_elab__def__like___boxed), 7, 4);
lean::closure_set(x_99, 0, x_0);
lean::closure_set(x_99, 1, x_79);
lean::closure_set(x_99, 2, x_97);
lean::closure_set(x_99, 3, x_98);
x_100 = l_lean_elaborator_locally(x_99, x_1, x_2, x_3);
return x_100;
}
case 3:
{
obj* x_101; obj* x_104; obj* x_106; 
x_101 = lean::cnstr_get(x_12, 0);
lean::inc(x_101);
lean::dec(x_12);
x_104 = lean::cnstr_get(x_101, 2);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_104, 0);
lean::inc(x_106);
if (lean::obj_tag(x_106) == 0)
{
obj* x_112; 
lean::dec(x_11);
lean::dec(x_104);
lean::dec(x_106);
lean::dec(x_101);
x_112 = lean::box(0);
x_4 = x_112;
goto lbl_5;
}
else
{
obj* x_113; 
x_113 = lean::cnstr_get(x_106, 0);
lean::inc(x_113);
lean::dec(x_106);
if (lean::obj_tag(x_113) == 0)
{
obj* x_116; obj* x_119; obj* x_122; obj* x_123; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_116 = lean::cnstr_get(x_101, 1);
lean::inc(x_116);
lean::dec(x_101);
x_119 = lean::cnstr_get(x_104, 1);
lean::inc(x_119);
lean::dec(x_104);
x_122 = lean::box(0);
x_123 = lean::cnstr_get(x_11, 0);
lean::inc(x_123);
lean::dec(x_11);
x_126 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_decl__modifiers__to__pexpr___boxed), 4, 1);
lean::closure_set(x_126, 0, x_123);
x_127 = l_lean_elaborator_declaration_elaborate___closed__3;
x_128 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_declaration_elaborate___lambda__1___boxed), 9, 5);
lean::closure_set(x_128, 0, x_119);
lean::closure_set(x_128, 1, x_116);
lean::closure_set(x_128, 2, x_122);
lean::closure_set(x_128, 3, x_127);
lean::closure_set(x_128, 4, x_0);
x_129 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_129, 0, x_126);
lean::closure_set(x_129, 1, x_128);
x_130 = l_lean_elaborator_locally(x_129, x_1, x_2, x_3);
return x_130;
}
else
{
obj* x_135; 
lean::dec(x_11);
lean::dec(x_113);
lean::dec(x_104);
lean::dec(x_101);
x_135 = lean::box(0);
x_4 = x_135;
goto lbl_5;
}
}
}
case 4:
{
obj* x_136; obj* x_139; 
x_136 = lean::cnstr_get(x_12, 0);
lean::inc(x_136);
lean::dec(x_12);
x_139 = lean::cnstr_get(x_136, 0);
lean::inc(x_139);
if (lean::obj_tag(x_139) == 0)
{
obj* x_141; obj* x_143; 
x_141 = lean::cnstr_get(x_136, 4);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_141, 0);
lean::inc(x_143);
if (lean::obj_tag(x_143) == 0)
{
obj* x_149; 
lean::dec(x_143);
lean::dec(x_141);
lean::dec(x_11);
lean::dec(x_136);
x_149 = lean::box(0);
x_4 = x_149;
goto lbl_5;
}
else
{
obj* x_150; obj* x_152; obj* x_154; obj* x_157; obj* x_160; obj* x_163; obj* x_164; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
x_150 = lean::cnstr_get(x_136, 2);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_136, 3);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_136, 6);
lean::inc(x_154);
lean::dec(x_136);
x_157 = lean::cnstr_get(x_141, 1);
lean::inc(x_157);
lean::dec(x_141);
x_160 = lean::cnstr_get(x_143, 0);
lean::inc(x_160);
lean::dec(x_143);
x_163 = lean::box(0);
x_164 = lean::cnstr_get(x_11, 0);
lean::inc(x_164);
lean::dec(x_11);
lean::inc(x_164);
x_168 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_decl__modifiers__to__pexpr___boxed), 4, 1);
lean::closure_set(x_168, 0, x_164);
x_169 = l_lean_elaborator_declaration_elaborate___closed__4;
x_170 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_declaration_elaborate___lambda__3___boxed), 13, 9);
lean::closure_set(x_170, 0, x_163);
lean::closure_set(x_170, 1, x_160);
lean::closure_set(x_170, 2, x_0);
lean::closure_set(x_170, 3, x_154);
lean::closure_set(x_170, 4, x_152);
lean::closure_set(x_170, 5, x_169);
lean::closure_set(x_170, 6, x_150);
lean::closure_set(x_170, 7, x_157);
lean::closure_set(x_170, 8, x_164);
x_171 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_171, 0, x_168);
lean::closure_set(x_171, 1, x_170);
x_172 = l_lean_elaborator_locally(x_171, x_1, x_2, x_3);
return x_172;
}
}
else
{
obj* x_176; 
lean::dec(x_11);
lean::dec(x_139);
lean::dec(x_136);
x_176 = lean::box(0);
x_4 = x_176;
goto lbl_5;
}
}
default:
{
obj* x_177; obj* x_180; 
x_177 = lean::cnstr_get(x_12, 0);
lean::inc(x_177);
lean::dec(x_12);
x_180 = lean::cnstr_get(x_177, 0);
lean::inc(x_180);
if (lean::obj_tag(x_180) == 0)
{
obj* x_183; obj* x_185; 
lean::dec(x_180);
x_183 = lean::cnstr_get(x_177, 3);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_183, 0);
lean::inc(x_185);
if (lean::obj_tag(x_185) == 0)
{
obj* x_191; 
lean::dec(x_183);
lean::dec(x_177);
lean::dec(x_185);
lean::dec(x_11);
x_191 = lean::box(0);
x_4 = x_191;
goto lbl_5;
}
else
{
obj* x_192; obj* x_194; obj* x_196; obj* x_198; obj* x_200; obj* x_203; obj* x_206; obj* x_209; obj* x_210; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; 
x_192 = lean::cnstr_get(x_177, 1);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_177, 2);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_177, 4);
lean::inc(x_196);
x_198 = lean::cnstr_get(x_177, 6);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_177, 7);
lean::inc(x_200);
lean::dec(x_177);
x_203 = lean::cnstr_get(x_183, 1);
lean::inc(x_203);
lean::dec(x_183);
x_206 = lean::cnstr_get(x_185, 0);
lean::inc(x_206);
lean::dec(x_185);
x_209 = lean::box(0);
x_210 = lean::cnstr_get(x_11, 0);
lean::inc(x_210);
lean::dec(x_11);
x_213 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_decl__modifiers__to__pexpr___boxed), 4, 1);
lean::closure_set(x_213, 0, x_210);
x_214 = l_lean_elaborator_declaration_elaborate___closed__5;
x_215 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_declaration_elaborate___lambda__5___boxed), 14, 10);
lean::closure_set(x_215, 0, x_206);
lean::closure_set(x_215, 1, x_194);
lean::closure_set(x_215, 2, x_0);
lean::closure_set(x_215, 3, x_200);
lean::closure_set(x_215, 4, x_198);
lean::closure_set(x_215, 5, x_209);
lean::closure_set(x_215, 6, x_214);
lean::closure_set(x_215, 7, x_196);
lean::closure_set(x_215, 8, x_192);
lean::closure_set(x_215, 9, x_203);
x_216 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_elaborator_declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_216, 0, x_213);
lean::closure_set(x_216, 1, x_215);
x_217 = l_lean_elaborator_locally(x_216, x_1, x_2, x_3);
return x_217;
}
}
else
{
obj* x_221; 
lean::dec(x_180);
lean::dec(x_177);
lean::dec(x_11);
x_221 = lean::box(0);
x_4 = x_221;
goto lbl_5;
}
}
}
lbl_5:
{
obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
lean::dec(x_4);
x_223 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_223, 0, x_0);
x_224 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__2___closed__1;
x_225 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg___boxed), 5, 2);
lean::closure_set(x_225, 0, x_223);
lean::closure_set(x_225, 1, x_224);
x_226 = l_lean_elaborator_locally(x_225, x_1, x_2, x_3);
return x_226;
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
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; uint8 x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 3);
lean::inc(x_11);
lean::dec(x_2);
x_14 = l_lean_name_quick__lt(x_3, x_7);
if (x_14 == 0)
{
uint8 x_16; 
lean::dec(x_5);
x_16 = l_lean_name_quick__lt(x_7, x_3);
lean::dec(x_7);
if (x_16 == 0)
{
obj* x_19; 
lean::dec(x_11);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_9);
return x_19;
}
else
{
lean::dec(x_9);
x_1 = x_0;
x_2 = x_11;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
x_1 = x_0;
x_2 = x_5;
goto _start;
}
}
}
}
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
x_2 = lean::box(0);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3(x_2, lean::box(0), x_3, x_1);
return x_6;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
x_3 = lean::box(0);
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 2);
lean::inc(x_12);
lean::dec(x_0);
lean::inc(x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_2);
x_17 = l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6(x_3, x_10, x_1, x_16);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_23; obj* x_25; obj* x_26; uint8 x_27; 
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
x_26 = l_lean_expander_binding__annotation__update;
x_27 = l_lean_parser_syntax_is__of__kind___main(x_26, x_23);
lean::dec(x_23);
if (x_27 == 0)
{
uint8 x_31; obj* x_32; obj* x_33; 
lean::dec(x_18);
lean::dec(x_21);
x_31 = 1;
x_32 = lean::box(x_31);
if (lean::is_scalar(x_25)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_25;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_3);
x_12 = x_33;
goto lbl_13;
}
else
{
obj* x_36; 
lean::dec(x_25);
lean::inc(x_2);
x_36 = l_lean_elaborator_current__scope(x_1, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_18);
lean::dec(x_21);
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
obj* x_47; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_59; 
x_47 = lean::cnstr_get(x_36, 0);
lean::inc(x_47);
lean::dec(x_36);
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
lean::dec(x_47);
x_55 = l_lean_elaborator_mangle__ident(x_21);
x_56 = lean::cnstr_get(x_50, 4);
lean::inc(x_56);
lean::dec(x_50);
x_59 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(x_56, x_55);
if (lean::obj_tag(x_59) == 0)
{
obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_18);
x_61 = lean::box(0);
x_62 = l_lean_name_to__string___closed__1;
lean::inc(x_55);
x_64 = l_lean_name_to__string__with__sep___main(x_62, x_55);
x_65 = l_lean_parser_substring_of__string(x_64);
x_66 = lean::box(0);
x_67 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_67, 0, x_61);
lean::cnstr_set(x_67, 1, x_65);
lean::cnstr_set(x_67, 2, x_55);
lean::cnstr_set(x_67, 3, x_66);
lean::cnstr_set(x_67, 4, x_66);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = l_string_iterator_extract___main___closed__1;
lean::inc(x_2);
x_72 = l_lean_expander_error___at_lean_elaborator_current__scope___spec__1___rarg(x_69, x_70, x_1, x_2, x_52);
lean::dec(x_52);
lean::dec(x_69);
if (lean::obj_tag(x_72) == 0)
{
obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
x_79 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_81 = x_72;
} else {
 lean::inc(x_79);
 lean::dec(x_72);
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
obj* x_83; obj* x_86; obj* x_88; uint8 x_89; obj* x_90; obj* x_91; 
x_83 = lean::cnstr_get(x_72, 0);
lean::inc(x_83);
lean::dec(x_72);
x_86 = lean::cnstr_get(x_83, 1);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 x_88 = x_83;
} else {
 lean::inc(x_86);
 lean::dec(x_83);
 x_88 = lean::box(0);
}
x_89 = 0;
x_90 = lean::box(x_89);
if (lean::is_scalar(x_88)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_88;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_86);
x_12 = x_91;
goto lbl_13;
}
}
else
{
obj* x_92; obj* x_95; obj* x_98; obj* x_100; 
x_92 = lean::cnstr_get(x_59, 0);
lean::inc(x_92);
lean::dec(x_59);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
lean::dec(x_92);
x_98 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9___lambda__1___boxed), 4, 3);
lean::closure_set(x_98, 0, x_95);
lean::closure_set(x_98, 1, x_18);
lean::closure_set(x_98, 2, x_55);
lean::inc(x_2);
x_100 = l_lean_elaborator_modify__current__scope(x_98, x_1, x_2, x_52);
if (lean::obj_tag(x_100) == 0)
{
obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
x_105 = lean::cnstr_get(x_100, 0);
if (lean::is_exclusive(x_100)) {
 x_107 = x_100;
} else {
 lean::inc(x_105);
 lean::dec(x_100);
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
obj* x_109; obj* x_112; obj* x_114; uint8 x_115; obj* x_116; obj* x_117; 
x_109 = lean::cnstr_get(x_100, 0);
lean::inc(x_109);
lean::dec(x_100);
x_112 = lean::cnstr_get(x_109, 1);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 x_114 = x_109;
} else {
 lean::inc(x_112);
 lean::dec(x_109);
 x_114 = lean::box(0);
}
x_115 = 0;
x_116 = lean::box(x_115);
if (lean::is_scalar(x_114)) {
 x_117 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_117 = x_114;
}
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_112);
x_12 = x_117;
goto lbl_13;
}
}
}
}
lbl_13:
{
obj* x_118; obj* x_120; obj* x_123; 
x_118 = lean::cnstr_get(x_12, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_12, 1);
lean::inc(x_120);
lean::dec(x_12);
x_123 = l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__9(x_9, x_1, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_127; obj* x_129; obj* x_130; 
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_118);
x_127 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_129 = x_123;
} else {
 lean::inc(x_127);
 lean::dec(x_123);
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
obj* x_131; obj* x_133; uint8 x_134; 
x_131 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_set(x_123, 0, lean::box(0));
 x_133 = x_123;
} else {
 lean::inc(x_131);
 lean::dec(x_123);
 x_133 = lean::box(0);
}
x_134 = lean::unbox(x_118);
if (x_134 == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_143; 
lean::dec(x_7);
lean::dec(x_11);
x_137 = lean::cnstr_get(x_131, 0);
x_139 = lean::cnstr_get(x_131, 1);
if (lean::is_exclusive(x_131)) {
 x_141 = x_131;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_131);
 x_141 = lean::box(0);
}
if (lean::is_scalar(x_141)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_141;
}
lean::cnstr_set(x_142, 0, x_137);
lean::cnstr_set(x_142, 1, x_139);
if (lean::is_scalar(x_133)) {
 x_143 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_143 = x_133;
}
lean::cnstr_set(x_143, 0, x_142);
return x_143;
}
else
{
obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_144 = lean::cnstr_get(x_131, 0);
x_146 = lean::cnstr_get(x_131, 1);
if (lean::is_exclusive(x_131)) {
 x_148 = x_131;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::dec(x_131);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_11;
}
lean::cnstr_set(x_149, 0, x_7);
lean::cnstr_set(x_149, 1, x_144);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
if (lean::is_scalar(x_133)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_133;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
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
obj* l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___main___at_lean_elaborator_variables_elaborate___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_find___main___at_lean_elaborator_variables_elaborate___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
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
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__7(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_variables_elaborate___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_variables_elaborate___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_insert___main___at_lean_elaborator_variables_elaborate___spec__5(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("register_notation_parser: unreachable");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2() {
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
obj* _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3() {
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
obj* _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4() {
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
obj* _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("register_notation_parser: unimplemented");
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
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
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; 
lean::dec(x_2);
x_15 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
x_7 = x_15;
goto lbl_8;
}
else
{
obj* x_16; obj* x_19; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
lean::dec(x_11);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = l_string_trim(x_19);
lean::dec(x_19);
lean::inc(x_22);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_25, 0, x_22);
x_26 = lean::mk_nat_obj(0u);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed), 8, 3);
lean::closure_set(x_27, 0, x_22);
lean::closure_set(x_27, 1, x_26);
lean::closure_set(x_27, 2, x_25);
x_30 = lean::cnstr_get(x_2, 1);
lean::inc(x_30);
lean::dec(x_2);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; 
x_33 = l_lean_expander_no__expansion___closed__1;
x_28 = x_33;
goto lbl_29;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
switch (lean::obj_tag(x_34)) {
case 0:
{
obj* x_38; 
lean::dec(x_34);
x_38 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2;
x_28 = x_38;
goto lbl_29;
}
case 1:
{
obj* x_40; 
lean::dec(x_34);
x_40 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3;
x_28 = x_40;
goto lbl_29;
}
default:
{
obj* x_41; obj* x_44; 
x_41 = lean::cnstr_get(x_34, 0);
lean::inc(x_41);
lean::dec(x_34);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
if (lean::obj_tag(x_44) == 0)
{
obj* x_47; 
x_47 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
x_28 = x_47;
goto lbl_29;
}
else
{
obj* x_48; obj* x_50; obj* x_51; 
x_48 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_set(x_44, 0, lean::box(0));
 x_50 = x_44;
} else {
 lean::inc(x_48);
 lean::dec(x_44);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
switch (lean::obj_tag(x_51)) {
case 0:
{
obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
lean::dec(x_51);
x_57 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_54);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_58, 0, x_57);
if (lean::is_scalar(x_50)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_50;
}
lean::cnstr_set(x_59, 0, x_58);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
x_28 = x_60;
goto lbl_29;
}
case 2:
{
obj* x_61; obj* x_64; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_61 = lean::cnstr_get(x_51, 0);
lean::inc(x_61);
lean::dec(x_51);
x_64 = lean::cnstr_get(x_61, 2);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_elaborator_prec__to__nat___main(x_64);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_68, 0, x_67);
if (lean::is_scalar(x_50)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_50;
}
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
x_28 = x_70;
goto lbl_29;
}
default:
{
obj* x_73; 
lean::dec(x_50);
lean::dec(x_51);
x_73 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__5;
x_28 = x_73;
goto lbl_29;
}
}
}
}
}
}
lbl_29:
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_27);
x_75 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_77 = x_28;
} else {
 lean::inc(x_75);
 lean::dec(x_28);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
x_7 = x_78;
goto lbl_8;
}
else
{
obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_79 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_81 = x_28;
} else {
 lean::inc(x_79);
 lean::dec(x_28);
 x_81 = lean::box(0);
}
x_82 = l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(x_79);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_27);
lean::cnstr_set(x_83, 1, x_82);
if (lean::is_scalar(x_81)) {
 x_84 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_84 = x_81;
}
lean::cnstr_set(x_84, 0, x_83);
x_7 = x_84;
goto lbl_8;
}
}
}
lbl_8:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_6);
lean::dec(x_4);
x_87 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_89 = x_7;
} else {
 lean::inc(x_87);
 lean::dec(x_7);
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
obj* x_91; obj* x_94; 
x_91 = lean::cnstr_get(x_7, 0);
lean::inc(x_91);
lean::dec(x_7);
x_94 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(x_4);
if (lean::obj_tag(x_94) == 0)
{
obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_6);
lean::dec(x_91);
x_97 = lean::cnstr_get(x_94, 0);
if (lean::is_exclusive(x_94)) {
 x_99 = x_94;
} else {
 lean::inc(x_97);
 lean::dec(x_94);
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
obj* x_101; obj* x_103; obj* x_104; obj* x_105; 
x_101 = lean::cnstr_get(x_94, 0);
if (lean::is_exclusive(x_94)) {
 x_103 = x_94;
} else {
 lean::inc(x_101);
 lean::dec(x_94);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_104 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_104 = x_6;
}
lean::cnstr_set(x_104, 0, x_91);
lean::cnstr_set(x_104, 1, x_101);
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_105 = x_103;
}
lean::cnstr_set(x_105, 0, x_104);
return x_105;
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
if (lean::obj_tag(x_5) == 0)
{
obj* x_23; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_23 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_30; 
x_24 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_release(x_5, 1);
 x_26 = x_5;
} else {
 lean::inc(x_24);
 lean::dec(x_5);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
lean::dec(x_24);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_39; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_26);
x_39 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
return x_39;
}
else
{
obj* x_40; obj* x_42; obj* x_43; obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
x_40 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_42 = x_8;
} else {
 lean::inc(x_40);
 lean::dec(x_8);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_30, 0);
lean::inc(x_43);
lean::dec(x_30);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
x_49 = l_string_trim(x_46);
lean::dec(x_46);
x_51 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(x_40);
x_52 = l_list_join___main___rarg(x_51);
x_53 = lean::cnstr_get(x_1, 0);
lean::inc(x_53);
lean::dec(x_1);
if (lean::obj_tag(x_53) == 0)
{
obj* x_56; 
x_56 = lean::cnstr_get(x_3, 0);
lean::inc(x_56);
lean::dec(x_3);
if (lean::obj_tag(x_56) == 0)
{
obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_75; obj* x_76; 
lean::dec(x_26);
x_60 = lean::cnstr_get(x_2, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_2, 1);
lean::inc(x_62);
x_64 = lean::box(0);
x_65 = lean_name_mk_string(x_64, x_49);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1), 7, 2);
lean::closure_set(x_66, 0, x_0);
lean::closure_set(x_66, 1, x_52);
x_67 = l_lean_parser_token__map_insert___rarg(x_62, x_65, x_66);
x_68 = lean::cnstr_get(x_2, 2);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_2, 3);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_2, 4);
lean::inc(x_72);
lean::dec(x_2);
x_75 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_75, 0, x_60);
lean::cnstr_set(x_75, 1, x_67);
lean::cnstr_set(x_75, 2, x_68);
lean::cnstr_set(x_75, 3, x_70);
lean::cnstr_set(x_75, 4, x_72);
if (lean::is_scalar(x_42)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_42;
}
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
else
{
obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_93; obj* x_96; obj* x_97; 
lean::dec(x_56);
x_78 = lean::cnstr_get(x_2, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_2, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_2, 2);
lean::inc(x_82);
x_84 = lean::box(0);
x_85 = lean_name_mk_string(x_84, x_49);
x_86 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(x_52);
x_87 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
if (lean::is_scalar(x_26)) {
 x_88 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_88 = x_26;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_86);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser_lean_parser_has__tokens___spec__3), 8, 2);
lean::closure_set(x_89, 0, x_0);
lean::closure_set(x_89, 1, x_88);
x_90 = l_lean_parser_token__map_insert___rarg(x_82, x_85, x_89);
x_91 = lean::cnstr_get(x_2, 3);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_2, 4);
lean::inc(x_93);
lean::dec(x_2);
x_96 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_96, 0, x_78);
lean::cnstr_set(x_96, 1, x_80);
lean::cnstr_set(x_96, 2, x_90);
lean::cnstr_set(x_96, 3, x_91);
lean::cnstr_set(x_96, 4, x_93);
if (lean::is_scalar(x_42)) {
 x_97 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_97 = x_42;
}
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
}
else
{
obj* x_99; 
lean::dec(x_53);
x_99 = lean::cnstr_get(x_3, 0);
lean::inc(x_99);
lean::dec(x_3);
if (lean::obj_tag(x_99) == 0)
{
obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_118; obj* x_119; 
lean::dec(x_26);
x_103 = lean::cnstr_get(x_2, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_2, 1);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_2, 2);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_2, 3);
lean::inc(x_109);
x_111 = lean::box(0);
x_112 = lean_name_mk_string(x_111, x_49);
x_113 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1), 7, 2);
lean::closure_set(x_113, 0, x_0);
lean::closure_set(x_113, 1, x_52);
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
if (lean::is_scalar(x_42)) {
 x_119 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_119 = x_42;
}
lean::cnstr_set(x_119, 0, x_118);
return x_119;
}
else
{
obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_129; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
lean::dec(x_99);
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
x_133 = lean_name_mk_string(x_132, x_49);
x_134 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(x_52);
x_135 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
if (lean::is_scalar(x_26)) {
 x_136 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_136 = x_26;
}
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
if (lean::is_scalar(x_42)) {
 x_140 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_140 = x_42;
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
obj* x_18; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_2);
x_18 = lean::box(0);
x_7 = x_18;
goto lbl_8;
}
else
{
obj* x_19; obj* x_22; obj* x_25; obj* x_28; obj* x_30; obj* x_32; 
x_19 = lean::cnstr_get(x_2, 1);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_11, 3);
lean::inc(x_22);
lean::dec(x_11);
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
lean::dec(x_13);
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
x_32 = lean::cnstr_get(x_28, 1);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_39; 
lean::dec(x_28);
lean::dec(x_9);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_25);
x_39 = lean::box(0);
x_7 = x_39;
goto lbl_8;
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_48; obj* x_50; obj* x_53; uint8 x_55; 
x_40 = lean::cnstr_get(x_28, 3);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_set(x_32, 0, lean::box(0));
 x_44 = x_32;
} else {
 lean::inc(x_42);
 lean::dec(x_32);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_25, 1);
lean::inc(x_45);
lean::dec(x_25);
x_48 = l_string_trim(x_45);
lean::dec(x_45);
x_50 = lean::cnstr_get(x_42, 1);
lean::inc(x_50);
lean::dec(x_42);
x_53 = l_string_trim(x_50);
lean::dec(x_50);
x_55 = lean::string_dec_eq(x_48, x_53);
lean::dec(x_53);
lean::dec(x_48);
if (x_55 == 0)
{
obj* x_64; 
lean::dec(x_28);
lean::dec(x_9);
lean::dec(x_40);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_44);
x_64 = lean::box(0);
x_7 = x_64;
goto lbl_8;
}
else
{
uint8 x_65; 
x_65 = l_lean_elaborator_match__precedence___main(x_22, x_40);
if (x_65 == 0)
{
obj* x_70; 
lean::dec(x_28);
lean::dec(x_9);
lean::dec(x_19);
lean::dec(x_44);
x_70 = lean::box(0);
x_7 = x_70;
goto lbl_8;
}
else
{
obj* x_71; 
x_71 = lean::cnstr_get(x_9, 1);
lean::inc(x_71);
lean::dec(x_9);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; 
x_74 = lean::cnstr_get(x_19, 1);
lean::inc(x_74);
lean::dec(x_19);
if (lean::obj_tag(x_74) == 0)
{
obj* x_77; 
if (lean::is_scalar(x_44)) {
 x_77 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_77 = x_44;
}
lean::cnstr_set(x_77, 0, x_74);
x_30 = x_77;
goto lbl_31;
}
else
{
obj* x_80; 
lean::dec(x_44);
lean::dec(x_74);
x_80 = lean::box(0);
x_30 = x_80;
goto lbl_31;
}
}
else
{
obj* x_82; obj* x_84; 
lean::dec(x_44);
x_82 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_set(x_71, 0, lean::box(0));
 x_84 = x_71;
} else {
 lean::inc(x_82);
 lean::dec(x_71);
 x_84 = lean::box(0);
}
switch (lean::obj_tag(x_82)) {
case 0:
{
obj* x_85; 
x_85 = lean::cnstr_get(x_19, 1);
lean::inc(x_85);
lean::dec(x_19);
if (lean::obj_tag(x_85) == 0)
{
obj* x_90; 
lean::dec(x_84);
lean::dec(x_82);
x_90 = lean::box(0);
x_30 = x_90;
goto lbl_31;
}
else
{
obj* x_91; 
x_91 = lean::cnstr_get(x_85, 0);
lean::inc(x_91);
switch (lean::obj_tag(x_91)) {
case 0:
{
obj* x_93; obj* x_96; obj* x_99; obj* x_102; uint8 x_105; 
x_93 = lean::cnstr_get(x_82, 0);
lean::inc(x_93);
lean::dec(x_82);
x_96 = lean::cnstr_get(x_91, 0);
lean::inc(x_96);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_93, 1);
lean::inc(x_99);
lean::dec(x_93);
x_102 = lean::cnstr_get(x_96, 1);
lean::inc(x_102);
lean::dec(x_96);
x_105 = l_lean_elaborator_match__precedence___main(x_99, x_102);
if (x_105 == 0)
{
obj* x_108; 
lean::dec(x_85);
lean::dec(x_84);
x_108 = lean::box(0);
x_30 = x_108;
goto lbl_31;
}
else
{
obj* x_109; 
if (lean::is_scalar(x_84)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_84;
}
lean::cnstr_set(x_109, 0, x_85);
x_30 = x_109;
goto lbl_31;
}
}
default:
{
obj* x_114; 
lean::dec(x_85);
lean::dec(x_84);
lean::dec(x_91);
lean::dec(x_82);
x_114 = lean::box(0);
x_30 = x_114;
goto lbl_31;
}
}
}
}
case 1:
{
obj* x_115; 
x_115 = lean::cnstr_get(x_19, 1);
lean::inc(x_115);
lean::dec(x_19);
if (lean::obj_tag(x_115) == 0)
{
obj* x_120; 
lean::dec(x_84);
lean::dec(x_82);
x_120 = lean::box(0);
x_30 = x_120;
goto lbl_31;
}
else
{
obj* x_121; 
x_121 = lean::cnstr_get(x_115, 0);
lean::inc(x_121);
switch (lean::obj_tag(x_121)) {
case 1:
{
obj* x_123; obj* x_126; obj* x_129; obj* x_132; uint8 x_135; 
x_123 = lean::cnstr_get(x_82, 0);
lean::inc(x_123);
lean::dec(x_82);
x_126 = lean::cnstr_get(x_121, 0);
lean::inc(x_126);
lean::dec(x_121);
x_129 = lean::cnstr_get(x_123, 1);
lean::inc(x_129);
lean::dec(x_123);
x_132 = lean::cnstr_get(x_126, 1);
lean::inc(x_132);
lean::dec(x_126);
x_135 = l_lean_elaborator_match__precedence___main(x_129, x_132);
if (x_135 == 0)
{
obj* x_138; 
lean::dec(x_84);
lean::dec(x_115);
x_138 = lean::box(0);
x_30 = x_138;
goto lbl_31;
}
else
{
obj* x_139; 
if (lean::is_scalar(x_84)) {
 x_139 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_139 = x_84;
}
lean::cnstr_set(x_139, 0, x_115);
x_30 = x_139;
goto lbl_31;
}
}
default:
{
obj* x_144; 
lean::dec(x_84);
lean::dec(x_82);
lean::dec(x_121);
lean::dec(x_115);
x_144 = lean::box(0);
x_30 = x_144;
goto lbl_31;
}
}
}
}
default:
{
obj* x_145; obj* x_147; obj* x_148; obj* x_150; 
x_145 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_set(x_82, 0, lean::box(0));
 x_147 = x_82;
} else {
 lean::inc(x_145);
 lean::dec(x_82);
 x_147 = lean::box(0);
}
x_150 = lean::cnstr_get(x_19, 1);
lean::inc(x_150);
lean::dec(x_19);
if (lean::obj_tag(x_150) == 0)
{
obj* x_156; 
lean::dec(x_84);
lean::dec(x_147);
lean::dec(x_145);
x_156 = lean::box(0);
x_30 = x_156;
goto lbl_31;
}
else
{
obj* x_157; obj* x_159; 
x_157 = lean::cnstr_get(x_150, 0);
if (lean::is_exclusive(x_150)) {
 lean::cnstr_set(x_150, 0, lean::box(0));
 x_159 = x_150;
} else {
 lean::inc(x_157);
 lean::dec(x_150);
 x_159 = lean::box(0);
}
switch (lean::obj_tag(x_157)) {
case 2:
{
obj* x_160; 
x_160 = lean::cnstr_get(x_145, 1);
lean::inc(x_160);
if (lean::obj_tag(x_160) == 0)
{
obj* x_162; obj* x_165; 
x_162 = lean::cnstr_get(x_157, 0);
lean::inc(x_162);
lean::dec(x_157);
x_165 = lean::cnstr_get(x_162, 1);
lean::inc(x_165);
lean::dec(x_162);
if (lean::obj_tag(x_165) == 0)
{
obj* x_169; 
lean::dec(x_159);
x_169 = lean::box(0);
x_148 = x_169;
goto lbl_149;
}
else
{
obj* x_170; obj* x_172; 
x_170 = lean::cnstr_get(x_165, 0);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_170, 1);
lean::inc(x_172);
lean::dec(x_170);
switch (lean::obj_tag(x_172)) {
case 0:
{
obj* x_176; 
lean::dec(x_172);
if (lean::is_scalar(x_159)) {
 x_176 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_176 = x_159;
}
lean::cnstr_set(x_176, 0, x_165);
x_148 = x_176;
goto lbl_149;
}
default:
{
obj* x_180; 
lean::dec(x_159);
lean::dec(x_172);
lean::dec(x_165);
x_180 = lean::box(0);
x_148 = x_180;
goto lbl_149;
}
}
}
}
else
{
obj* x_182; obj* x_184; 
lean::dec(x_159);
x_182 = lean::cnstr_get(x_160, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get(x_182, 1);
lean::inc(x_184);
lean::dec(x_182);
switch (lean::obj_tag(x_184)) {
case 0:
{
obj* x_187; obj* x_190; 
x_187 = lean::cnstr_get(x_157, 0);
lean::inc(x_187);
lean::dec(x_157);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
lean::dec(x_187);
if (lean::obj_tag(x_190) == 0)
{
obj* x_195; 
lean::dec(x_184);
lean::dec(x_160);
x_195 = lean::box(0);
x_148 = x_195;
goto lbl_149;
}
else
{
obj* x_196; obj* x_198; obj* x_199; 
x_196 = lean::cnstr_get(x_190, 0);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_set(x_190, 0, lean::box(0));
 x_198 = x_190;
} else {
 lean::inc(x_196);
 lean::dec(x_190);
 x_198 = lean::box(0);
}
x_199 = lean::cnstr_get(x_196, 1);
lean::inc(x_199);
lean::dec(x_196);
switch (lean::obj_tag(x_199)) {
case 0:
{
obj* x_202; obj* x_205; obj* x_208; obj* x_209; uint8 x_210; 
x_202 = lean::cnstr_get(x_184, 0);
lean::inc(x_202);
lean::dec(x_184);
x_205 = lean::cnstr_get(x_199, 0);
lean::inc(x_205);
lean::dec(x_199);
x_208 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_202);
x_209 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_205);
x_210 = lean::nat_dec_eq(x_208, x_209);
lean::dec(x_209);
lean::dec(x_208);
if (x_210 == 0)
{
obj* x_215; 
lean::dec(x_198);
lean::dec(x_160);
x_215 = lean::box(0);
x_148 = x_215;
goto lbl_149;
}
else
{
obj* x_216; 
if (lean::is_scalar(x_198)) {
 x_216 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_216 = x_198;
}
lean::cnstr_set(x_216, 0, x_160);
x_148 = x_216;
goto lbl_149;
}
}
default:
{
obj* x_221; 
lean::dec(x_198);
lean::dec(x_184);
lean::dec(x_199);
lean::dec(x_160);
x_221 = lean::box(0);
x_148 = x_221;
goto lbl_149;
}
}
}
}
default:
{
obj* x_225; 
lean::dec(x_184);
lean::dec(x_157);
lean::dec(x_160);
x_225 = lean::box(0);
x_148 = x_225;
goto lbl_149;
}
}
}
}
default:
{
obj* x_231; 
lean::dec(x_84);
lean::dec(x_159);
lean::dec(x_157);
lean::dec(x_147);
lean::dec(x_145);
x_231 = lean::box(0);
x_30 = x_231;
goto lbl_31;
}
}
}
lbl_149:
{
if (lean::obj_tag(x_148) == 0)
{
obj* x_235; 
lean::dec(x_84);
lean::dec(x_147);
lean::dec(x_145);
x_235 = lean::box(0);
x_30 = x_235;
goto lbl_31;
}
else
{
obj* x_236; obj* x_238; obj* x_239; obj* x_242; obj* x_243; obj* x_244; obj* x_245; 
x_236 = lean::cnstr_get(x_148, 0);
if (lean::is_exclusive(x_148)) {
 x_238 = x_148;
} else {
 lean::inc(x_236);
 lean::dec(x_148);
 x_238 = lean::box(0);
}
x_239 = lean::cnstr_get(x_145, 0);
lean::inc(x_239);
lean::dec(x_145);
x_242 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_242, 0, x_239);
lean::cnstr_set(x_242, 1, x_236);
if (lean::is_scalar(x_147)) {
 x_243 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_243 = x_147;
}
lean::cnstr_set(x_243, 0, x_242);
if (lean::is_scalar(x_238)) {
 x_244 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_244 = x_238;
}
lean::cnstr_set(x_244, 0, x_243);
if (lean::is_scalar(x_84)) {
 x_245 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_245 = x_84;
}
lean::cnstr_set(x_245, 0, x_244);
x_30 = x_245;
goto lbl_31;
}
}
}
}
}
}
}
}
lbl_31:
{
if (lean::obj_tag(x_30) == 0)
{
obj* x_247; 
lean::dec(x_28);
x_247 = lean::box(0);
x_7 = x_247;
goto lbl_8;
}
else
{
obj* x_248; obj* x_250; obj* x_251; obj* x_252; 
x_248 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_250 = x_30;
} else {
 lean::inc(x_248);
 lean::dec(x_30);
 x_250 = lean::box(0);
}
x_251 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_251, 0, x_28);
lean::cnstr_set(x_251, 1, x_248);
if (lean::is_scalar(x_250)) {
 x_252 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_252 = x_250;
}
lean::cnstr_set(x_252, 0, x_251);
x_7 = x_252;
goto lbl_8;
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
lean::dec(x_6);
lean::dec(x_256);
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
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__2(obj* x_0) {
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
obj* x_18; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_2);
x_18 = lean::box(0);
x_7 = x_18;
goto lbl_8;
}
else
{
obj* x_19; obj* x_22; obj* x_25; obj* x_28; obj* x_30; obj* x_32; 
x_19 = lean::cnstr_get(x_2, 1);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_11, 3);
lean::inc(x_22);
lean::dec(x_11);
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
lean::dec(x_13);
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
x_32 = lean::cnstr_get(x_28, 1);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_39; 
lean::dec(x_28);
lean::dec(x_9);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_25);
x_39 = lean::box(0);
x_7 = x_39;
goto lbl_8;
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_48; obj* x_50; obj* x_53; uint8 x_55; 
x_40 = lean::cnstr_get(x_28, 3);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_set(x_32, 0, lean::box(0));
 x_44 = x_32;
} else {
 lean::inc(x_42);
 lean::dec(x_32);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_25, 1);
lean::inc(x_45);
lean::dec(x_25);
x_48 = l_string_trim(x_45);
lean::dec(x_45);
x_50 = lean::cnstr_get(x_42, 1);
lean::inc(x_50);
lean::dec(x_42);
x_53 = l_string_trim(x_50);
lean::dec(x_50);
x_55 = lean::string_dec_eq(x_48, x_53);
lean::dec(x_53);
lean::dec(x_48);
if (x_55 == 0)
{
obj* x_64; 
lean::dec(x_28);
lean::dec(x_9);
lean::dec(x_40);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_44);
x_64 = lean::box(0);
x_7 = x_64;
goto lbl_8;
}
else
{
uint8 x_65; 
x_65 = l_lean_elaborator_match__precedence___main(x_22, x_40);
if (x_65 == 0)
{
obj* x_70; 
lean::dec(x_28);
lean::dec(x_9);
lean::dec(x_19);
lean::dec(x_44);
x_70 = lean::box(0);
x_7 = x_70;
goto lbl_8;
}
else
{
obj* x_71; 
x_71 = lean::cnstr_get(x_9, 1);
lean::inc(x_71);
lean::dec(x_9);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; 
x_74 = lean::cnstr_get(x_19, 1);
lean::inc(x_74);
lean::dec(x_19);
if (lean::obj_tag(x_74) == 0)
{
obj* x_77; 
if (lean::is_scalar(x_44)) {
 x_77 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_77 = x_44;
}
lean::cnstr_set(x_77, 0, x_74);
x_30 = x_77;
goto lbl_31;
}
else
{
obj* x_80; 
lean::dec(x_44);
lean::dec(x_74);
x_80 = lean::box(0);
x_30 = x_80;
goto lbl_31;
}
}
else
{
obj* x_82; obj* x_84; 
lean::dec(x_44);
x_82 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_set(x_71, 0, lean::box(0));
 x_84 = x_71;
} else {
 lean::inc(x_82);
 lean::dec(x_71);
 x_84 = lean::box(0);
}
switch (lean::obj_tag(x_82)) {
case 0:
{
obj* x_85; 
x_85 = lean::cnstr_get(x_19, 1);
lean::inc(x_85);
lean::dec(x_19);
if (lean::obj_tag(x_85) == 0)
{
obj* x_90; 
lean::dec(x_84);
lean::dec(x_82);
x_90 = lean::box(0);
x_30 = x_90;
goto lbl_31;
}
else
{
obj* x_91; 
x_91 = lean::cnstr_get(x_85, 0);
lean::inc(x_91);
switch (lean::obj_tag(x_91)) {
case 0:
{
obj* x_93; obj* x_96; obj* x_99; obj* x_102; uint8 x_105; 
x_93 = lean::cnstr_get(x_82, 0);
lean::inc(x_93);
lean::dec(x_82);
x_96 = lean::cnstr_get(x_91, 0);
lean::inc(x_96);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_93, 1);
lean::inc(x_99);
lean::dec(x_93);
x_102 = lean::cnstr_get(x_96, 1);
lean::inc(x_102);
lean::dec(x_96);
x_105 = l_lean_elaborator_match__precedence___main(x_99, x_102);
if (x_105 == 0)
{
obj* x_108; 
lean::dec(x_85);
lean::dec(x_84);
x_108 = lean::box(0);
x_30 = x_108;
goto lbl_31;
}
else
{
obj* x_109; 
if (lean::is_scalar(x_84)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_84;
}
lean::cnstr_set(x_109, 0, x_85);
x_30 = x_109;
goto lbl_31;
}
}
default:
{
obj* x_114; 
lean::dec(x_85);
lean::dec(x_84);
lean::dec(x_91);
lean::dec(x_82);
x_114 = lean::box(0);
x_30 = x_114;
goto lbl_31;
}
}
}
}
case 1:
{
obj* x_115; 
x_115 = lean::cnstr_get(x_19, 1);
lean::inc(x_115);
lean::dec(x_19);
if (lean::obj_tag(x_115) == 0)
{
obj* x_120; 
lean::dec(x_84);
lean::dec(x_82);
x_120 = lean::box(0);
x_30 = x_120;
goto lbl_31;
}
else
{
obj* x_121; 
x_121 = lean::cnstr_get(x_115, 0);
lean::inc(x_121);
switch (lean::obj_tag(x_121)) {
case 1:
{
obj* x_123; obj* x_126; obj* x_129; obj* x_132; uint8 x_135; 
x_123 = lean::cnstr_get(x_82, 0);
lean::inc(x_123);
lean::dec(x_82);
x_126 = lean::cnstr_get(x_121, 0);
lean::inc(x_126);
lean::dec(x_121);
x_129 = lean::cnstr_get(x_123, 1);
lean::inc(x_129);
lean::dec(x_123);
x_132 = lean::cnstr_get(x_126, 1);
lean::inc(x_132);
lean::dec(x_126);
x_135 = l_lean_elaborator_match__precedence___main(x_129, x_132);
if (x_135 == 0)
{
obj* x_138; 
lean::dec(x_84);
lean::dec(x_115);
x_138 = lean::box(0);
x_30 = x_138;
goto lbl_31;
}
else
{
obj* x_139; 
if (lean::is_scalar(x_84)) {
 x_139 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_139 = x_84;
}
lean::cnstr_set(x_139, 0, x_115);
x_30 = x_139;
goto lbl_31;
}
}
default:
{
obj* x_144; 
lean::dec(x_84);
lean::dec(x_82);
lean::dec(x_121);
lean::dec(x_115);
x_144 = lean::box(0);
x_30 = x_144;
goto lbl_31;
}
}
}
}
default:
{
obj* x_145; obj* x_147; obj* x_148; obj* x_150; 
x_145 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_set(x_82, 0, lean::box(0));
 x_147 = x_82;
} else {
 lean::inc(x_145);
 lean::dec(x_82);
 x_147 = lean::box(0);
}
x_150 = lean::cnstr_get(x_19, 1);
lean::inc(x_150);
lean::dec(x_19);
if (lean::obj_tag(x_150) == 0)
{
obj* x_156; 
lean::dec(x_84);
lean::dec(x_147);
lean::dec(x_145);
x_156 = lean::box(0);
x_30 = x_156;
goto lbl_31;
}
else
{
obj* x_157; obj* x_159; 
x_157 = lean::cnstr_get(x_150, 0);
if (lean::is_exclusive(x_150)) {
 lean::cnstr_set(x_150, 0, lean::box(0));
 x_159 = x_150;
} else {
 lean::inc(x_157);
 lean::dec(x_150);
 x_159 = lean::box(0);
}
switch (lean::obj_tag(x_157)) {
case 2:
{
obj* x_160; 
x_160 = lean::cnstr_get(x_145, 1);
lean::inc(x_160);
if (lean::obj_tag(x_160) == 0)
{
obj* x_162; obj* x_165; 
x_162 = lean::cnstr_get(x_157, 0);
lean::inc(x_162);
lean::dec(x_157);
x_165 = lean::cnstr_get(x_162, 1);
lean::inc(x_165);
lean::dec(x_162);
if (lean::obj_tag(x_165) == 0)
{
obj* x_169; 
lean::dec(x_159);
x_169 = lean::box(0);
x_148 = x_169;
goto lbl_149;
}
else
{
obj* x_170; obj* x_172; 
x_170 = lean::cnstr_get(x_165, 0);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_170, 1);
lean::inc(x_172);
lean::dec(x_170);
switch (lean::obj_tag(x_172)) {
case 0:
{
obj* x_176; 
lean::dec(x_172);
if (lean::is_scalar(x_159)) {
 x_176 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_176 = x_159;
}
lean::cnstr_set(x_176, 0, x_165);
x_148 = x_176;
goto lbl_149;
}
default:
{
obj* x_180; 
lean::dec(x_159);
lean::dec(x_172);
lean::dec(x_165);
x_180 = lean::box(0);
x_148 = x_180;
goto lbl_149;
}
}
}
}
else
{
obj* x_182; obj* x_184; 
lean::dec(x_159);
x_182 = lean::cnstr_get(x_160, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get(x_182, 1);
lean::inc(x_184);
lean::dec(x_182);
switch (lean::obj_tag(x_184)) {
case 0:
{
obj* x_187; obj* x_190; 
x_187 = lean::cnstr_get(x_157, 0);
lean::inc(x_187);
lean::dec(x_157);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
lean::dec(x_187);
if (lean::obj_tag(x_190) == 0)
{
obj* x_195; 
lean::dec(x_184);
lean::dec(x_160);
x_195 = lean::box(0);
x_148 = x_195;
goto lbl_149;
}
else
{
obj* x_196; obj* x_198; obj* x_199; 
x_196 = lean::cnstr_get(x_190, 0);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_set(x_190, 0, lean::box(0));
 x_198 = x_190;
} else {
 lean::inc(x_196);
 lean::dec(x_190);
 x_198 = lean::box(0);
}
x_199 = lean::cnstr_get(x_196, 1);
lean::inc(x_199);
lean::dec(x_196);
switch (lean::obj_tag(x_199)) {
case 0:
{
obj* x_202; obj* x_205; obj* x_208; obj* x_209; uint8 x_210; 
x_202 = lean::cnstr_get(x_184, 0);
lean::inc(x_202);
lean::dec(x_184);
x_205 = lean::cnstr_get(x_199, 0);
lean::inc(x_205);
lean::dec(x_199);
x_208 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_202);
x_209 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_205);
x_210 = lean::nat_dec_eq(x_208, x_209);
lean::dec(x_209);
lean::dec(x_208);
if (x_210 == 0)
{
obj* x_215; 
lean::dec(x_198);
lean::dec(x_160);
x_215 = lean::box(0);
x_148 = x_215;
goto lbl_149;
}
else
{
obj* x_216; 
if (lean::is_scalar(x_198)) {
 x_216 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_216 = x_198;
}
lean::cnstr_set(x_216, 0, x_160);
x_148 = x_216;
goto lbl_149;
}
}
default:
{
obj* x_221; 
lean::dec(x_198);
lean::dec(x_184);
lean::dec(x_199);
lean::dec(x_160);
x_221 = lean::box(0);
x_148 = x_221;
goto lbl_149;
}
}
}
}
default:
{
obj* x_225; 
lean::dec(x_184);
lean::dec(x_157);
lean::dec(x_160);
x_225 = lean::box(0);
x_148 = x_225;
goto lbl_149;
}
}
}
}
default:
{
obj* x_231; 
lean::dec(x_84);
lean::dec(x_159);
lean::dec(x_157);
lean::dec(x_147);
lean::dec(x_145);
x_231 = lean::box(0);
x_30 = x_231;
goto lbl_31;
}
}
}
lbl_149:
{
if (lean::obj_tag(x_148) == 0)
{
obj* x_235; 
lean::dec(x_84);
lean::dec(x_147);
lean::dec(x_145);
x_235 = lean::box(0);
x_30 = x_235;
goto lbl_31;
}
else
{
obj* x_236; obj* x_238; obj* x_239; obj* x_242; obj* x_243; obj* x_244; obj* x_245; 
x_236 = lean::cnstr_get(x_148, 0);
if (lean::is_exclusive(x_148)) {
 x_238 = x_148;
} else {
 lean::inc(x_236);
 lean::dec(x_148);
 x_238 = lean::box(0);
}
x_239 = lean::cnstr_get(x_145, 0);
lean::inc(x_239);
lean::dec(x_145);
x_242 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_242, 0, x_239);
lean::cnstr_set(x_242, 1, x_236);
if (lean::is_scalar(x_147)) {
 x_243 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_243 = x_147;
}
lean::cnstr_set(x_243, 0, x_242);
if (lean::is_scalar(x_238)) {
 x_244 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_244 = x_238;
}
lean::cnstr_set(x_244, 0, x_243);
if (lean::is_scalar(x_84)) {
 x_245 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_245 = x_84;
}
lean::cnstr_set(x_245, 0, x_244);
x_30 = x_245;
goto lbl_31;
}
}
}
}
}
}
}
}
lbl_31:
{
if (lean::obj_tag(x_30) == 0)
{
obj* x_247; 
lean::dec(x_28);
x_247 = lean::box(0);
x_7 = x_247;
goto lbl_8;
}
else
{
obj* x_248; obj* x_250; obj* x_251; obj* x_252; 
x_248 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_250 = x_30;
} else {
 lean::inc(x_248);
 lean::dec(x_30);
 x_250 = lean::box(0);
}
x_251 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_251, 0, x_28);
lean::cnstr_set(x_251, 1, x_248);
if (lean::is_scalar(x_250)) {
 x_252 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_252 = x_250;
}
lean::cnstr_set(x_252, 0, x_251);
x_7 = x_252;
goto lbl_8;
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
x_259 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__2(x_4);
if (lean::obj_tag(x_259) == 0)
{
obj* x_262; 
lean::dec(x_6);
lean::dec(x_256);
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
obj* x_2; uint8 x_4; obj* x_5; uint8 x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = l_option_is__some___main___rarg(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_option_is__some___main___rarg(x_5);
lean::dec(x_5);
if (x_4 == 0)
{
if (x_7 == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = l_lean_elaborator_match__spec___closed__1;
x_16 = l_list_zip__with___main___rarg(x_15, x_9, x_12);
x_17 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; 
lean::dec(x_2);
x_19 = lean::box(0);
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 x_22 = x_17;
} else {
 lean::inc(x_20);
 lean::dec(x_17);
 x_22 = lean::box(0);
}
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_2);
lean::cnstr_set(x_23, 1, x_20);
if (lean::is_scalar(x_22)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_22;
}
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
else
{
obj* x_28; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_28 = lean::box(0);
return x_28;
}
}
else
{
if (x_7 == 0)
{
obj* x_32; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_32 = lean::box(0);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_39; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
lean::dec(x_0);
x_36 = lean::cnstr_get(x_1, 1);
lean::inc(x_36);
lean::dec(x_1);
x_39 = l_lean_elaborator_match__spec___closed__1;
x_40 = l_list_zip__with___main___rarg(x_39, x_33, x_36);
x_41 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__2(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; 
lean::dec(x_2);
x_43 = lean::box(0);
return x_43;
}
else
{
obj* x_44; obj* x_46; obj* x_47; obj* x_48; 
x_44 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_46 = x_41;
} else {
 lean::inc(x_44);
 lean::dec(x_41);
 x_46 = lean::box(0);
}
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_2);
lean::cnstr_set(x_47, 1, x_44);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
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
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2(x_3, x_0, x_1, x_2);
return x_4;
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
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_register__notation__macro___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_register__notation__macro___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
uint8 l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(uint8 x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; uint8 x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_0, x_3);
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
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; uint8 x_14; uint8 x_15; 
x_4 = l_lean_parser_command_notation_has__view;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_8, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_14 = 0;
x_15 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_14, x_11);
lean::dec(x_11);
if (x_15 == 0)
{
obj* x_18; 
lean::inc(x_2);
x_18 = l_lean_elaborator_notation_elaborate__aux(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_18) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_2);
x_20 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_22 = x_18;
} else {
 lean::inc(x_20);
 lean::dec(x_18);
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
obj* x_24; obj* x_27; obj* x_29; obj* x_33; 
x_24 = lean::cnstr_get(x_18, 0);
lean::inc(x_24);
lean::dec(x_18);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
lean::inc(x_27);
x_33 = l_lean_elaborator_register__notation__macro(x_27, x_1, x_2, x_29);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_2);
lean::dec(x_27);
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
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_33, 0);
lean::inc(x_40);
lean::dec(x_33);
x_43 = lean::cnstr_get(x_27, 0);
lean::inc(x_43);
lean::dec(x_27);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_48; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_72; obj* x_75; obj* x_76; 
x_46 = lean::cnstr_get(x_40, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_40, 1);
lean::inc(x_48);
lean::dec(x_40);
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_46);
lean::cnstr_set(x_55, 1, x_53);
x_56 = lean::cnstr_get(x_48, 2);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_48, 3);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_48, 4);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_48, 5);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_48, 6);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_48, 7);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_48, 8);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_48, 9);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_48, 10);
lean::inc(x_72);
lean::dec(x_48);
x_75 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_75, 0, x_51);
lean::cnstr_set(x_75, 1, x_55);
lean::cnstr_set(x_75, 2, x_56);
lean::cnstr_set(x_75, 3, x_58);
lean::cnstr_set(x_75, 4, x_60);
lean::cnstr_set(x_75, 5, x_62);
lean::cnstr_set(x_75, 6, x_64);
lean::cnstr_set(x_75, 7, x_66);
lean::cnstr_set(x_75, 8, x_68);
lean::cnstr_set(x_75, 9, x_70);
lean::cnstr_set(x_75, 10, x_72);
x_76 = l_lean_elaborator_update__parser__config(x_1, x_2, x_75);
return x_76;
}
else
{
obj* x_78; obj* x_80; obj* x_83; obj* x_85; 
lean::dec(x_43);
x_78 = lean::cnstr_get(x_40, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_40, 1);
lean::inc(x_80);
lean::dec(x_40);
x_83 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_notation_elaborate___lambda__1), 2, 1);
lean::closure_set(x_83, 0, x_78);
lean::inc(x_2);
x_85 = l_lean_elaborator_modify__current__scope(x_83, x_1, x_2, x_80);
if (lean::obj_tag(x_85) == 0)
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_2);
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
obj* x_91; obj* x_94; obj* x_97; 
x_91 = lean::cnstr_get(x_85, 0);
lean::inc(x_91);
lean::dec(x_85);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
lean::dec(x_91);
x_97 = l_lean_elaborator_update__parser__config(x_1, x_2, x_94);
return x_97;
}
}
}
}
}
else
{
obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_112; obj* x_115; obj* x_116; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_124; obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_8);
x_99 = lean::cnstr_get(x_3, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_3, 1);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_3, 2);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_3, 3);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_3, 4);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_2, 0);
lean::inc(x_109);
lean::dec(x_2);
x_112 = lean::cnstr_get(x_109, 0);
lean::inc(x_112);
lean::dec(x_109);
x_115 = lean::box(0);
x_116 = l_lean_elaborator_notation_elaborate___closed__1;
x_117 = 1;
x_118 = l_string_iterator_extract___main___closed__1;
x_119 = l_lean_elaborator_notation_elaborate___closed__2;
x_120 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_120, 0, x_112);
lean::cnstr_set(x_120, 1, x_116);
lean::cnstr_set(x_120, 2, x_115);
lean::cnstr_set(x_120, 3, x_118);
lean::cnstr_set(x_120, 4, x_119);
lean::cnstr_set_scalar(x_120, sizeof(void*)*5, x_117);
x_121 = x_120;
x_122 = lean::cnstr_get(x_3, 5);
lean::inc(x_122);
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_121);
lean::cnstr_set(x_124, 1, x_122);
x_125 = lean::cnstr_get(x_3, 6);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_3, 7);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_3, 8);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_3, 9);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_3, 10);
lean::inc(x_133);
lean::dec(x_3);
x_136 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_136, 0, x_99);
lean::cnstr_set(x_136, 1, x_101);
lean::cnstr_set(x_136, 2, x_103);
lean::cnstr_set(x_136, 3, x_105);
lean::cnstr_set(x_136, 4, x_107);
lean::cnstr_set(x_136, 5, x_124);
lean::cnstr_set(x_136, 6, x_125);
lean::cnstr_set(x_136, 7, x_127);
lean::cnstr_set(x_136, 8, x_129);
lean::cnstr_set(x_136, 9, x_131);
lean::cnstr_set(x_136, 10, x_133);
x_137 = lean::box(0);
x_138 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_136);
x_139 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_139, 0, x_138);
return x_139;
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_2, x_1);
x_4 = lean::box(x_3);
lean::dec(x_1);
return x_4;
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
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_lean_name_quick__lt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_lean_name_quick__lt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_lean_name_quick__lt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_lean_name_quick__lt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_rbnode_is__red___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(x_0, x_35, x_2, x_3);
x_52 = l_rbnode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(x_0, x_29, x_2, x_3);
x_61 = l_rbnode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(x_0, x_1, x_8, x_10);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
}
}
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = l_list_foldl___main___at_lean_elaborator_elaborators___spec__6(x_1, x_2, x_0);
return x_3;
}
}
obj* _init_l_lean_elaborator_elaborators() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
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
x_73 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1(x_72);
return x_73;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__5(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_insert___main___at_lean_elaborator_elaborators___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_list_foldl___main___at_lean_elaborator_elaborators___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldl___main___at_lean_elaborator_elaborators___spec__6(x_0, x_1, x_2);
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
uint8 l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_5, 2);
x_7 = lean_name_dec_eq(x_6, x_0);
if (x_7 == 0)
{
x_2 = x_4;
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
obj* x_6; uint8 x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_0, 7);
x_7 = 0;
x_8 = l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(x_1, x_7, x_6);
if (x_8 == 0)
{
return x_7;
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
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_1);
x_4 = l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(x_0, x_3, x_2);
x_5 = lean::box(x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
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
uint8 l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_3, 2);
x_6 = lean_name_dec_eq(x_0, x_5);
if (x_6 == 0)
{
x_2 = x_4;
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
obj* x_23; uint8 x_26; uint8 x_27; 
x_23 = lean::cnstr_get(x_13, 2);
lean::inc(x_23);
lean::dec(x_13);
x_26 = 0;
x_27 = l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(x_0, x_26, x_23);
lean::dec(x_23);
if (x_27 == 0)
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
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_1);
x_4 = l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(x_0, x_3, x_2);
x_5 = lean::box(x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
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
obj* l_lean_elaborator_mk__state(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_3 = lean::box(0);
x_4 = lean::box(0);
x_5 = l_lean_elaborator_mk__state___closed__1;
x_6 = l_lean_elaborator_mk__state___closed__2;
x_7 = l_lean_elaborator_mk__state___closed__3;
x_8 = l_lean_elaborator_mk__state___closed__4;
x_9 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_7);
lean::cnstr_set(x_9, 4, x_8);
lean::cnstr_set(x_9, 5, x_4);
lean::cnstr_set(x_9, 6, x_3);
lean::cnstr_set(x_9, 7, x_3);
lean::cnstr_set(x_9, 8, x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_lean_expander_builtin__transformers;
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0u);
x_19 = l_lean_message__log_empty;
x_20 = l_lean_elaborator_mk__state___closed__5;
x_21 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_21, 0, x_3);
lean::cnstr_set(x_21, 1, x_3);
lean::cnstr_set(x_21, 2, x_18);
lean::cnstr_set(x_21, 3, x_3);
lean::cnstr_set(x_21, 4, x_10);
lean::cnstr_set(x_21, 5, x_19);
lean::cnstr_set(x_21, 6, x_11);
lean::cnstr_set(x_21, 7, x_17);
lean::cnstr_set(x_21, 8, x_1);
lean::cnstr_set(x_21, 9, x_20);
lean::cnstr_set(x_21, 10, x_18);
return x_21;
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
x_3 = l_rbnode_find___main___at_lean_name__map_contains___spec__2(x_2, lean::box(0), x_0, x_1);
return x_3;
}
}
obj* _init_l_lean_elaborator_process__command___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("not a command: ");
return x_0;
}
}
obj* _init_l_lean_elaborator_process__command___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown command: ");
return x_0;
}
}
obj* l_lean_elaborator_process__command___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_1);
x_5 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_1);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_1);
x_8 = l_lean_parser_syntax_to__format___main(x_1);
x_9 = lean::mk_nat_obj(80u);
x_10 = l_lean_format_pretty(x_8, x_9);
x_11 = l_lean_elaborator_process__command___lambda__1___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg(x_7, x_12, x_0, x_2, x_3);
lean::dec(x_3);
lean::dec(x_0);
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
lean::cnstr_set(x_26, 0, x_1);
x_27 = l_lean_name_to__string___closed__1;
x_28 = l_lean_name_to__string__with__sep___main(x_27, x_21);
x_29 = l_lean_elaborator_process__command___lambda__1___closed__2;
x_30 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_32 = l_lean_expander_error___at_lean_elaborator_process__command___spec__2___rarg(x_26, x_30, x_0, x_2, x_3);
lean::dec(x_3);
lean::dec(x_0);
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
x_42 = l_lean_elaborator_preresolve___main(x_1, x_0, x_2, x_3);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_0);
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
x_58 = lean::apply_4(x_38, x_53, x_0, x_2, x_55);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_process__command___lambda__1), 4, 0);
return x_0;
}
}
obj* l_lean_elaborator_process__command(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_35; obj* x_36; obj* x_37; 
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
x_36 = l_lean_elaborator_process__command___closed__1;
x_37 = lean::fixpoint3(x_36, x_2, x_0, x_35);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
lean::dec(x_37);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_24);
x_42 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_42, 0, x_3);
lean::cnstr_set(x_42, 1, x_5);
lean::cnstr_set(x_42, 2, x_7);
lean::cnstr_set(x_42, 3, x_9);
lean::cnstr_set(x_42, 4, x_11);
lean::cnstr_set(x_42, 5, x_41);
lean::cnstr_set(x_42, 6, x_13);
lean::cnstr_set(x_42, 7, x_15);
lean::cnstr_set(x_42, 8, x_17);
lean::cnstr_set(x_42, 9, x_19);
lean::cnstr_set(x_42, 10, x_21);
return x_42;
}
else
{
obj* x_53; obj* x_56; 
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
x_53 = lean::cnstr_get(x_37, 0);
lean::inc(x_53);
lean::dec(x_37);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
lean::dec(x_53);
return x_56;
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
obj* initialize_init_lean_parser_module(obj*);
obj* initialize_init_lean_expander(obj*);
obj* initialize_init_lean_expr(obj*);
obj* initialize_init_lean_options(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_elaborator(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_module(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expander(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_options(w);
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
 l_lean_elaborator_process__command___lambda__1___closed__1 = _init_l_lean_elaborator_process__command___lambda__1___closed__1();
lean::mark_persistent(l_lean_elaborator_process__command___lambda__1___closed__1);
 l_lean_elaborator_process__command___lambda__1___closed__2 = _init_l_lean_elaborator_process__command___lambda__1___closed__2();
lean::mark_persistent(l_lean_elaborator_process__command___lambda__1___closed__2);
 l_lean_elaborator_process__command___closed__1 = _init_l_lean_elaborator_process__command___closed__1();
lean::mark_persistent(l_lean_elaborator_process__command___closed__1);
return w;
}
