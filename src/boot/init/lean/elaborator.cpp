// Lean compiler output
// Module: init.lean.elaborator
// Imports: init.lean.parser.module init.lean.expander init.lean.expr init.lean.options
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
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
obj* l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__5(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_command_declaration;
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
obj* l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___lambda__1___closed__1;
obj* l_list_filter__map___main___rarg(obj*, obj*);
obj* l_list_length___main___rarg(obj*);
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
obj* l_lean_elaborator_run___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__31;
obj* l_lean_elaborator_register__notation__macro(obj*, obj*, obj*);
obj* l_lean_elaborator_section_elaborate___lambda__1(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(obj*, obj*, obj*);
obj* l_list_enum__from___main___rarg(obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t_monad__state(obj*);
obj* l_lean_elaborator_variables_elaborate___closed__2;
unsigned char l_lean_elaborator_match__precedence___main(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__39;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__16(obj*, obj*, obj*);
obj* l_lean_parser_number_view_to__nat___main(obj*);
obj* l_lean_elaborator_run___closed__6;
extern obj* l_lean_parser_term_sort_has__view_x_27___lambda__1___closed__4;
extern obj* l_lean_parser_command_open_has__view;
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(obj*, obj*, obj*, obj*);
unsigned char l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_lean_elaborator_run___lambda__8(obj*);
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
obj* l_lean_parser_term_simple__binder_view_to__binder__info___main(obj*);
extern obj* l_lean_parser_command_set__option;
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2(obj*, obj*);
obj* l_lean_elaborator_max__recursion;
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
obj* l_coe__decidable__eq(unsigned char);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(obj*, obj*, obj*);
extern obj* l_lean_parser_command_notation;
obj* l_lean_elaborator_elaborator__t;
obj* l_lean_elaborator_current__command(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__24(obj*, obj*, obj*);
obj* l_lean_kvmap_set__name(obj*, obj*, obj*);
unsigned char l_lean_elaborator_is__open__namespace(obj*, obj*);
obj* l_lean_elaborator_elaborators;
obj* l_lean_elaborator_commands_elaborate(unsigned char, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_pi_has__view;
obj* l_lean_elaborator_ordered__rbmap_find___rarg(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(obj*, obj*);
obj* l_lean_elaborator_resolve__context___main___lambda__1(obj*, obj*);
extern obj* l_lean_parser_command_universe_has__view;
obj* l_lean_elaborator_locally___rarg(obj*, obj*, obj*);
obj* l_state__t_monad__state___rarg(obj*);
obj* l_lean_elaborator_elaborator__m;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1;
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
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(obj*, obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__6(obj*, obj*, obj*);
extern obj* l_lean_parser_command_reserve__notation;
obj* l_lean_elaborator_commands_elaborate___main___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_except__t_monad__except___rarg(obj*);
extern obj* l_lean_parser_term_have_has__view;
obj* l_lean_elaborator_init__quot_elaborate(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
extern obj* l_lean_parser_command_variables_has__view;
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, unsigned char);
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__32;
obj* l_lean_elaborator_end__scope___lambda__1(obj*, obj*);
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_lean_parser_trie_insert___rarg(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__22(obj*, obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(unsigned char, obj*);
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_elaborator__t___at_lean_elaborator_command_elaborate___spec__2;
obj* l_lean_elaborator_preresolve___main(obj*, obj*, obj*);
obj* l_lean_elaborator_mk__notation__kind___rarg___closed__1;
obj* l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_variables_elaborate___spec__1(obj*, obj*);
unsigned char l_option_is__some___main___rarg(obj*);
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
obj* l_lean_elaborator_mk__notation__kind(obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7;
obj* l_lean_elaborator_attribute_elaborate___closed__2;
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
obj* l_reader__t_bind___at_lean_elaborator_section_elaborate___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_list_zip__with___main___rarg(obj*, obj*, obj*);
obj* l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1;
obj* l_lean_elaborator_run___closed__3;
obj* l_lean_elaborator_reserve__notation_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_simple__binders__to__pexpr(obj*, obj*, obj*);
obj* l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(obj*, obj*);
obj* l_lean_elaborator_is__open__namespace___boxed(obj*, obj*);
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
obj* l_list_append___main___rarg(obj*, obj*);
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
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__38;
obj* l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(obj*);
unsigned char l_lean_elaborator_is__open__namespace___main(obj*, obj*);
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(obj*, obj*, obj*);
extern obj* l_char_has__repr___closed__1;
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
extern obj* l_lean_parser_max__prec;
obj* l_lean_elaborator_notation_elaborate__aux(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__7(obj*, obj*);
obj* l_lean_elaborator_end__scope___lambda__2___closed__2;
extern obj* l_lean_options_mk;
obj* l_lean_parser_module_yield__command___lambda__3(obj*, obj*);
obj* l___private_3693562977__run__aux___main___rarg(obj*, obj*, obj*, obj*);
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
obj* l_lean_elaborator_commands_elaborate___main___lambda__3(unsigned char, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(obj*);
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(obj*);
obj* l_lean_elaborator_commands_elaborate___main(unsigned char, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8(obj*);
obj* l_lean_elaborator_run___lambda__3(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__1(obj*);
obj* l_lean_elaborator_resolve__context(obj*, obj*, obj*);
obj* l_except__t_monad___rarg(obj*);
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
obj* l_lean_parser_syntax_kind___main(obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__2;
obj* l_lean_elaborator_section_elaborate(obj*, obj*, obj*);
obj* l_lean_elaborator_namespace_elaborate___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_preresolve(obj*, obj*, obj*);
extern obj* l_lean_parser_module_header_has__view;
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__26(obj*, obj*, obj*);
unsigned char l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(obj*);
obj* l_lean_elaborator_infer__mod__to__pexpr___closed__1;
extern obj* l_lean_parser_command_section;
obj* l_list_mfilter___main___at_lean_elaborator_variables_elaborate___spec__4(obj*, obj*, obj*);
obj* l_reader__t_lift(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__21;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_struct__inst__item_has__view;
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__2(obj*);
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(obj*, obj*, obj*);
obj* l_lean_elaborator_match__precedence___main___boxed(obj*, obj*);
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(obj*);
obj* l_lean_parser_term_binders_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_find(obj*, obj*, obj*);
obj* l___private_3693562977__run__aux___at_lean_elaborator_run___spec__6(obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_term_binder__ident_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14(obj*, obj*, obj*);
obj* l_lean_elaborator_coelaborator__m_monad__coroutine;
obj* l_lean_elaborator_to__pexpr___main___closed__8;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__43;
unsigned char l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_elaborator_attribute_elaborate___closed__1;
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(obj*);
unsigned char l_lean_elaborator_match__precedence(obj*, obj*);
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
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1(obj*);
obj* l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
obj* l_lean_elaborator_commands_elaborate___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_match__spec(obj*, obj*);
obj* l_lean_expander_mk__notation__transformer(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__2(obj*, obj*, obj*);
obj* l_lean_elaborator_ordered__rbmap_insert(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__30;
obj* l_lean_elaborator_mk__eqns(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__3(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___lambda__1(obj*);
obj* l_lean_elaborator_level__add___main(obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_expr_mk__capp(obj*, obj*);
obj* l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(obj*, obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__2(unsigned char, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main(obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__2(obj*);
obj* l_lean_elaborator_run___lambda__1___closed__1;
extern obj* l_lean_parser_command_declaration_has__view;
obj* l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
extern obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
obj* l_lean_elaborator_run___closed__7;
obj* l_lean_kvmap_insert__core___main(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__28;
obj* l_lean_elaborator_to__level___main___closed__3;
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__1(obj*, obj*, obj*);
extern obj* l_lean_parser_command_end_has__view;
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__1(obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__4(obj*, obj*, obj*, obj*);
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
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(obj*);
obj* l_lean_elaborator_old__elab__command(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(obj*);
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1(obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_state__t_lift___rarg(obj*, obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__20(obj*, obj*, obj*);
extern obj* l_lean_expander_get__opt__type___main___closed__1;
obj* l_rbmap_insert___main___at_lean_elaborator_old__elab__command___spec__10(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_level_trailing_has__view;
obj* l_lean_elaborator_no__kind_elaborate___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_locally___rarg___closed__1;
obj* l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__10(obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__29;
extern obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_option_map___rarg(obj*, obj*);
extern obj* l_lean_expander_no__expansion___closed__1;
obj* l_coroutine_yield___rarg(obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__40;
obj* l_rbmap_insert___main___at_lean_elaborator_ordered__rbmap_of__list___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1(obj*);
obj* l_lean_elaborator_command_elaborate(obj*, obj*, obj*);
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(obj*, obj*, obj*);
obj* l_lean_elaborator_prec__to__nat___main(obj*);
obj* l_lean_elaborator_with__current__command___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_view_value(obj*);
obj* l_lean_elaborator_commands_elaborate___main___lambda__4(obj*, obj*, unsigned char, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__42;
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1;
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1(obj*, obj*, obj*);
extern obj* l_lean_parser_command_notation_has__view;
extern obj* l_lean_parser_command_check;
obj* l_lean_elaborator_yield__to__outside___rarg___lambda__1(obj*, obj*);
obj* l_lean_elaborator_max__commands;
extern obj* l_lean_parser_command_export;
obj* l_lean_elaborator_command__parser__config_register__notation__parser___closed__2;
obj* l_lean_elaborator_elaborator__t_monad__state___rarg(obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_to__pexpr___main___closed__44;
obj* l_rbnode_insert___at_lean_elaborator_ordered__rbmap_insert___spec__2(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(obj*);
obj* l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1___lambda__12(obj*, obj*, obj*);
obj* l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
obj* l_lean_elaborator_init__quot_elaborate___closed__1;
obj* l_lean_elaborator_postprocess__notation__spec___closed__1;
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2;
extern obj* l_lean_parser_command_set__option_has__view;
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
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_6; 
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_19; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_15 = x_1;
}
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; 
lean::dec(x_19);
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_2);
if (lean::obj_tag(x_24) == 0)
{
obj* x_29; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_24);
if (lean::is_scalar(x_15)) {
 x_29 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_29 = x_15;
}
lean::cnstr_set(x_29, 0, x_7);
lean::cnstr_set(x_29, 1, x_2);
lean::cnstr_set(x_29, 2, x_3);
lean::cnstr_set(x_29, 3, x_13);
return x_29;
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_24);
x_31 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_13, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_15;
}
lean::cnstr_set(x_32, 0, x_7);
lean::cnstr_set(x_32, 1, x_9);
lean::cnstr_set(x_32, 2, x_11);
lean::cnstr_set(x_32, 3, x_31);
return x_32;
}
}
else
{
obj* x_34; obj* x_35; 
lean::dec(x_19);
x_34 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_7, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_35 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_35 = x_15;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
lean::cnstr_set(x_35, 2, x_11);
lean::cnstr_set(x_35, 3, x_13);
return x_35;
}
}
default:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_48; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 3);
lean::inc(x_42);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_44 = x_1;
}
lean::inc(x_38);
lean::inc(x_2);
lean::inc(x_0);
x_48 = lean::apply_2(x_0, x_2, x_38);
if (lean::obj_tag(x_48) == 0)
{
obj* x_53; 
lean::dec(x_48);
lean::inc(x_2);
lean::inc(x_38);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_38, x_2);
if (lean::obj_tag(x_53) == 0)
{
obj* x_58; 
lean::dec(x_0);
lean::dec(x_40);
lean::dec(x_38);
lean::dec(x_53);
if (lean::is_scalar(x_44)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_44;
}
lean::cnstr_set(x_58, 0, x_36);
lean::cnstr_set(x_58, 1, x_2);
lean::cnstr_set(x_58, 2, x_3);
lean::cnstr_set(x_58, 3, x_42);
return x_58;
}
else
{
unsigned char x_61; 
lean::dec(x_53);
lean::inc(x_42);
x_61 = l_rbnode_get__color___main___rarg(x_42);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_44);
x_63 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_42, x_2, x_3);
x_64 = l_rbnode_balance2__node___main___rarg(x_63, x_38, x_40, x_36);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_42, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_44;
}
lean::cnstr_set(x_66, 0, x_36);
lean::cnstr_set(x_66, 1, x_38);
lean::cnstr_set(x_66, 2, x_40);
lean::cnstr_set(x_66, 3, x_65);
return x_66;
}
}
}
else
{
unsigned char x_69; 
lean::dec(x_48);
lean::inc(x_36);
x_69 = l_rbnode_get__color___main___rarg(x_36);
if (x_69 == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_44);
x_71 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_36, x_2, x_3);
x_72 = l_rbnode_balance1__node___main___rarg(x_71, x_38, x_40, x_42);
return x_72;
}
else
{
obj* x_73; obj* x_74; 
x_73 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_insert___spec__3___rarg(x_0, x_36, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_38);
lean::cnstr_set(x_74, 2, x_40);
lean::cnstr_set(x_74, 3, x_42);
return x_74;
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
unsigned char x_5; obj* x_6; obj* x_7; 
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
obj* l_rbnode_find___main___at_lean_elaborator_ordered__rbmap_find___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_8 = lean::box(0);
return x_8;
}
case 1:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_21; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 2);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 3);
lean::inc(x_15);
lean::dec(x_2);
lean::inc(x_11);
lean::inc(x_3);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_3, x_11);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_21);
lean::inc(x_3);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_3);
if (lean::obj_tag(x_26) == 0)
{
obj* x_31; 
lean::dec(x_15);
lean::dec(x_26);
lean::dec(x_3);
lean::dec(x_0);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_13);
return x_31;
}
else
{
lean::dec(x_26);
lean::dec(x_13);
x_1 = x_0;
x_2 = x_15;
goto _start;
}
}
else
{
lean::dec(x_21);
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_11);
x_1 = x_0;
x_2 = x_9;
goto _start;
}
}
default:
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_52; 
x_40 = lean::cnstr_get(x_2, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_2, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_2, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_2, 3);
lean::inc(x_46);
lean::dec(x_2);
lean::inc(x_42);
lean::inc(x_3);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_3, x_42);
if (lean::obj_tag(x_52) == 0)
{
obj* x_57; 
lean::dec(x_40);
lean::dec(x_52);
lean::inc(x_3);
lean::inc(x_0);
x_57 = lean::apply_2(x_0, x_42, x_3);
if (lean::obj_tag(x_57) == 0)
{
obj* x_62; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_46);
lean::dec(x_57);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_44);
return x_62;
}
else
{
lean::dec(x_44);
lean::dec(x_57);
x_1 = x_0;
x_2 = x_46;
goto _start;
}
}
else
{
lean::dec(x_42);
lean::dec(x_44);
lean::dec(x_46);
lean::dec(x_52);
x_1 = x_0;
x_2 = x_40;
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
obj* l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_6; 
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_19; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_15 = x_1;
}
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; 
lean::dec(x_19);
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_2);
if (lean::obj_tag(x_24) == 0)
{
obj* x_29; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_24);
if (lean::is_scalar(x_15)) {
 x_29 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_29 = x_15;
}
lean::cnstr_set(x_29, 0, x_7);
lean::cnstr_set(x_29, 1, x_2);
lean::cnstr_set(x_29, 2, x_3);
lean::cnstr_set(x_29, 3, x_13);
return x_29;
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_24);
x_31 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_13, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_15;
}
lean::cnstr_set(x_32, 0, x_7);
lean::cnstr_set(x_32, 1, x_9);
lean::cnstr_set(x_32, 2, x_11);
lean::cnstr_set(x_32, 3, x_31);
return x_32;
}
}
else
{
obj* x_34; obj* x_35; 
lean::dec(x_19);
x_34 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_7, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_35 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_35 = x_15;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
lean::cnstr_set(x_35, 2, x_11);
lean::cnstr_set(x_35, 3, x_13);
return x_35;
}
}
default:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_48; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 3);
lean::inc(x_42);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_44 = x_1;
}
lean::inc(x_38);
lean::inc(x_2);
lean::inc(x_0);
x_48 = lean::apply_2(x_0, x_2, x_38);
if (lean::obj_tag(x_48) == 0)
{
obj* x_53; 
lean::dec(x_48);
lean::inc(x_2);
lean::inc(x_38);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_38, x_2);
if (lean::obj_tag(x_53) == 0)
{
obj* x_58; 
lean::dec(x_0);
lean::dec(x_40);
lean::dec(x_38);
lean::dec(x_53);
if (lean::is_scalar(x_44)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_44;
}
lean::cnstr_set(x_58, 0, x_36);
lean::cnstr_set(x_58, 1, x_2);
lean::cnstr_set(x_58, 2, x_3);
lean::cnstr_set(x_58, 3, x_42);
return x_58;
}
else
{
unsigned char x_61; 
lean::dec(x_53);
lean::inc(x_42);
x_61 = l_rbnode_get__color___main___rarg(x_42);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_44);
x_63 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_42, x_2, x_3);
x_64 = l_rbnode_balance2__node___main___rarg(x_63, x_38, x_40, x_36);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_42, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_44;
}
lean::cnstr_set(x_66, 0, x_36);
lean::cnstr_set(x_66, 1, x_38);
lean::cnstr_set(x_66, 2, x_40);
lean::cnstr_set(x_66, 3, x_65);
return x_66;
}
}
}
else
{
unsigned char x_69; 
lean::dec(x_48);
lean::inc(x_36);
x_69 = l_rbnode_get__color___main___rarg(x_36);
if (x_69 == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_44);
x_71 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_36, x_2, x_3);
x_72 = l_rbnode_balance1__node___main___rarg(x_71, x_38, x_40, x_42);
return x_72;
}
else
{
obj* x_73; obj* x_74; 
x_73 = l_rbnode_ins___main___at_lean_elaborator_ordered__rbmap_of__list___spec__4___rarg(x_0, x_36, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_38);
lean::cnstr_set(x_74, 2, x_40);
lean::cnstr_set(x_74, 3, x_42);
return x_74;
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
unsigned char x_5; obj* x_6; obj* x_7; 
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
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_16; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
lean::inc(x_0);
x_16 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_ordered__rbmap_of__list___spec__1___rarg(x_0, x_1, x_10, x_12);
x_1 = x_16;
x_2 = x_7;
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
obj* _init_l_lean_elaborator_elaborator__t() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
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
obj* l_lean_elaborator_command_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_3, x_0, x_1, x_2);
return x_4;
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
obj* l_list_foldl___main___at_lean_elaborator_mangle__ident___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::name_mk_numeral(x_0, x_3);
x_0 = x_8;
x_1 = x_5;
goto _start;
}
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
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
lean::dec(x_4);
lean::inc(x_0);
x_7 = l_lean_parser_syntax_to__format___main(x_0);
x_8 = lean::mk_nat_obj(80u);
x_9 = l_lean_format_pretty(x_7, x_8);
x_10 = l_lean_elaborator_level__get__app__args___main___closed__1;
lean::inc(x_10);
x_12 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_14 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_12, x_1, x_2);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_19 = lean::name_dec_eq(x_15, x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_19);
x_21 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_22 = lean::name_dec_eq(x_15, x_21);
lean::dec(x_15);
if (lean::obj_tag(x_22) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_33; 
lean::dec(x_22);
lean::inc(x_0);
x_26 = l_lean_parser_syntax_to__format___main(x_0);
x_27 = lean::mk_nat_obj(80u);
x_28 = l_lean_format_pretty(x_26, x_27);
x_29 = l_lean_elaborator_level__get__app__args___main___closed__1;
lean::inc(x_29);
x_31 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_33 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_31, x_1, x_2);
return x_33;
}
else
{
obj* x_35; obj* x_36; obj* x_39; 
lean::dec(x_22);
x_35 = l_lean_parser_level_trailing_has__view;
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
lean::inc(x_0);
x_39 = lean::apply_1(x_36, x_0);
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
lean::inc(x_48);
if (lean::is_shared(x_46)) {
 lean::dec(x_46);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_46, 0);
 x_50 = x_46;
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
lean::inc(x_52);
if (lean::is_shared(x_46)) {
 lean::dec(x_46);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_46, 0);
 x_54 = x_46;
}
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 1);
lean::inc(x_57);
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_59 = x_52;
}
x_60 = lean::cnstr_get(x_55, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_55, 1);
lean::inc(x_62);
if (lean::is_shared(x_55)) {
 lean::dec(x_55);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_64 = x_55;
}
x_65 = lean::cnstr_get(x_41, 1);
lean::inc(x_65);
lean::dec(x_41);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set(x_68, 1, x_62);
if (lean::is_scalar(x_59)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_59;
}
lean::cnstr_set(x_69, 0, x_60);
lean::cnstr_set(x_69, 1, x_68);
if (lean::is_scalar(x_64)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_64;
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
obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_1);
lean::dec(x_39);
x_74 = lean::box(0);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_0);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_2);
x_77 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_15);
x_81 = lean::box(0);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_0);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_2);
x_84 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
return x_84;
}
}
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
obj* l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; unsigned char x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
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
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
x_10 = l_lean_elaborator_level__add___main(x_0, x_7);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
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
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; 
lean::dec(x_22);
lean::dec(x_26);
lean::dec(x_14);
lean::dec(x_19);
lean::dec(x_20);
lean::inc(x_0);
x_33 = l_lean_parser_syntax_to__format___main(x_0);
x_34 = lean::mk_nat_obj(80u);
x_35 = l_lean_format_pretty(x_33, x_34);
x_36 = l_lean_elaborator_to__level___main___closed__1;
lean::inc(x_36);
x_38 = lean::string_append(x_36, x_35);
lean::dec(x_35);
x_40 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_38, x_1, x_17);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_45; 
x_41 = lean::cnstr_get(x_26, 0);
lean::inc(x_41);
lean::dec(x_26);
x_44 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_45 = lean::name_dec_eq(x_41, x_44);
if (lean::obj_tag(x_45) == 0)
{
obj* x_47; obj* x_48; 
lean::dec(x_45);
x_47 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_48 = lean::name_dec_eq(x_41, x_47);
lean::dec(x_41);
if (lean::obj_tag(x_48) == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_63; 
lean::dec(x_22);
lean::dec(x_14);
lean::dec(x_19);
lean::dec(x_20);
lean::dec(x_48);
lean::inc(x_0);
x_56 = l_lean_parser_syntax_to__format___main(x_0);
x_57 = lean::mk_nat_obj(80u);
x_58 = l_lean_format_pretty(x_56, x_57);
x_59 = l_lean_elaborator_to__level___main___closed__1;
lean::inc(x_59);
x_61 = lean::string_append(x_59, x_58);
lean::dec(x_58);
x_63 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_61, x_1, x_17);
return x_63;
}
else
{
obj* x_65; obj* x_66; obj* x_68; 
lean::dec(x_48);
x_65 = l_lean_parser_level_trailing_has__view;
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
x_68 = lean::apply_1(x_66, x_20);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; obj* x_75; 
lean::dec(x_22);
lean::dec(x_14);
lean::dec(x_19);
lean::dec(x_68);
x_73 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_73);
x_75 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_73, x_1, x_17);
return x_75;
}
else
{
obj* x_76; 
x_76 = lean::cnstr_get(x_68, 0);
lean::inc(x_76);
lean::dec(x_68);
if (lean::obj_tag(x_22) == 0)
{
obj* x_81; obj* x_83; 
lean::dec(x_22);
lean::dec(x_0);
x_81 = lean::cnstr_get(x_76, 0);
lean::inc(x_81);
x_83 = l_lean_elaborator_to__level___main(x_81, x_1, x_17);
if (lean::obj_tag(x_83) == 0)
{
obj* x_86; obj* x_89; 
lean::dec(x_19);
lean::dec(x_76);
x_86 = lean::cnstr_get(x_83, 0);
lean::inc(x_86);
lean::dec(x_83);
if (lean::is_scalar(x_14)) {
 x_89 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_89 = x_14;
}
lean::cnstr_set(x_89, 0, x_86);
return x_89;
}
else
{
obj* x_90; obj* x_93; obj* x_95; obj* x_98; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_90 = lean::cnstr_get(x_83, 0);
lean::inc(x_90);
lean::dec(x_83);
x_93 = lean::cnstr_get(x_90, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_90, 1);
lean::inc(x_95);
lean::dec(x_90);
x_98 = lean::cnstr_get(x_76, 2);
lean::inc(x_98);
lean::dec(x_76);
x_101 = l_lean_parser_number_view_to__nat___main(x_98);
x_102 = l_lean_elaborator_level__add___main(x_93, x_101);
if (lean::is_scalar(x_19)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_19;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_95);
if (lean::is_scalar(x_14)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_14;
}
lean::cnstr_set(x_104, 0, x_103);
return x_104;
}
}
else
{
obj* x_109; obj* x_111; 
lean::dec(x_22);
lean::dec(x_14);
lean::dec(x_19);
lean::dec(x_76);
x_109 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_109);
x_111 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_109, x_1, x_17);
return x_111;
}
}
}
}
else
{
obj* x_114; obj* x_115; obj* x_117; 
lean::dec(x_41);
lean::dec(x_45);
x_114 = l_lean_parser_level_leading_has__view;
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
x_117 = lean::apply_1(x_115, x_20);
switch (lean::obj_tag(x_117)) {
case 0:
{
lean::dec(x_117);
if (lean::obj_tag(x_22) == 0)
{
obj* x_122; obj* x_124; 
lean::dec(x_22);
lean::dec(x_14);
lean::dec(x_19);
x_122 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_122);
x_124 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_122, x_1, x_17);
return x_124;
}
else
{
obj* x_126; obj* x_128; obj* x_132; 
lean::dec(x_0);
x_126 = lean::cnstr_get(x_22, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_22, 1);
lean::inc(x_128);
lean::dec(x_22);
lean::inc(x_1);
x_132 = l_lean_elaborator_to__level___main(x_126, x_1, x_17);
if (lean::obj_tag(x_132) == 0)
{
obj* x_136; obj* x_139; 
lean::dec(x_1);
lean::dec(x_19);
lean::dec(x_128);
x_136 = lean::cnstr_get(x_132, 0);
lean::inc(x_136);
lean::dec(x_132);
if (lean::is_scalar(x_14)) {
 x_139 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_139 = x_14;
}
lean::cnstr_set(x_139, 0, x_136);
return x_139;
}
else
{
obj* x_140; obj* x_143; obj* x_145; obj* x_148; 
x_140 = lean::cnstr_get(x_132, 0);
lean::inc(x_140);
lean::dec(x_132);
x_143 = lean::cnstr_get(x_140, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_140, 1);
lean::inc(x_145);
lean::dec(x_140);
x_148 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_128, x_1, x_145);
if (lean::obj_tag(x_148) == 0)
{
obj* x_151; obj* x_154; 
lean::dec(x_19);
lean::dec(x_143);
x_151 = lean::cnstr_get(x_148, 0);
lean::inc(x_151);
lean::dec(x_148);
if (lean::is_scalar(x_14)) {
 x_154 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_154 = x_14;
}
lean::cnstr_set(x_154, 0, x_151);
return x_154;
}
else
{
obj* x_155; obj* x_158; obj* x_160; obj* x_163; obj* x_164; obj* x_165; 
x_155 = lean::cnstr_get(x_148, 0);
lean::inc(x_155);
lean::dec(x_148);
x_158 = lean::cnstr_get(x_155, 0);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_155, 1);
lean::inc(x_160);
lean::dec(x_155);
x_163 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__2(x_143, x_158);
if (lean::is_scalar(x_19)) {
 x_164 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_164 = x_19;
}
lean::cnstr_set(x_164, 0, x_163);
lean::cnstr_set(x_164, 1, x_160);
if (lean::is_scalar(x_14)) {
 x_165 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_165 = x_14;
}
lean::cnstr_set(x_165, 0, x_164);
return x_165;
}
}
}
}
case 1:
{
lean::dec(x_117);
if (lean::obj_tag(x_22) == 0)
{
obj* x_170; obj* x_172; 
lean::dec(x_22);
lean::dec(x_14);
lean::dec(x_19);
x_170 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_170);
x_172 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_170, x_1, x_17);
return x_172;
}
else
{
obj* x_174; obj* x_176; obj* x_180; 
lean::dec(x_0);
x_174 = lean::cnstr_get(x_22, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_22, 1);
lean::inc(x_176);
lean::dec(x_22);
lean::inc(x_1);
x_180 = l_lean_elaborator_to__level___main(x_174, x_1, x_17);
if (lean::obj_tag(x_180) == 0)
{
obj* x_184; obj* x_187; 
lean::dec(x_1);
lean::dec(x_19);
lean::dec(x_176);
x_184 = lean::cnstr_get(x_180, 0);
lean::inc(x_184);
lean::dec(x_180);
if (lean::is_scalar(x_14)) {
 x_187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_187 = x_14;
}
lean::cnstr_set(x_187, 0, x_184);
return x_187;
}
else
{
obj* x_188; obj* x_191; obj* x_193; obj* x_196; 
x_188 = lean::cnstr_get(x_180, 0);
lean::inc(x_188);
lean::dec(x_180);
x_191 = lean::cnstr_get(x_188, 0);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_188, 1);
lean::inc(x_193);
lean::dec(x_188);
x_196 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_176, x_1, x_193);
if (lean::obj_tag(x_196) == 0)
{
obj* x_199; obj* x_202; 
lean::dec(x_19);
lean::dec(x_191);
x_199 = lean::cnstr_get(x_196, 0);
lean::inc(x_199);
lean::dec(x_196);
if (lean::is_scalar(x_14)) {
 x_202 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_202 = x_14;
}
lean::cnstr_set(x_202, 0, x_199);
return x_202;
}
else
{
obj* x_203; obj* x_206; obj* x_208; obj* x_211; obj* x_212; obj* x_213; 
x_203 = lean::cnstr_get(x_196, 0);
lean::inc(x_203);
lean::dec(x_196);
x_206 = lean::cnstr_get(x_203, 0);
lean::inc(x_206);
x_208 = lean::cnstr_get(x_203, 1);
lean::inc(x_208);
lean::dec(x_203);
x_211 = l_list_foldr___main___at_lean_elaborator_to__level___main___spec__4(x_191, x_206);
if (lean::is_scalar(x_19)) {
 x_212 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_212 = x_19;
}
lean::cnstr_set(x_212, 0, x_211);
lean::cnstr_set(x_212, 1, x_208);
if (lean::is_scalar(x_14)) {
 x_213 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_213 = x_14;
}
lean::cnstr_set(x_213, 0, x_212);
return x_213;
}
}
}
}
case 2:
{
lean::dec(x_117);
if (lean::obj_tag(x_22) == 0)
{
obj* x_218; obj* x_220; obj* x_221; 
lean::dec(x_22);
lean::dec(x_1);
lean::dec(x_0);
x_218 = l_lean_elaborator_to__level___main___closed__3;
lean::inc(x_218);
if (lean::is_scalar(x_19)) {
 x_220 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_220 = x_19;
}
lean::cnstr_set(x_220, 0, x_218);
lean::cnstr_set(x_220, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_221 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_221 = x_14;
}
lean::cnstr_set(x_221, 0, x_220);
return x_221;
}
else
{
obj* x_225; obj* x_227; 
lean::dec(x_22);
lean::dec(x_14);
lean::dec(x_19);
x_225 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_225);
x_227 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_225, x_1, x_17);
return x_227;
}
}
case 3:
{
obj* x_232; obj* x_234; 
lean::dec(x_22);
lean::dec(x_14);
lean::dec(x_19);
lean::dec(x_117);
x_232 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_232);
x_234 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_232, x_1, x_17);
return x_234;
}
case 4:
{
obj* x_235; 
x_235 = lean::cnstr_get(x_117, 0);
lean::inc(x_235);
lean::dec(x_117);
if (lean::obj_tag(x_22) == 0)
{
obj* x_241; obj* x_242; obj* x_243; obj* x_244; 
lean::dec(x_22);
lean::dec(x_1);
lean::dec(x_0);
x_241 = l_lean_parser_number_view_to__nat___main(x_235);
x_242 = l_lean_level_of__nat___main(x_241);
if (lean::is_scalar(x_19)) {
 x_243 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_243 = x_19;
}
lean::cnstr_set(x_243, 0, x_242);
lean::cnstr_set(x_243, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_244 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_244 = x_14;
}
lean::cnstr_set(x_244, 0, x_243);
return x_244;
}
else
{
obj* x_249; obj* x_251; 
lean::dec(x_235);
lean::dec(x_22);
lean::dec(x_14);
lean::dec(x_19);
x_249 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_249);
x_251 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_249, x_1, x_17);
return x_251;
}
}
default:
{
obj* x_252; 
x_252 = lean::cnstr_get(x_117, 0);
lean::inc(x_252);
lean::dec(x_117);
if (lean::obj_tag(x_22) == 0)
{
obj* x_256; obj* x_257; obj* x_259; obj* x_263; 
lean::dec(x_22);
x_256 = l_lean_elaborator_mangle__ident(x_252);
x_257 = lean::cnstr_get(x_17, 4);
lean::inc(x_257);
x_259 = lean::cnstr_get(x_257, 1);
lean::inc(x_259);
lean::dec(x_257);
lean::inc(x_256);
x_263 = l_lean_elaborator_ordered__rbmap_find___at_lean_elaborator_to__level___main___spec__5(x_259, x_256);
if (lean::obj_tag(x_263) == 0)
{
obj* x_267; obj* x_269; obj* x_270; obj* x_272; obj* x_274; obj* x_275; obj* x_276; 
lean::dec(x_263);
lean::dec(x_14);
lean::dec(x_19);
x_267 = l_lean_name_to__string___closed__1;
lean::inc(x_267);
x_269 = l_lean_name_to__string__with__sep___main(x_267, x_256);
x_270 = l_lean_elaborator_to__level___main___closed__4;
lean::inc(x_270);
x_272 = lean::string_append(x_270, x_269);
lean::dec(x_269);
x_274 = l_char_has__repr___closed__1;
x_275 = lean::string_append(x_272, x_274);
x_276 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_275, x_1, x_17);
return x_276;
}
else
{
obj* x_280; obj* x_281; obj* x_282; 
lean::dec(x_263);
lean::dec(x_1);
lean::dec(x_0);
x_280 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_280, 0, x_256);
if (lean::is_scalar(x_19)) {
 x_281 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_281 = x_19;
}
lean::cnstr_set(x_281, 0, x_280);
lean::cnstr_set(x_281, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_282 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_282 = x_14;
}
lean::cnstr_set(x_282, 0, x_281);
return x_282;
}
}
else
{
obj* x_287; obj* x_289; 
lean::dec(x_252);
lean::dec(x_22);
lean::dec(x_14);
lean::dec(x_19);
x_287 = l_lean_elaborator_to__level___main___closed__2;
lean::inc(x_287);
x_289 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_287, x_1, x_17);
return x_289;
}
}
}
}
}
}
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
x_1 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
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
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
lean::inc(x_1);
x_14 = l_lean_elaborator_to__level___main(x_8, x_1, x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_20 = x_14;
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
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_24 = x_14;
}
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_29 = x_22;
}
x_30 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__1(x_10, x_1, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_37; 
lean::dec(x_12);
lean::dec(x_25);
lean::dec(x_29);
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
if (lean::is_scalar(x_24)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_24;
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
if (lean::is_scalar(x_12)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_12;
}
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_41);
if (lean::is_scalar(x_29)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_29;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_24)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_24;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
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
lean::dec(x_1);
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
x_9 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
lean::inc(x_1);
x_14 = l_lean_elaborator_to__level___main(x_8, x_1, x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_20 = x_14;
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
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_24 = x_14;
}
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_29 = x_22;
}
x_30 = l_list_mmap___main___at_lean_elaborator_to__level___main___spec__3(x_10, x_1, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_37; 
lean::dec(x_12);
lean::dec(x_25);
lean::dec(x_29);
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
if (lean::is_scalar(x_24)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_24;
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
if (lean::is_scalar(x_12)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_12;
}
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_41);
if (lean::is_scalar(x_29)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_29;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_24)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_24;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
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
lean::dec(x_1);
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
x_9 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
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
obj* l_lean_elaborator_to__level(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_elaborator_to__level___main(x_0, x_1, x_2);
return x_3;
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
x_6 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* _init_l_lean_elaborator_expr_mk__annotation___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("annotation");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_dummy() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Prop");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
return x_4;
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
obj* _init_l_lean_elaborator_mk__eqns___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_mk__eqns___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("pre_equations");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_21; unsigned char x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
lean::inc(x_0);
x_21 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1(x_0, x_7);
x_22 = 4;
x_23 = lean::box(x_22);
lean::inc(x_10);
x_25 = lean_expr_local(x_10, x_10, x_0, x_23);
x_26 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
lean::inc(x_26);
x_28 = l_lean_elaborator_expr_mk__annotation(x_26, x_25);
x_29 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_28, x_15);
x_30 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_17);
if (lean::is_scalar(x_9)) {
 x_31 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_31 = x_9;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_21);
return x_31;
}
}
}
obj* _init_l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_to__pexpr___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_5; 
x_5 = lean::box(0);
x_3 = x_5;
goto lbl_4;
}
case 1:
{
obj* x_6; 
x_6 = lean::box(0);
x_3 = x_6;
goto lbl_4;
}
case 2:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
lean::dec(x_7);
x_20 = l_lean_elaborator_to__pexpr___main___closed__7;
x_21 = lean::name_dec_eq(x_9, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_21);
x_23 = l_lean_elaborator_to__pexpr___main___closed__2;
x_24 = lean::name_dec_eq(x_9, x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_lean_elaborator_to__pexpr___main___closed__8;
x_26 = lean::name_dec_eq(x_9, x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_26);
x_28 = l_lean_elaborator_to__pexpr___main___closed__9;
x_29 = lean::name_dec_eq(x_9, x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_29);
x_31 = l_lean_parser_term_sort_has__view_x_27___lambda__1___closed__4;
x_32 = lean::name_dec_eq(x_9, x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_34; obj* x_35; 
lean::dec(x_32);
x_34 = l_lean_elaborator_to__pexpr___main___closed__10;
x_35 = lean::name_dec_eq(x_9, x_34);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; obj* x_38; 
lean::dec(x_35);
x_37 = l_lean_elaborator_to__pexpr___main___closed__11;
x_38 = lean::name_dec_eq(x_9, x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_40; obj* x_41; 
lean::dec(x_38);
x_40 = l_lean_elaborator_to__pexpr___main___closed__12;
x_41 = lean::name_dec_eq(x_9, x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_44; 
lean::dec(x_41);
x_43 = l_lean_elaborator_to__pexpr___main___closed__13;
x_44 = lean::name_dec_eq(x_9, x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_46; obj* x_47; 
lean::dec(x_44);
x_46 = l_lean_elaborator_to__pexpr___main___closed__14;
x_47 = lean::name_dec_eq(x_9, x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_49; obj* x_50; 
lean::dec(x_47);
x_49 = l_lean_elaborator_to__pexpr___main___closed__15;
x_50 = lean::name_dec_eq(x_9, x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_53; 
lean::dec(x_50);
x_52 = l_lean_elaborator_to__pexpr___main___closed__16;
x_53 = lean::name_dec_eq(x_9, x_52);
if (lean::obj_tag(x_53) == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_53);
x_55 = l_lean_elaborator_to__pexpr___main___closed__17;
x_56 = lean::name_dec_eq(x_9, x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_58; obj* x_59; 
lean::dec(x_56);
x_58 = l_lean_elaborator_to__pexpr___main___closed__18;
x_59 = lean::name_dec_eq(x_9, x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_59);
x_61 = l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
x_62 = lean::name_dec_eq(x_9, x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_62);
x_64 = l_lean_elaborator_to__pexpr___main___closed__19;
x_65 = lean::name_dec_eq(x_9, x_64);
if (lean::obj_tag(x_65) == 0)
{
obj* x_68; obj* x_69; 
lean::dec(x_11);
lean::dec(x_65);
x_68 = l_lean_elaborator_to__pexpr___main___closed__20;
x_69 = lean::name_dec_eq(x_9, x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_69);
x_71 = l_lean_elaborator_to__pexpr___main___closed__21;
x_72 = lean::name_dec_eq(x_9, x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_83; 
lean::dec(x_72);
x_74 = l_lean_name_to__string___closed__1;
lean::inc(x_74);
x_76 = l_lean_name_to__string__with__sep___main(x_74, x_9);
x_77 = l_lean_elaborator_to__pexpr___main___closed__22;
lean::inc(x_77);
x_79 = lean::string_append(x_77, x_76);
lean::dec(x_76);
lean::inc(x_1);
lean::inc(x_0);
x_83 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_79, x_1, x_2);
if (lean::obj_tag(x_83) == 0)
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_24);
lean::dec(x_1);
lean::dec(x_0);
x_87 = lean::cnstr_get(x_83, 0);
lean::inc(x_87);
if (lean::is_shared(x_83)) {
 lean::dec(x_83);
 x_89 = lean::box(0);
} else {
 lean::cnstr_release(x_83, 0);
 x_89 = x_83;
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
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_98; 
x_91 = lean::cnstr_get(x_83, 0);
lean::inc(x_91);
if (lean::is_shared(x_83)) {
 lean::dec(x_83);
 x_93 = lean::box(0);
} else {
 lean::cnstr_release(x_83, 0);
 x_93 = x_83;
}
x_94 = lean::cnstr_get(x_91, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_91, 1);
lean::inc(x_96);
if (lean::is_shared(x_91)) {
 lean::dec(x_91);
 x_98 = lean::box(0);
} else {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 x_98 = x_91;
}
if (lean::obj_tag(x_24) == 0)
{
obj* x_100; 
lean::dec(x_24);
x_100 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_100) == 0)
{
obj* x_103; obj* x_104; 
lean::dec(x_1);
lean::dec(x_100);
if (lean::is_scalar(x_98)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_98;
}
lean::cnstr_set(x_103, 0, x_94);
lean::cnstr_set(x_103, 1, x_96);
if (lean::is_scalar(x_93)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_93;
}
lean::cnstr_set(x_104, 0, x_103);
return x_104;
}
else
{
obj* x_105; obj* x_108; obj* x_111; obj* x_114; obj* x_115; obj* x_116; obj* x_118; obj* x_120; obj* x_121; obj* x_124; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
x_105 = lean::cnstr_get(x_100, 0);
lean::inc(x_105);
lean::dec(x_100);
x_108 = lean::cnstr_get(x_1, 0);
lean::inc(x_108);
lean::dec(x_1);
x_111 = lean::cnstr_get(x_108, 2);
lean::inc(x_111);
lean::dec(x_108);
x_114 = l_lean_file__map_to__position(x_111, x_105);
x_115 = lean::box(0);
x_116 = lean::cnstr_get(x_114, 1);
lean::inc(x_116);
x_118 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_118);
x_120 = l_lean_kvmap_set__nat(x_115, x_118, x_116);
x_121 = lean::cnstr_get(x_114, 0);
lean::inc(x_121);
lean::dec(x_114);
x_124 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_124);
x_126 = l_lean_kvmap_set__nat(x_120, x_124, x_121);
x_127 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_94);
if (lean::is_scalar(x_98)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_98;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_96);
if (lean::is_scalar(x_93)) {
 x_129 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_129 = x_93;
}
lean::cnstr_set(x_129, 0, x_128);
return x_129;
}
}
else
{
obj* x_133; obj* x_134; 
lean::dec(x_24);
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_98)) {
 x_133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_133 = x_98;
}
lean::cnstr_set(x_133, 0, x_94);
lean::cnstr_set(x_133, 1, x_96);
if (lean::is_scalar(x_93)) {
 x_134 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_134 = x_93;
}
lean::cnstr_set(x_134, 0, x_133);
return x_134;
}
}
}
else
{
obj* x_137; obj* x_138; obj* x_141; obj* x_142; obj* x_144; obj* x_146; 
lean::dec(x_24);
lean::dec(x_72);
x_137 = l_lean_parser_term_match_has__view;
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
lean::inc(x_0);
x_141 = lean::apply_1(x_138, x_0);
x_142 = lean::cnstr_get(x_141, 5);
lean::inc(x_142);
x_144 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(x_142);
lean::inc(x_1);
x_146 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_144, x_1, x_2);
if (lean::obj_tag(x_146) == 0)
{
obj* x_148; obj* x_150; obj* x_151; 
lean::dec(x_141);
x_148 = lean::cnstr_get(x_146, 0);
lean::inc(x_148);
if (lean::is_shared(x_146)) {
 lean::dec(x_146);
 x_150 = lean::box(0);
} else {
 lean::cnstr_release(x_146, 0);
 x_150 = x_146;
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
x_14 = x_151;
goto lbl_15;
}
else
{
obj* x_152; obj* x_154; obj* x_155; obj* x_157; obj* x_159; obj* x_160; obj* x_162; obj* x_164; 
x_152 = lean::cnstr_get(x_146, 0);
lean::inc(x_152);
if (lean::is_shared(x_146)) {
 lean::dec(x_146);
 x_154 = lean::box(0);
} else {
 lean::cnstr_release(x_146, 0);
 x_154 = x_146;
}
x_155 = lean::cnstr_get(x_152, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_152, 1);
lean::inc(x_157);
if (lean::is_shared(x_152)) {
 lean::dec(x_152);
 x_159 = lean::box(0);
} else {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_159 = x_152;
}
x_160 = lean::cnstr_get(x_141, 2);
lean::inc(x_160);
x_162 = l_lean_expander_get__opt__type___main(x_160);
lean::inc(x_1);
x_164 = l_lean_elaborator_to__pexpr___main(x_162, x_1, x_157);
if (lean::obj_tag(x_164) == 0)
{
obj* x_168; obj* x_171; 
lean::dec(x_155);
lean::dec(x_159);
lean::dec(x_141);
x_168 = lean::cnstr_get(x_164, 0);
lean::inc(x_168);
lean::dec(x_164);
if (lean::is_scalar(x_154)) {
 x_171 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_171 = x_154;
}
lean::cnstr_set(x_171, 0, x_168);
x_14 = x_171;
goto lbl_15;
}
else
{
obj* x_172; obj* x_175; obj* x_177; obj* x_180; 
x_172 = lean::cnstr_get(x_164, 0);
lean::inc(x_172);
lean::dec(x_164);
x_175 = lean::cnstr_get(x_172, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_172, 1);
lean::inc(x_177);
lean::dec(x_172);
x_180 = l_lean_elaborator_mk__eqns(x_175, x_155);
switch (lean::obj_tag(x_180)) {
case 0:
{
obj* x_185; obj* x_189; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_185 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_185);
lean::inc(x_0);
x_189 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_185, x_1, x_177);
x_14 = x_189;
goto lbl_15;
}
case 1:
{
obj* x_194; obj* x_198; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_194 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_194);
lean::inc(x_0);
x_198 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_194, x_1, x_177);
x_14 = x_198;
goto lbl_15;
}
case 2:
{
obj* x_203; obj* x_207; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_203 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_203);
lean::inc(x_0);
x_207 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_203, x_1, x_177);
x_14 = x_207;
goto lbl_15;
}
case 3:
{
obj* x_212; obj* x_216; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_212 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_212);
lean::inc(x_0);
x_216 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_212, x_1, x_177);
x_14 = x_216;
goto lbl_15;
}
case 4:
{
obj* x_221; obj* x_225; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_221 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_221);
lean::inc(x_0);
x_225 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_221, x_1, x_177);
x_14 = x_225;
goto lbl_15;
}
case 5:
{
obj* x_230; obj* x_234; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_230 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_230);
lean::inc(x_0);
x_234 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_230, x_1, x_177);
x_14 = x_234;
goto lbl_15;
}
case 6:
{
obj* x_239; obj* x_243; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_239 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_239);
lean::inc(x_0);
x_243 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_239, x_1, x_177);
x_14 = x_243;
goto lbl_15;
}
case 7:
{
obj* x_248; obj* x_252; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_248 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_248);
lean::inc(x_0);
x_252 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_248, x_1, x_177);
x_14 = x_252;
goto lbl_15;
}
case 8:
{
obj* x_257; obj* x_261; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_257 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_257);
lean::inc(x_0);
x_261 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_257, x_1, x_177);
x_14 = x_261;
goto lbl_15;
}
case 9:
{
obj* x_266; obj* x_270; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_266 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_266);
lean::inc(x_0);
x_270 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_266, x_1, x_177);
x_14 = x_270;
goto lbl_15;
}
case 10:
{
obj* x_271; obj* x_273; obj* x_275; obj* x_276; obj* x_280; 
x_271 = lean::cnstr_get(x_180, 0);
lean::inc(x_271);
x_273 = lean::cnstr_get(x_180, 1);
lean::inc(x_273);
if (lean::is_shared(x_180)) {
 lean::dec(x_180);
 x_275 = lean::box(0);
} else {
 lean::cnstr_release(x_180, 0);
 lean::cnstr_release(x_180, 1);
 x_275 = x_180;
}
x_276 = lean::cnstr_get(x_141, 1);
lean::inc(x_276);
lean::dec(x_141);
lean::inc(x_1);
x_280 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_276, x_1, x_177);
if (lean::obj_tag(x_280) == 0)
{
obj* x_285; obj* x_288; 
lean::dec(x_271);
lean::dec(x_275);
lean::dec(x_273);
lean::dec(x_159);
x_285 = lean::cnstr_get(x_280, 0);
lean::inc(x_285);
lean::dec(x_280);
if (lean::is_scalar(x_154)) {
 x_288 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_288 = x_154;
}
lean::cnstr_set(x_288, 0, x_285);
x_14 = x_288;
goto lbl_15;
}
else
{
obj* x_289; obj* x_292; obj* x_294; obj* x_297; unsigned char x_298; obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; 
x_289 = lean::cnstr_get(x_280, 0);
lean::inc(x_289);
lean::dec(x_280);
x_292 = lean::cnstr_get(x_289, 0);
lean::inc(x_292);
x_294 = lean::cnstr_get(x_289, 1);
lean::inc(x_294);
lean::dec(x_289);
x_297 = l_lean_elaborator_to__pexpr___main___closed__24;
x_298 = 1;
lean::inc(x_297);
x_300 = l_lean_kvmap_set__bool(x_271, x_297, x_298);
if (lean::is_scalar(x_275)) {
 x_301 = lean::alloc_cnstr(10, 2, 0);
} else {
 x_301 = x_275;
}
lean::cnstr_set(x_301, 0, x_300);
lean::cnstr_set(x_301, 1, x_273);
x_302 = l_list_foldl___main___at_lean_expr_mk__app___spec__1(x_301, x_292);
if (lean::is_scalar(x_159)) {
 x_303 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_303 = x_159;
}
lean::cnstr_set(x_303, 0, x_302);
lean::cnstr_set(x_303, 1, x_294);
if (lean::is_scalar(x_154)) {
 x_304 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_304 = x_154;
}
lean::cnstr_set(x_304, 0, x_303);
x_14 = x_304;
goto lbl_15;
}
}
default:
{
obj* x_309; obj* x_313; 
lean::dec(x_180);
lean::dec(x_154);
lean::dec(x_159);
lean::dec(x_141);
x_309 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_1);
lean::inc(x_309);
lean::inc(x_0);
x_313 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_309, x_1, x_177);
x_14 = x_313;
goto lbl_15;
}
}
}
}
}
}
else
{
obj* x_316; obj* x_317; obj* x_320; obj* x_321; obj* x_323; obj* x_324; obj* x_326; obj* x_328; obj* x_329; obj* x_330; obj* x_332; obj* x_334; 
lean::dec(x_24);
lean::dec(x_69);
x_316 = l_lean_parser_term_struct__inst_has__view;
x_317 = lean::cnstr_get(x_316, 0);
lean::inc(x_317);
lean::inc(x_0);
x_320 = lean::apply_1(x_317, x_0);
x_321 = lean::cnstr_get(x_320, 3);
lean::inc(x_321);
x_323 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_321);
x_324 = lean::cnstr_get(x_323, 0);
lean::inc(x_324);
x_326 = lean::cnstr_get(x_323, 1);
lean::inc(x_326);
if (lean::is_shared(x_323)) {
 lean::dec(x_323);
 x_328 = lean::box(0);
} else {
 lean::cnstr_release(x_323, 0);
 lean::cnstr_release(x_323, 1);
 x_328 = x_323;
}
x_329 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_326);
x_330 = lean::cnstr_get(x_329, 0);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_329, 1);
lean::inc(x_332);
if (lean::is_shared(x_329)) {
 lean::dec(x_329);
 x_334 = lean::box(0);
} else {
 lean::cnstr_release(x_329, 0);
 lean::cnstr_release(x_329, 1);
 x_334 = x_329;
}
if (lean::obj_tag(x_332) == 0)
{
obj* x_338; 
lean::dec(x_332);
lean::inc(x_1);
lean::inc(x_0);
x_338 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_324, x_1, x_2);
if (lean::obj_tag(x_338) == 0)
{
obj* x_346; obj* x_348; obj* x_349; 
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_330);
x_346 = lean::cnstr_get(x_338, 0);
lean::inc(x_346);
if (lean::is_shared(x_338)) {
 lean::dec(x_338);
 x_348 = lean::box(0);
} else {
 lean::cnstr_release(x_338, 0);
 x_348 = x_338;
}
if (lean::is_scalar(x_348)) {
 x_349 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_349 = x_348;
}
lean::cnstr_set(x_349, 0, x_346);
return x_349;
}
else
{
obj* x_350; obj* x_352; obj* x_353; obj* x_355; obj* x_358; obj* x_362; 
x_350 = lean::cnstr_get(x_338, 0);
lean::inc(x_350);
if (lean::is_shared(x_338)) {
 lean::dec(x_338);
 x_352 = lean::box(0);
} else {
 lean::cnstr_release(x_338, 0);
 x_352 = x_338;
}
x_353 = lean::cnstr_get(x_350, 0);
lean::inc(x_353);
x_355 = lean::cnstr_get(x_350, 1);
lean::inc(x_355);
lean::dec(x_350);
lean::inc(x_1);
lean::inc(x_0);
x_362 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_330, x_1, x_355);
if (lean::obj_tag(x_362) == 0)
{
obj* x_370; obj* x_373; 
lean::dec(x_320);
lean::dec(x_353);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
x_370 = lean::cnstr_get(x_362, 0);
lean::inc(x_370);
lean::dec(x_362);
if (lean::is_scalar(x_352)) {
 x_373 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_373 = x_352;
}
lean::cnstr_set(x_373, 0, x_370);
return x_373;
}
else
{
obj* x_374; obj* x_377; obj* x_379; obj* x_382; 
x_374 = lean::cnstr_get(x_362, 0);
lean::inc(x_374);
lean::dec(x_362);
x_377 = lean::cnstr_get(x_374, 0);
lean::inc(x_377);
x_379 = lean::cnstr_get(x_374, 1);
lean::inc(x_379);
lean::dec(x_374);
x_382 = lean::cnstr_get(x_320, 2);
lean::inc(x_382);
if (lean::obj_tag(x_382) == 0)
{
obj* x_386; 
lean::dec(x_352);
lean::dec(x_382);
if (lean::is_scalar(x_334)) {
 x_386 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_386 = x_334;
}
lean::cnstr_set(x_386, 0, x_377);
lean::cnstr_set(x_386, 1, x_379);
x_358 = x_386;
goto lbl_359;
}
else
{
obj* x_387; obj* x_390; obj* x_394; 
x_387 = lean::cnstr_get(x_382, 0);
lean::inc(x_387);
lean::dec(x_382);
x_390 = lean::cnstr_get(x_387, 0);
lean::inc(x_390);
lean::dec(x_387);
lean::inc(x_1);
x_394 = l_lean_elaborator_to__pexpr___main(x_390, x_1, x_379);
if (lean::obj_tag(x_394) == 0)
{
obj* x_403; obj* x_406; 
lean::dec(x_377);
lean::dec(x_320);
lean::dec(x_353);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
x_403 = lean::cnstr_get(x_394, 0);
lean::inc(x_403);
lean::dec(x_394);
if (lean::is_scalar(x_352)) {
 x_406 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_406 = x_352;
}
lean::cnstr_set(x_406, 0, x_403);
return x_406;
}
else
{
obj* x_408; obj* x_411; obj* x_413; obj* x_416; obj* x_417; obj* x_418; obj* x_419; 
lean::dec(x_352);
x_408 = lean::cnstr_get(x_394, 0);
lean::inc(x_408);
lean::dec(x_394);
x_411 = lean::cnstr_get(x_408, 0);
lean::inc(x_411);
x_413 = lean::cnstr_get(x_408, 1);
lean::inc(x_413);
lean::dec(x_408);
x_416 = lean::box(0);
x_417 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_417, 0, x_411);
lean::cnstr_set(x_417, 1, x_416);
x_418 = l_list_append___main___rarg(x_377, x_417);
if (lean::is_scalar(x_334)) {
 x_419 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_419 = x_334;
}
lean::cnstr_set(x_419, 0, x_418);
lean::cnstr_set(x_419, 1, x_413);
x_358 = x_419;
goto lbl_359;
}
}
}
lbl_359:
{
obj* x_420; obj* x_422; obj* x_425; obj* x_427; obj* x_428; obj* x_431; obj* x_432; unsigned char x_433; obj* x_435; obj* x_436; obj* x_439; obj* x_441; obj* x_442; obj* x_444; obj* x_445; obj* x_446; obj* x_448; obj* x_449; obj* x_450; obj* x_451; obj* x_452; 
x_420 = lean::cnstr_get(x_358, 0);
lean::inc(x_420);
x_422 = lean::cnstr_get(x_358, 1);
lean::inc(x_422);
lean::dec(x_358);
x_425 = lean::box(0);
lean::inc(x_353);
x_427 = l_list_length___main___rarg(x_353);
x_428 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_428);
lean::inc(x_425);
x_431 = l_lean_kvmap_set__nat(x_425, x_428, x_427);
x_432 = l_lean_elaborator_to__pexpr___main___closed__26;
x_433 = 0;
lean::inc(x_432);
x_435 = l_lean_kvmap_set__bool(x_431, x_432, x_433);
x_436 = lean::cnstr_get(x_320, 1);
lean::inc(x_436);
lean::dec(x_320);
x_439 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_439);
x_441 = l_option_map___rarg(x_439, x_436);
x_442 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_442);
x_444 = l_option_map___rarg(x_442, x_441);
x_445 = l_option_get__or__else___main___rarg(x_444, x_425);
x_446 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_446);
x_448 = l_lean_kvmap_set__name(x_435, x_446, x_445);
x_449 = l_list_append___main___rarg(x_353, x_420);
x_450 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(x_449);
x_451 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_451, 0, x_448);
lean::cnstr_set(x_451, 1, x_450);
if (lean::is_scalar(x_328)) {
 x_452 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_452 = x_328;
}
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_422);
x_16 = x_452;
goto lbl_17;
}
}
}
else
{
obj* x_453; obj* x_455; obj* x_457; obj* x_458; 
x_453 = lean::cnstr_get(x_332, 0);
lean::inc(x_453);
x_455 = lean::cnstr_get(x_332, 1);
lean::inc(x_455);
if (lean::is_shared(x_332)) {
 lean::dec(x_332);
 x_457 = lean::box(0);
} else {
 lean::cnstr_release(x_332, 0);
 lean::cnstr_release(x_332, 1);
 x_457 = x_332;
}
x_458 = lean::cnstr_get(x_453, 0);
lean::inc(x_458);
lean::dec(x_453);
if (lean::obj_tag(x_458) == 0)
{
obj* x_462; obj* x_463; obj* x_465; obj* x_466; obj* x_469; 
lean::dec(x_455);
x_462 = l_lean_parser_term_struct__inst__item_has__view;
x_463 = lean::cnstr_get(x_462, 1);
lean::inc(x_463);
x_465 = lean::apply_1(x_463, x_458);
x_466 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
lean::inc(x_466);
x_469 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_465, x_466, x_1, x_2);
if (lean::obj_tag(x_469) == 0)
{
obj* x_479; obj* x_481; obj* x_482; 
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_324);
lean::dec(x_330);
lean::dec(x_457);
x_479 = lean::cnstr_get(x_469, 0);
lean::inc(x_479);
if (lean::is_shared(x_469)) {
 lean::dec(x_469);
 x_481 = lean::box(0);
} else {
 lean::cnstr_release(x_469, 0);
 x_481 = x_469;
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
obj* x_483; obj* x_485; obj* x_486; obj* x_488; obj* x_493; 
x_483 = lean::cnstr_get(x_469, 0);
lean::inc(x_483);
if (lean::is_shared(x_469)) {
 lean::dec(x_469);
 x_485 = lean::box(0);
} else {
 lean::cnstr_release(x_469, 0);
 x_485 = x_469;
}
x_486 = lean::cnstr_get(x_483, 0);
lean::inc(x_486);
x_488 = lean::cnstr_get(x_483, 1);
lean::inc(x_488);
lean::dec(x_483);
lean::inc(x_1);
lean::inc(x_0);
x_493 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_324, x_1, x_488);
if (lean::obj_tag(x_493) == 0)
{
obj* x_503; obj* x_506; 
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_330);
lean::dec(x_457);
lean::dec(x_486);
x_503 = lean::cnstr_get(x_493, 0);
lean::inc(x_503);
lean::dec(x_493);
if (lean::is_scalar(x_485)) {
 x_506 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_506 = x_485;
}
lean::cnstr_set(x_506, 0, x_503);
return x_506;
}
else
{
obj* x_507; obj* x_510; obj* x_512; obj* x_515; obj* x_519; 
x_507 = lean::cnstr_get(x_493, 0);
lean::inc(x_507);
lean::dec(x_493);
x_510 = lean::cnstr_get(x_507, 0);
lean::inc(x_510);
x_512 = lean::cnstr_get(x_507, 1);
lean::inc(x_512);
lean::dec(x_507);
lean::inc(x_1);
lean::inc(x_0);
x_519 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_330, x_1, x_512);
if (lean::obj_tag(x_519) == 0)
{
obj* x_529; obj* x_532; 
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_457);
lean::dec(x_510);
lean::dec(x_486);
x_529 = lean::cnstr_get(x_519, 0);
lean::inc(x_529);
lean::dec(x_519);
if (lean::is_scalar(x_485)) {
 x_532 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_532 = x_485;
}
lean::cnstr_set(x_532, 0, x_529);
return x_532;
}
else
{
obj* x_533; obj* x_536; obj* x_538; obj* x_541; 
x_533 = lean::cnstr_get(x_519, 0);
lean::inc(x_533);
lean::dec(x_519);
x_536 = lean::cnstr_get(x_533, 0);
lean::inc(x_536);
x_538 = lean::cnstr_get(x_533, 1);
lean::inc(x_538);
lean::dec(x_533);
x_541 = lean::cnstr_get(x_320, 2);
lean::inc(x_541);
if (lean::obj_tag(x_541) == 0)
{
obj* x_546; 
lean::dec(x_457);
lean::dec(x_485);
lean::dec(x_541);
if (lean::is_scalar(x_334)) {
 x_546 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_546 = x_334;
}
lean::cnstr_set(x_546, 0, x_536);
lean::cnstr_set(x_546, 1, x_538);
x_515 = x_546;
goto lbl_516;
}
else
{
obj* x_547; obj* x_550; obj* x_554; 
x_547 = lean::cnstr_get(x_541, 0);
lean::inc(x_547);
lean::dec(x_541);
x_550 = lean::cnstr_get(x_547, 0);
lean::inc(x_550);
lean::dec(x_547);
lean::inc(x_1);
x_554 = l_lean_elaborator_to__pexpr___main(x_550, x_1, x_538);
if (lean::obj_tag(x_554) == 0)
{
obj* x_565; obj* x_568; 
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_457);
lean::dec(x_510);
lean::dec(x_486);
lean::dec(x_536);
x_565 = lean::cnstr_get(x_554, 0);
lean::inc(x_565);
lean::dec(x_554);
if (lean::is_scalar(x_485)) {
 x_568 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_568 = x_485;
}
lean::cnstr_set(x_568, 0, x_565);
return x_568;
}
else
{
obj* x_570; obj* x_573; obj* x_575; obj* x_578; obj* x_579; obj* x_580; obj* x_581; 
lean::dec(x_485);
x_570 = lean::cnstr_get(x_554, 0);
lean::inc(x_570);
lean::dec(x_554);
x_573 = lean::cnstr_get(x_570, 0);
lean::inc(x_573);
x_575 = lean::cnstr_get(x_570, 1);
lean::inc(x_575);
lean::dec(x_570);
x_578 = lean::box(0);
if (lean::is_scalar(x_457)) {
 x_579 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_579 = x_457;
}
lean::cnstr_set(x_579, 0, x_573);
lean::cnstr_set(x_579, 1, x_578);
x_580 = l_list_append___main___rarg(x_536, x_579);
if (lean::is_scalar(x_334)) {
 x_581 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_581 = x_334;
}
lean::cnstr_set(x_581, 0, x_580);
lean::cnstr_set(x_581, 1, x_575);
x_515 = x_581;
goto lbl_516;
}
}
}
lbl_516:
{
obj* x_582; obj* x_584; obj* x_587; obj* x_589; obj* x_590; obj* x_593; obj* x_594; unsigned char x_595; obj* x_598; obj* x_599; obj* x_602; obj* x_604; obj* x_605; obj* x_607; obj* x_608; obj* x_609; obj* x_611; obj* x_612; obj* x_613; obj* x_614; obj* x_615; 
x_582 = lean::cnstr_get(x_515, 0);
lean::inc(x_582);
x_584 = lean::cnstr_get(x_515, 1);
lean::inc(x_584);
lean::dec(x_515);
x_587 = lean::box(0);
lean::inc(x_510);
x_589 = l_list_length___main___rarg(x_510);
x_590 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_590);
lean::inc(x_587);
x_593 = l_lean_kvmap_set__nat(x_587, x_590, x_589);
x_594 = l_lean_elaborator_to__pexpr___main___closed__26;
x_595 = lean::unbox(x_486);
lean::dec(x_486);
lean::inc(x_594);
x_598 = l_lean_kvmap_set__bool(x_593, x_594, x_595);
x_599 = lean::cnstr_get(x_320, 1);
lean::inc(x_599);
lean::dec(x_320);
x_602 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_602);
x_604 = l_option_map___rarg(x_602, x_599);
x_605 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_605);
x_607 = l_option_map___rarg(x_605, x_604);
x_608 = l_option_get__or__else___main___rarg(x_607, x_587);
x_609 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_609);
x_611 = l_lean_kvmap_set__name(x_598, x_609, x_608);
x_612 = l_list_append___main___rarg(x_510, x_582);
x_613 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_612);
x_614 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_614, 0, x_611);
lean::cnstr_set(x_614, 1, x_613);
if (lean::is_scalar(x_328)) {
 x_615 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_615 = x_328;
}
lean::cnstr_set(x_615, 0, x_614);
lean::cnstr_set(x_615, 1, x_584);
x_16 = x_615;
goto lbl_17;
}
}
}
}
else
{
if (lean::obj_tag(x_455) == 0)
{
obj* x_620; 
lean::dec(x_458);
lean::dec(x_455);
lean::inc(x_1);
lean::inc(x_0);
x_620 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_324, x_1, x_2);
if (lean::obj_tag(x_620) == 0)
{
obj* x_629; obj* x_631; obj* x_632; 
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_330);
lean::dec(x_457);
x_629 = lean::cnstr_get(x_620, 0);
lean::inc(x_629);
if (lean::is_shared(x_620)) {
 lean::dec(x_620);
 x_631 = lean::box(0);
} else {
 lean::cnstr_release(x_620, 0);
 x_631 = x_620;
}
if (lean::is_scalar(x_631)) {
 x_632 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_632 = x_631;
}
lean::cnstr_set(x_632, 0, x_629);
return x_632;
}
else
{
obj* x_633; obj* x_635; obj* x_636; obj* x_638; obj* x_641; obj* x_645; 
x_633 = lean::cnstr_get(x_620, 0);
lean::inc(x_633);
if (lean::is_shared(x_620)) {
 lean::dec(x_620);
 x_635 = lean::box(0);
} else {
 lean::cnstr_release(x_620, 0);
 x_635 = x_620;
}
x_636 = lean::cnstr_get(x_633, 0);
lean::inc(x_636);
x_638 = lean::cnstr_get(x_633, 1);
lean::inc(x_638);
lean::dec(x_633);
lean::inc(x_1);
lean::inc(x_0);
x_645 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_330, x_1, x_638);
if (lean::obj_tag(x_645) == 0)
{
obj* x_654; obj* x_657; 
lean::dec(x_636);
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_457);
x_654 = lean::cnstr_get(x_645, 0);
lean::inc(x_654);
lean::dec(x_645);
if (lean::is_scalar(x_635)) {
 x_657 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_657 = x_635;
}
lean::cnstr_set(x_657, 0, x_654);
return x_657;
}
else
{
obj* x_658; obj* x_661; obj* x_663; obj* x_666; 
x_658 = lean::cnstr_get(x_645, 0);
lean::inc(x_658);
lean::dec(x_645);
x_661 = lean::cnstr_get(x_658, 0);
lean::inc(x_661);
x_663 = lean::cnstr_get(x_658, 1);
lean::inc(x_663);
lean::dec(x_658);
x_666 = lean::cnstr_get(x_320, 2);
lean::inc(x_666);
if (lean::obj_tag(x_666) == 0)
{
obj* x_671; 
lean::dec(x_666);
lean::dec(x_635);
lean::dec(x_457);
if (lean::is_scalar(x_334)) {
 x_671 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_671 = x_334;
}
lean::cnstr_set(x_671, 0, x_661);
lean::cnstr_set(x_671, 1, x_663);
x_641 = x_671;
goto lbl_642;
}
else
{
obj* x_672; obj* x_675; obj* x_679; 
x_672 = lean::cnstr_get(x_666, 0);
lean::inc(x_672);
lean::dec(x_666);
x_675 = lean::cnstr_get(x_672, 0);
lean::inc(x_675);
lean::dec(x_672);
lean::inc(x_1);
x_679 = l_lean_elaborator_to__pexpr___main(x_675, x_1, x_663);
if (lean::obj_tag(x_679) == 0)
{
obj* x_689; obj* x_692; 
lean::dec(x_661);
lean::dec(x_636);
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_457);
x_689 = lean::cnstr_get(x_679, 0);
lean::inc(x_689);
lean::dec(x_679);
if (lean::is_scalar(x_635)) {
 x_692 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_692 = x_635;
}
lean::cnstr_set(x_692, 0, x_689);
return x_692;
}
else
{
obj* x_694; obj* x_697; obj* x_699; obj* x_702; obj* x_703; obj* x_704; obj* x_705; 
lean::dec(x_635);
x_694 = lean::cnstr_get(x_679, 0);
lean::inc(x_694);
lean::dec(x_679);
x_697 = lean::cnstr_get(x_694, 0);
lean::inc(x_697);
x_699 = lean::cnstr_get(x_694, 1);
lean::inc(x_699);
lean::dec(x_694);
x_702 = lean::box(0);
if (lean::is_scalar(x_457)) {
 x_703 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_703 = x_457;
}
lean::cnstr_set(x_703, 0, x_697);
lean::cnstr_set(x_703, 1, x_702);
x_704 = l_list_append___main___rarg(x_661, x_703);
if (lean::is_scalar(x_334)) {
 x_705 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_705 = x_334;
}
lean::cnstr_set(x_705, 0, x_704);
lean::cnstr_set(x_705, 1, x_699);
x_641 = x_705;
goto lbl_642;
}
}
}
lbl_642:
{
obj* x_706; obj* x_708; obj* x_711; obj* x_713; obj* x_714; obj* x_717; obj* x_718; unsigned char x_719; obj* x_721; obj* x_722; obj* x_725; obj* x_727; obj* x_728; obj* x_730; obj* x_731; obj* x_732; obj* x_734; obj* x_735; obj* x_736; obj* x_737; obj* x_738; 
x_706 = lean::cnstr_get(x_641, 0);
lean::inc(x_706);
x_708 = lean::cnstr_get(x_641, 1);
lean::inc(x_708);
lean::dec(x_641);
x_711 = lean::box(0);
lean::inc(x_636);
x_713 = l_list_length___main___rarg(x_636);
x_714 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_714);
lean::inc(x_711);
x_717 = l_lean_kvmap_set__nat(x_711, x_714, x_713);
x_718 = l_lean_elaborator_to__pexpr___main___closed__26;
x_719 = 1;
lean::inc(x_718);
x_721 = l_lean_kvmap_set__bool(x_717, x_718, x_719);
x_722 = lean::cnstr_get(x_320, 1);
lean::inc(x_722);
lean::dec(x_320);
x_725 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_725);
x_727 = l_option_map___rarg(x_725, x_722);
x_728 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_728);
x_730 = l_option_map___rarg(x_728, x_727);
x_731 = l_option_get__or__else___main___rarg(x_730, x_711);
x_732 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_732);
x_734 = l_lean_kvmap_set__name(x_721, x_732, x_731);
x_735 = l_list_append___main___rarg(x_636, x_706);
x_736 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_735);
x_737 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_737, 0, x_734);
lean::cnstr_set(x_737, 1, x_736);
if (lean::is_scalar(x_328)) {
 x_738 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_738 = x_328;
}
lean::cnstr_set(x_738, 0, x_737);
lean::cnstr_set(x_738, 1, x_708);
x_16 = x_738;
goto lbl_17;
}
}
}
else
{
obj* x_740; obj* x_741; obj* x_743; obj* x_744; obj* x_747; 
lean::dec(x_455);
x_740 = l_lean_parser_term_struct__inst__item_has__view;
x_741 = lean::cnstr_get(x_740, 1);
lean::inc(x_741);
x_743 = lean::apply_1(x_741, x_458);
x_744 = l_lean_elaborator_to__pexpr___main___closed__30;
lean::inc(x_1);
lean::inc(x_744);
x_747 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_743, x_744, x_1, x_2);
if (lean::obj_tag(x_747) == 0)
{
obj* x_757; obj* x_759; obj* x_760; 
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_324);
lean::dec(x_330);
lean::dec(x_457);
x_757 = lean::cnstr_get(x_747, 0);
lean::inc(x_757);
if (lean::is_shared(x_747)) {
 lean::dec(x_747);
 x_759 = lean::box(0);
} else {
 lean::cnstr_release(x_747, 0);
 x_759 = x_747;
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
obj* x_761; obj* x_763; obj* x_764; obj* x_766; obj* x_771; 
x_761 = lean::cnstr_get(x_747, 0);
lean::inc(x_761);
if (lean::is_shared(x_747)) {
 lean::dec(x_747);
 x_763 = lean::box(0);
} else {
 lean::cnstr_release(x_747, 0);
 x_763 = x_747;
}
x_764 = lean::cnstr_get(x_761, 0);
lean::inc(x_764);
x_766 = lean::cnstr_get(x_761, 1);
lean::inc(x_766);
lean::dec(x_761);
lean::inc(x_1);
lean::inc(x_0);
x_771 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_324, x_1, x_766);
if (lean::obj_tag(x_771) == 0)
{
obj* x_781; obj* x_784; 
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_330);
lean::dec(x_457);
lean::dec(x_764);
x_781 = lean::cnstr_get(x_771, 0);
lean::inc(x_781);
lean::dec(x_771);
if (lean::is_scalar(x_763)) {
 x_784 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_784 = x_763;
}
lean::cnstr_set(x_784, 0, x_781);
return x_784;
}
else
{
obj* x_785; obj* x_788; obj* x_790; obj* x_793; obj* x_797; 
x_785 = lean::cnstr_get(x_771, 0);
lean::inc(x_785);
lean::dec(x_771);
x_788 = lean::cnstr_get(x_785, 0);
lean::inc(x_788);
x_790 = lean::cnstr_get(x_785, 1);
lean::inc(x_790);
lean::dec(x_785);
lean::inc(x_1);
lean::inc(x_0);
x_797 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_330, x_1, x_790);
if (lean::obj_tag(x_797) == 0)
{
obj* x_807; obj* x_810; 
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_457);
lean::dec(x_764);
lean::dec(x_788);
x_807 = lean::cnstr_get(x_797, 0);
lean::inc(x_807);
lean::dec(x_797);
if (lean::is_scalar(x_763)) {
 x_810 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_810 = x_763;
}
lean::cnstr_set(x_810, 0, x_807);
return x_810;
}
else
{
obj* x_811; obj* x_814; obj* x_816; obj* x_819; 
x_811 = lean::cnstr_get(x_797, 0);
lean::inc(x_811);
lean::dec(x_797);
x_814 = lean::cnstr_get(x_811, 0);
lean::inc(x_814);
x_816 = lean::cnstr_get(x_811, 1);
lean::inc(x_816);
lean::dec(x_811);
x_819 = lean::cnstr_get(x_320, 2);
lean::inc(x_819);
if (lean::obj_tag(x_819) == 0)
{
obj* x_824; 
lean::dec(x_819);
lean::dec(x_457);
lean::dec(x_763);
if (lean::is_scalar(x_334)) {
 x_824 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_824 = x_334;
}
lean::cnstr_set(x_824, 0, x_814);
lean::cnstr_set(x_824, 1, x_816);
x_793 = x_824;
goto lbl_794;
}
else
{
obj* x_825; obj* x_828; obj* x_832; 
x_825 = lean::cnstr_get(x_819, 0);
lean::inc(x_825);
lean::dec(x_819);
x_828 = lean::cnstr_get(x_825, 0);
lean::inc(x_828);
lean::dec(x_825);
lean::inc(x_1);
x_832 = l_lean_elaborator_to__pexpr___main(x_828, x_1, x_816);
if (lean::obj_tag(x_832) == 0)
{
obj* x_843; obj* x_846; 
lean::dec(x_320);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_328);
lean::dec(x_334);
lean::dec(x_457);
lean::dec(x_764);
lean::dec(x_788);
lean::dec(x_814);
x_843 = lean::cnstr_get(x_832, 0);
lean::inc(x_843);
lean::dec(x_832);
if (lean::is_scalar(x_763)) {
 x_846 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_846 = x_763;
}
lean::cnstr_set(x_846, 0, x_843);
return x_846;
}
else
{
obj* x_848; obj* x_851; obj* x_853; obj* x_856; obj* x_857; obj* x_858; obj* x_859; 
lean::dec(x_763);
x_848 = lean::cnstr_get(x_832, 0);
lean::inc(x_848);
lean::dec(x_832);
x_851 = lean::cnstr_get(x_848, 0);
lean::inc(x_851);
x_853 = lean::cnstr_get(x_848, 1);
lean::inc(x_853);
lean::dec(x_848);
x_856 = lean::box(0);
if (lean::is_scalar(x_457)) {
 x_857 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_857 = x_457;
}
lean::cnstr_set(x_857, 0, x_851);
lean::cnstr_set(x_857, 1, x_856);
x_858 = l_list_append___main___rarg(x_814, x_857);
if (lean::is_scalar(x_334)) {
 x_859 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_859 = x_334;
}
lean::cnstr_set(x_859, 0, x_858);
lean::cnstr_set(x_859, 1, x_853);
x_793 = x_859;
goto lbl_794;
}
}
}
lbl_794:
{
obj* x_860; obj* x_862; obj* x_865; obj* x_867; obj* x_868; obj* x_871; obj* x_872; unsigned char x_873; obj* x_876; obj* x_877; obj* x_880; obj* x_882; obj* x_883; obj* x_885; obj* x_886; obj* x_887; obj* x_889; obj* x_890; obj* x_891; obj* x_892; obj* x_893; 
x_860 = lean::cnstr_get(x_793, 0);
lean::inc(x_860);
x_862 = lean::cnstr_get(x_793, 1);
lean::inc(x_862);
lean::dec(x_793);
x_865 = lean::box(0);
lean::inc(x_788);
x_867 = l_list_length___main___rarg(x_788);
x_868 = l_lean_elaborator_to__pexpr___main___closed__25;
lean::inc(x_868);
lean::inc(x_865);
x_871 = l_lean_kvmap_set__nat(x_865, x_868, x_867);
x_872 = l_lean_elaborator_to__pexpr___main___closed__26;
x_873 = lean::unbox(x_764);
lean::dec(x_764);
lean::inc(x_872);
x_876 = l_lean_kvmap_set__bool(x_871, x_872, x_873);
x_877 = lean::cnstr_get(x_320, 1);
lean::inc(x_877);
lean::dec(x_320);
x_880 = l_lean_elaborator_to__pexpr___main___closed__27;
lean::inc(x_880);
x_882 = l_option_map___rarg(x_880, x_877);
x_883 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_883);
x_885 = l_option_map___rarg(x_883, x_882);
x_886 = l_option_get__or__else___main___rarg(x_885, x_865);
x_887 = l_lean_elaborator_to__pexpr___main___closed__29;
lean::inc(x_887);
x_889 = l_lean_kvmap_set__name(x_876, x_887, x_886);
x_890 = l_list_append___main___rarg(x_788, x_860);
x_891 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_890);
x_892 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_892, 0, x_889);
lean::cnstr_set(x_892, 1, x_891);
if (lean::is_scalar(x_328)) {
 x_893 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_893 = x_328;
}
lean::cnstr_set(x_893, 0, x_892);
lean::cnstr_set(x_893, 1, x_862);
x_16 = x_893;
goto lbl_17;
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
obj* x_898; 
lean::dec(x_24);
lean::dec(x_65);
lean::inc(x_1);
lean::inc(x_11);
x_898 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_11, x_1, x_2);
if (lean::obj_tag(x_898) == 0)
{
obj* x_903; obj* x_905; obj* x_906; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_903 = lean::cnstr_get(x_898, 0);
lean::inc(x_903);
if (lean::is_shared(x_898)) {
 lean::dec(x_898);
 x_905 = lean::box(0);
} else {
 lean::cnstr_release(x_898, 0);
 x_905 = x_898;
}
if (lean::is_scalar(x_905)) {
 x_906 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_906 = x_905;
}
lean::cnstr_set(x_906, 0, x_903);
return x_906;
}
else
{
obj* x_907; obj* x_910; obj* x_912; obj* x_914; obj* x_915; obj* x_916; 
x_907 = lean::cnstr_get(x_898, 0);
lean::inc(x_907);
lean::dec(x_898);
x_910 = lean::cnstr_get(x_907, 0);
lean::inc(x_910);
x_912 = lean::cnstr_get(x_907, 1);
lean::inc(x_912);
if (lean::is_shared(x_907)) {
 lean::dec(x_907);
 x_914 = lean::box(0);
} else {
 lean::cnstr_release(x_907, 0);
 lean::cnstr_release(x_907, 1);
 x_914 = x_907;
}
x_915 = l_list_reverse___rarg(x_910);
if (lean::is_scalar(x_914)) {
 x_916 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_916 = x_914;
}
lean::cnstr_set(x_916, 0, x_915);
lean::cnstr_set(x_916, 1, x_912);
x_18 = x_916;
goto lbl_19;
}
}
}
else
{
obj* x_920; obj* x_921; obj* x_924; obj* x_925; obj* x_926; obj* x_927; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_62);
x_920 = l_lean_parser_number_has__view;
x_921 = lean::cnstr_get(x_920, 0);
lean::inc(x_921);
lean::inc(x_0);
x_924 = lean::apply_1(x_921, x_0);
x_925 = l_lean_parser_number_view_to__nat___main(x_924);
x_926 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_926, 0, x_925);
x_927 = lean::alloc_cnstr(9, 1, 0);
lean::cnstr_set(x_927, 0, x_926);
if (lean::obj_tag(x_24) == 0)
{
obj* x_929; 
lean::dec(x_24);
x_929 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_929) == 0)
{
obj* x_932; obj* x_933; 
lean::dec(x_929);
lean::dec(x_1);
x_932 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_932, 0, x_927);
lean::cnstr_set(x_932, 1, x_2);
x_933 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_933, 0, x_932);
return x_933;
}
else
{
obj* x_934; obj* x_937; obj* x_940; obj* x_943; obj* x_944; obj* x_945; obj* x_947; obj* x_949; obj* x_950; obj* x_953; obj* x_955; obj* x_956; obj* x_957; obj* x_958; 
x_934 = lean::cnstr_get(x_929, 0);
lean::inc(x_934);
lean::dec(x_929);
x_937 = lean::cnstr_get(x_1, 0);
lean::inc(x_937);
lean::dec(x_1);
x_940 = lean::cnstr_get(x_937, 2);
lean::inc(x_940);
lean::dec(x_937);
x_943 = l_lean_file__map_to__position(x_940, x_934);
x_944 = lean::box(0);
x_945 = lean::cnstr_get(x_943, 1);
lean::inc(x_945);
x_947 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_947);
x_949 = l_lean_kvmap_set__nat(x_944, x_947, x_945);
x_950 = lean::cnstr_get(x_943, 0);
lean::inc(x_950);
lean::dec(x_943);
x_953 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_953);
x_955 = l_lean_kvmap_set__nat(x_949, x_953, x_950);
x_956 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_956, 0, x_955);
lean::cnstr_set(x_956, 1, x_927);
x_957 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_957, 0, x_956);
lean::cnstr_set(x_957, 1, x_2);
x_958 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_958, 0, x_957);
return x_958;
}
}
else
{
obj* x_962; obj* x_963; 
lean::dec(x_24);
lean::dec(x_1);
lean::dec(x_0);
x_962 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_962, 0, x_927);
lean::cnstr_set(x_962, 1, x_2);
x_963 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_963, 0, x_962);
return x_963;
}
}
}
else
{
obj* x_967; obj* x_968; obj* x_971; obj* x_972; obj* x_976; 
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_59);
x_967 = l_lean_parser_term_inaccessible_has__view;
x_968 = lean::cnstr_get(x_967, 0);
lean::inc(x_968);
lean::inc(x_0);
x_971 = lean::apply_1(x_968, x_0);
x_972 = lean::cnstr_get(x_971, 1);
lean::inc(x_972);
lean::dec(x_971);
lean::inc(x_1);
x_976 = l_lean_elaborator_to__pexpr___main(x_972, x_1, x_2);
if (lean::obj_tag(x_976) == 0)
{
obj* x_980; obj* x_982; obj* x_983; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_980 = lean::cnstr_get(x_976, 0);
lean::inc(x_980);
if (lean::is_shared(x_976)) {
 lean::dec(x_976);
 x_982 = lean::box(0);
} else {
 lean::cnstr_release(x_976, 0);
 x_982 = x_976;
}
if (lean::is_scalar(x_982)) {
 x_983 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_983 = x_982;
}
lean::cnstr_set(x_983, 0, x_980);
return x_983;
}
else
{
obj* x_984; obj* x_987; obj* x_989; obj* x_991; obj* x_992; obj* x_994; obj* x_995; 
x_984 = lean::cnstr_get(x_976, 0);
lean::inc(x_984);
lean::dec(x_976);
x_987 = lean::cnstr_get(x_984, 0);
lean::inc(x_987);
x_989 = lean::cnstr_get(x_984, 1);
lean::inc(x_989);
if (lean::is_shared(x_984)) {
 lean::dec(x_984);
 x_991 = lean::box(0);
} else {
 lean::cnstr_release(x_984, 0);
 lean::cnstr_release(x_984, 1);
 x_991 = x_984;
}
x_992 = l_lean_elaborator_to__pexpr___main___closed__31;
lean::inc(x_992);
x_994 = l_lean_elaborator_expr_mk__annotation(x_992, x_987);
if (lean::is_scalar(x_991)) {
 x_995 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_995 = x_991;
}
lean::cnstr_set(x_995, 0, x_994);
lean::cnstr_set(x_995, 1, x_989);
x_16 = x_995;
goto lbl_17;
}
}
}
else
{
obj* x_999; obj* x_1000; obj* x_1003; obj* x_1004; obj* x_1006; obj* x_1007; obj* x_1009; obj* x_1012; 
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_56);
x_999 = l_lean_parser_term_explicit_has__view;
x_1000 = lean::cnstr_get(x_999, 0);
lean::inc(x_1000);
lean::inc(x_0);
x_1003 = lean::apply_1(x_1000, x_0);
x_1004 = lean::cnstr_get(x_1003, 0);
lean::inc(x_1004);
x_1006 = l_lean_parser_ident__univs_has__view;
x_1007 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1007);
x_1009 = lean::cnstr_get(x_1003, 1);
lean::inc(x_1009);
lean::dec(x_1003);
x_1012 = lean::apply_1(x_1007, x_1009);
if (lean::obj_tag(x_1004) == 0)
{
obj* x_1015; 
lean::dec(x_1004);
lean::inc(x_1);
x_1015 = l_lean_elaborator_to__pexpr___main(x_1012, x_1, x_2);
if (lean::obj_tag(x_1015) == 0)
{
obj* x_1019; obj* x_1021; obj* x_1022; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1019 = lean::cnstr_get(x_1015, 0);
lean::inc(x_1019);
if (lean::is_shared(x_1015)) {
 lean::dec(x_1015);
 x_1021 = lean::box(0);
} else {
 lean::cnstr_release(x_1015, 0);
 x_1021 = x_1015;
}
if (lean::is_scalar(x_1021)) {
 x_1022 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1022 = x_1021;
}
lean::cnstr_set(x_1022, 0, x_1019);
return x_1022;
}
else
{
obj* x_1023; obj* x_1026; obj* x_1028; obj* x_1030; obj* x_1031; obj* x_1033; obj* x_1034; 
x_1023 = lean::cnstr_get(x_1015, 0);
lean::inc(x_1023);
lean::dec(x_1015);
x_1026 = lean::cnstr_get(x_1023, 0);
lean::inc(x_1026);
x_1028 = lean::cnstr_get(x_1023, 1);
lean::inc(x_1028);
if (lean::is_shared(x_1023)) {
 lean::dec(x_1023);
 x_1030 = lean::box(0);
} else {
 lean::cnstr_release(x_1023, 0);
 lean::cnstr_release(x_1023, 1);
 x_1030 = x_1023;
}
x_1031 = l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1;
lean::inc(x_1031);
x_1033 = l_lean_elaborator_expr_mk__annotation(x_1031, x_1026);
if (lean::is_scalar(x_1030)) {
 x_1034 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1034 = x_1030;
}
lean::cnstr_set(x_1034, 0, x_1033);
lean::cnstr_set(x_1034, 1, x_1028);
x_16 = x_1034;
goto lbl_17;
}
}
else
{
obj* x_1037; 
lean::dec(x_1004);
lean::inc(x_1);
x_1037 = l_lean_elaborator_to__pexpr___main(x_1012, x_1, x_2);
if (lean::obj_tag(x_1037) == 0)
{
obj* x_1041; obj* x_1043; obj* x_1044; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1041 = lean::cnstr_get(x_1037, 0);
lean::inc(x_1041);
if (lean::is_shared(x_1037)) {
 lean::dec(x_1037);
 x_1043 = lean::box(0);
} else {
 lean::cnstr_release(x_1037, 0);
 x_1043 = x_1037;
}
if (lean::is_scalar(x_1043)) {
 x_1044 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1044 = x_1043;
}
lean::cnstr_set(x_1044, 0, x_1041);
return x_1044;
}
else
{
obj* x_1045; obj* x_1048; obj* x_1050; obj* x_1052; obj* x_1053; obj* x_1055; obj* x_1056; 
x_1045 = lean::cnstr_get(x_1037, 0);
lean::inc(x_1045);
lean::dec(x_1037);
x_1048 = lean::cnstr_get(x_1045, 0);
lean::inc(x_1048);
x_1050 = lean::cnstr_get(x_1045, 1);
lean::inc(x_1050);
if (lean::is_shared(x_1045)) {
 lean::dec(x_1045);
 x_1052 = lean::box(0);
} else {
 lean::cnstr_release(x_1045, 0);
 lean::cnstr_release(x_1045, 1);
 x_1052 = x_1045;
}
x_1053 = l_lean_elaborator_to__pexpr___main___closed__32;
lean::inc(x_1053);
x_1055 = l_lean_elaborator_expr_mk__annotation(x_1053, x_1048);
if (lean::is_scalar(x_1052)) {
 x_1056 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1056 = x_1052;
}
lean::cnstr_set(x_1056, 0, x_1055);
lean::cnstr_set(x_1056, 1, x_1050);
x_16 = x_1056;
goto lbl_17;
}
}
}
}
else
{
obj* x_1060; obj* x_1061; obj* x_1064; obj* x_1065; obj* x_1067; 
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_53);
x_1060 = l_lean_parser_term_projection_has__view;
x_1061 = lean::cnstr_get(x_1060, 0);
lean::inc(x_1061);
lean::inc(x_0);
x_1064 = lean::apply_1(x_1061, x_0);
x_1065 = lean::cnstr_get(x_1064, 2);
lean::inc(x_1065);
x_1067 = lean::cnstr_get(x_1064, 0);
lean::inc(x_1067);
lean::dec(x_1064);
if (lean::obj_tag(x_1065) == 0)
{
obj* x_1070; obj* x_1074; 
x_1070 = lean::cnstr_get(x_1065, 0);
lean::inc(x_1070);
lean::dec(x_1065);
lean::inc(x_1);
x_1074 = l_lean_elaborator_to__pexpr___main(x_1067, x_1, x_2);
if (lean::obj_tag(x_1074) == 0)
{
obj* x_1079; obj* x_1081; obj* x_1082; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1070);
x_1079 = lean::cnstr_get(x_1074, 0);
lean::inc(x_1079);
if (lean::is_shared(x_1074)) {
 lean::dec(x_1074);
 x_1081 = lean::box(0);
} else {
 lean::cnstr_release(x_1074, 0);
 x_1081 = x_1074;
}
if (lean::is_scalar(x_1081)) {
 x_1082 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1082 = x_1081;
}
lean::cnstr_set(x_1082, 0, x_1079);
return x_1082;
}
else
{
obj* x_1083; obj* x_1086; obj* x_1088; obj* x_1090; obj* x_1091; obj* x_1094; obj* x_1095; obj* x_1096; obj* x_1098; obj* x_1099; obj* x_1100; 
x_1083 = lean::cnstr_get(x_1074, 0);
lean::inc(x_1083);
lean::dec(x_1074);
x_1086 = lean::cnstr_get(x_1083, 0);
lean::inc(x_1086);
x_1088 = lean::cnstr_get(x_1083, 1);
lean::inc(x_1088);
if (lean::is_shared(x_1083)) {
 lean::dec(x_1083);
 x_1090 = lean::box(0);
} else {
 lean::cnstr_release(x_1083, 0);
 lean::cnstr_release(x_1083, 1);
 x_1090 = x_1083;
}
x_1091 = lean::cnstr_get(x_1070, 2);
lean::inc(x_1091);
lean::dec(x_1070);
x_1094 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1094, 0, x_1091);
x_1095 = lean::box(0);
x_1096 = l_lean_elaborator_to__pexpr___main___closed__33;
lean::inc(x_1096);
x_1098 = l_lean_kvmap_insert__core___main(x_1095, x_1096, x_1094);
x_1099 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_1099, 0, x_1098);
lean::cnstr_set(x_1099, 1, x_1086);
if (lean::is_scalar(x_1090)) {
 x_1100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1100 = x_1090;
}
lean::cnstr_set(x_1100, 0, x_1099);
lean::cnstr_set(x_1100, 1, x_1088);
x_16 = x_1100;
goto lbl_17;
}
}
else
{
obj* x_1101; obj* x_1105; 
x_1101 = lean::cnstr_get(x_1065, 0);
lean::inc(x_1101);
lean::dec(x_1065);
lean::inc(x_1);
x_1105 = l_lean_elaborator_to__pexpr___main(x_1067, x_1, x_2);
if (lean::obj_tag(x_1105) == 0)
{
obj* x_1110; obj* x_1112; obj* x_1113; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1101);
x_1110 = lean::cnstr_get(x_1105, 0);
lean::inc(x_1110);
if (lean::is_shared(x_1105)) {
 lean::dec(x_1105);
 x_1112 = lean::box(0);
} else {
 lean::cnstr_release(x_1105, 0);
 x_1112 = x_1105;
}
if (lean::is_scalar(x_1112)) {
 x_1113 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1113 = x_1112;
}
lean::cnstr_set(x_1113, 0, x_1110);
return x_1113;
}
else
{
obj* x_1114; obj* x_1117; obj* x_1119; obj* x_1121; obj* x_1122; obj* x_1123; obj* x_1124; obj* x_1125; obj* x_1127; obj* x_1128; obj* x_1129; 
x_1114 = lean::cnstr_get(x_1105, 0);
lean::inc(x_1114);
lean::dec(x_1105);
x_1117 = lean::cnstr_get(x_1114, 0);
lean::inc(x_1117);
x_1119 = lean::cnstr_get(x_1114, 1);
lean::inc(x_1119);
if (lean::is_shared(x_1114)) {
 lean::dec(x_1114);
 x_1121 = lean::box(0);
} else {
 lean::cnstr_release(x_1114, 0);
 lean::cnstr_release(x_1114, 1);
 x_1121 = x_1114;
}
x_1122 = l_lean_parser_number_view_to__nat___main(x_1101);
x_1123 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1123, 0, x_1122);
x_1124 = lean::box(0);
x_1125 = l_lean_elaborator_to__pexpr___main___closed__33;
lean::inc(x_1125);
x_1127 = l_lean_kvmap_insert__core___main(x_1124, x_1125, x_1123);
x_1128 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_1128, 0, x_1127);
lean::cnstr_set(x_1128, 1, x_1117);
if (lean::is_scalar(x_1121)) {
 x_1129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1129 = x_1121;
}
lean::cnstr_set(x_1129, 0, x_1128);
lean::cnstr_set(x_1129, 1, x_1119);
x_16 = x_1129;
goto lbl_17;
}
}
}
}
else
{
obj* x_1133; obj* x_1134; obj* x_1137; obj* x_1138; 
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_50);
x_1133 = l_lean_parser_term_let_has__view;
x_1134 = lean::cnstr_get(x_1133, 0);
lean::inc(x_1134);
lean::inc(x_0);
x_1137 = lean::apply_1(x_1134, x_0);
x_1138 = lean::cnstr_get(x_1137, 1);
lean::inc(x_1138);
if (lean::obj_tag(x_1138) == 0)
{
obj* x_1140; obj* x_1143; obj* x_1145; obj* x_1147; 
x_1140 = lean::cnstr_get(x_1138, 0);
lean::inc(x_1140);
lean::dec(x_1138);
x_1143 = lean::cnstr_get(x_1140, 0);
lean::inc(x_1143);
x_1145 = lean::cnstr_get(x_1140, 1);
lean::inc(x_1145);
x_1147 = lean::cnstr_get(x_1140, 2);
lean::inc(x_1147);
lean::dec(x_1140);
if (lean::obj_tag(x_1145) == 0)
{
lean::dec(x_1145);
if (lean::obj_tag(x_1147) == 0)
{
obj* x_1154; obj* x_1158; 
lean::dec(x_1137);
lean::dec(x_1143);
lean::dec(x_1147);
x_1154 = l_lean_elaborator_to__pexpr___main___closed__34;
lean::inc(x_1);
lean::inc(x_1154);
lean::inc(x_0);
x_1158 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1154, x_1, x_2);
if (lean::obj_tag(x_1158) == 0)
{
obj* x_1162; obj* x_1164; obj* x_1165; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1162 = lean::cnstr_get(x_1158, 0);
lean::inc(x_1162);
if (lean::is_shared(x_1158)) {
 lean::dec(x_1158);
 x_1164 = lean::box(0);
} else {
 lean::cnstr_release(x_1158, 0);
 x_1164 = x_1158;
}
if (lean::is_scalar(x_1164)) {
 x_1165 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1165 = x_1164;
}
lean::cnstr_set(x_1165, 0, x_1162);
return x_1165;
}
else
{
obj* x_1166; 
x_1166 = lean::cnstr_get(x_1158, 0);
lean::inc(x_1166);
lean::dec(x_1158);
x_16 = x_1166;
goto lbl_17;
}
}
else
{
obj* x_1169; obj* x_1172; obj* x_1176; 
x_1169 = lean::cnstr_get(x_1147, 0);
lean::inc(x_1169);
lean::dec(x_1147);
x_1172 = lean::cnstr_get(x_1169, 1);
lean::inc(x_1172);
lean::dec(x_1169);
lean::inc(x_1);
x_1176 = l_lean_elaborator_to__pexpr___main(x_1172, x_1, x_2);
if (lean::obj_tag(x_1176) == 0)
{
obj* x_1182; obj* x_1184; obj* x_1185; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1137);
lean::dec(x_1143);
x_1182 = lean::cnstr_get(x_1176, 0);
lean::inc(x_1182);
if (lean::is_shared(x_1176)) {
 lean::dec(x_1176);
 x_1184 = lean::box(0);
} else {
 lean::cnstr_release(x_1176, 0);
 x_1184 = x_1176;
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
obj* x_1186; obj* x_1188; obj* x_1189; obj* x_1191; obj* x_1193; obj* x_1194; obj* x_1197; 
x_1186 = lean::cnstr_get(x_1176, 0);
lean::inc(x_1186);
if (lean::is_shared(x_1176)) {
 lean::dec(x_1176);
 x_1188 = lean::box(0);
} else {
 lean::cnstr_release(x_1176, 0);
 x_1188 = x_1176;
}
x_1189 = lean::cnstr_get(x_1186, 0);
lean::inc(x_1189);
x_1191 = lean::cnstr_get(x_1186, 1);
lean::inc(x_1191);
if (lean::is_shared(x_1186)) {
 lean::dec(x_1186);
 x_1193 = lean::box(0);
} else {
 lean::cnstr_release(x_1186, 0);
 lean::cnstr_release(x_1186, 1);
 x_1193 = x_1186;
}
x_1194 = lean::cnstr_get(x_1137, 3);
lean::inc(x_1194);
lean::inc(x_1);
x_1197 = l_lean_elaborator_to__pexpr___main(x_1194, x_1, x_1191);
if (lean::obj_tag(x_1197) == 0)
{
obj* x_1205; obj* x_1208; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1193);
lean::dec(x_1137);
lean::dec(x_1143);
lean::dec(x_1189);
x_1205 = lean::cnstr_get(x_1197, 0);
lean::inc(x_1205);
lean::dec(x_1197);
if (lean::is_scalar(x_1188)) {
 x_1208 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1208 = x_1188;
}
lean::cnstr_set(x_1208, 0, x_1205);
return x_1208;
}
else
{
obj* x_1209; obj* x_1212; obj* x_1214; obj* x_1217; obj* x_1221; 
x_1209 = lean::cnstr_get(x_1197, 0);
lean::inc(x_1209);
lean::dec(x_1197);
x_1212 = lean::cnstr_get(x_1209, 0);
lean::inc(x_1212);
x_1214 = lean::cnstr_get(x_1209, 1);
lean::inc(x_1214);
lean::dec(x_1209);
x_1217 = lean::cnstr_get(x_1137, 5);
lean::inc(x_1217);
lean::dec(x_1137);
lean::inc(x_1);
x_1221 = l_lean_elaborator_to__pexpr___main(x_1217, x_1, x_1214);
if (lean::obj_tag(x_1221) == 0)
{
obj* x_1229; obj* x_1232; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1193);
lean::dec(x_1212);
lean::dec(x_1143);
lean::dec(x_1189);
x_1229 = lean::cnstr_get(x_1221, 0);
lean::inc(x_1229);
lean::dec(x_1221);
if (lean::is_scalar(x_1188)) {
 x_1232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1232 = x_1188;
}
lean::cnstr_set(x_1232, 0, x_1229);
return x_1232;
}
else
{
obj* x_1234; obj* x_1237; obj* x_1239; obj* x_1242; obj* x_1243; obj* x_1244; 
lean::dec(x_1188);
x_1234 = lean::cnstr_get(x_1221, 0);
lean::inc(x_1234);
lean::dec(x_1221);
x_1237 = lean::cnstr_get(x_1234, 0);
lean::inc(x_1237);
x_1239 = lean::cnstr_get(x_1234, 1);
lean::inc(x_1239);
lean::dec(x_1234);
x_1242 = l_lean_elaborator_mangle__ident(x_1143);
x_1243 = lean::alloc_cnstr(8, 4, 0);
lean::cnstr_set(x_1243, 0, x_1242);
lean::cnstr_set(x_1243, 1, x_1189);
lean::cnstr_set(x_1243, 2, x_1212);
lean::cnstr_set(x_1243, 3, x_1237);
if (lean::is_scalar(x_1193)) {
 x_1244 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1244 = x_1193;
}
lean::cnstr_set(x_1244, 0, x_1243);
lean::cnstr_set(x_1244, 1, x_1239);
x_16 = x_1244;
goto lbl_17;
}
}
}
}
}
else
{
obj* x_1249; obj* x_1253; 
lean::dec(x_1137);
lean::dec(x_1143);
lean::dec(x_1147);
lean::dec(x_1145);
x_1249 = l_lean_elaborator_to__pexpr___main___closed__34;
lean::inc(x_1);
lean::inc(x_1249);
lean::inc(x_0);
x_1253 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1249, x_1, x_2);
if (lean::obj_tag(x_1253) == 0)
{
obj* x_1257; obj* x_1259; obj* x_1260; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1257 = lean::cnstr_get(x_1253, 0);
lean::inc(x_1257);
if (lean::is_shared(x_1253)) {
 lean::dec(x_1253);
 x_1259 = lean::box(0);
} else {
 lean::cnstr_release(x_1253, 0);
 x_1259 = x_1253;
}
if (lean::is_scalar(x_1259)) {
 x_1260 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1260 = x_1259;
}
lean::cnstr_set(x_1260, 0, x_1257);
return x_1260;
}
else
{
obj* x_1261; 
x_1261 = lean::cnstr_get(x_1253, 0);
lean::inc(x_1261);
lean::dec(x_1253);
x_16 = x_1261;
goto lbl_17;
}
}
}
else
{
obj* x_1266; obj* x_1270; 
lean::dec(x_1138);
lean::dec(x_1137);
x_1266 = l_lean_elaborator_to__pexpr___main___closed__34;
lean::inc(x_1);
lean::inc(x_1266);
lean::inc(x_0);
x_1270 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1266, x_1, x_2);
if (lean::obj_tag(x_1270) == 0)
{
obj* x_1274; obj* x_1276; obj* x_1277; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1274 = lean::cnstr_get(x_1270, 0);
lean::inc(x_1274);
if (lean::is_shared(x_1270)) {
 lean::dec(x_1270);
 x_1276 = lean::box(0);
} else {
 lean::cnstr_release(x_1270, 0);
 x_1276 = x_1270;
}
if (lean::is_scalar(x_1276)) {
 x_1277 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1277 = x_1276;
}
lean::cnstr_set(x_1277, 0, x_1274);
return x_1277;
}
else
{
obj* x_1278; 
x_1278 = lean::cnstr_get(x_1270, 0);
lean::inc(x_1278);
lean::dec(x_1270);
x_16 = x_1278;
goto lbl_17;
}
}
}
}
else
{
obj* x_1284; obj* x_1285; obj* x_1288; obj* x_1289; obj* x_1292; 
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_47);
x_1284 = l_lean_parser_term_show_has__view;
x_1285 = lean::cnstr_get(x_1284, 0);
lean::inc(x_1285);
lean::inc(x_0);
x_1288 = lean::apply_1(x_1285, x_0);
x_1289 = lean::cnstr_get(x_1288, 1);
lean::inc(x_1289);
lean::inc(x_1);
x_1292 = l_lean_elaborator_to__pexpr___main(x_1289, x_1, x_2);
if (lean::obj_tag(x_1292) == 0)
{
obj* x_1297; obj* x_1299; obj* x_1300; 
lean::dec(x_1288);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1297 = lean::cnstr_get(x_1292, 0);
lean::inc(x_1297);
if (lean::is_shared(x_1292)) {
 lean::dec(x_1292);
 x_1299 = lean::box(0);
} else {
 lean::cnstr_release(x_1292, 0);
 x_1299 = x_1292;
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
obj* x_1301; obj* x_1303; obj* x_1304; obj* x_1306; obj* x_1308; obj* x_1309; obj* x_1312; obj* x_1316; 
x_1301 = lean::cnstr_get(x_1292, 0);
lean::inc(x_1301);
if (lean::is_shared(x_1292)) {
 lean::dec(x_1292);
 x_1303 = lean::box(0);
} else {
 lean::cnstr_release(x_1292, 0);
 x_1303 = x_1292;
}
x_1304 = lean::cnstr_get(x_1301, 0);
lean::inc(x_1304);
x_1306 = lean::cnstr_get(x_1301, 1);
lean::inc(x_1306);
if (lean::is_shared(x_1301)) {
 lean::dec(x_1301);
 x_1308 = lean::box(0);
} else {
 lean::cnstr_release(x_1301, 0);
 lean::cnstr_release(x_1301, 1);
 x_1308 = x_1301;
}
x_1309 = lean::cnstr_get(x_1288, 3);
lean::inc(x_1309);
lean::dec(x_1288);
x_1312 = lean::cnstr_get(x_1309, 1);
lean::inc(x_1312);
lean::dec(x_1309);
lean::inc(x_1);
x_1316 = l_lean_elaborator_to__pexpr___main(x_1312, x_1, x_1306);
if (lean::obj_tag(x_1316) == 0)
{
obj* x_1322; obj* x_1325; 
lean::dec(x_1304);
lean::dec(x_1308);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1322 = lean::cnstr_get(x_1316, 0);
lean::inc(x_1322);
lean::dec(x_1316);
if (lean::is_scalar(x_1303)) {
 x_1325 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1325 = x_1303;
}
lean::cnstr_set(x_1325, 0, x_1322);
return x_1325;
}
else
{
obj* x_1327; obj* x_1330; obj* x_1332; obj* x_1335; unsigned char x_1336; obj* x_1337; obj* x_1340; obj* x_1341; obj* x_1342; obj* x_1343; obj* x_1345; obj* x_1346; 
lean::dec(x_1303);
x_1327 = lean::cnstr_get(x_1316, 0);
lean::inc(x_1327);
lean::dec(x_1316);
x_1330 = lean::cnstr_get(x_1327, 0);
lean::inc(x_1330);
x_1332 = lean::cnstr_get(x_1327, 1);
lean::inc(x_1332);
lean::dec(x_1327);
x_1335 = l_lean_elaborator_to__pexpr___main___closed__35;
x_1336 = 0;
x_1337 = l_lean_elaborator_to__pexpr___main___closed__36;
lean::inc(x_1337);
lean::inc(x_1335);
x_1340 = lean::alloc_cnstr(6, 3, 1);
lean::cnstr_set(x_1340, 0, x_1335);
lean::cnstr_set(x_1340, 1, x_1304);
lean::cnstr_set(x_1340, 2, x_1337);
lean::cnstr_set_scalar(x_1340, sizeof(void*)*3, x_1336);
x_1341 = x_1340;
x_1342 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_1342, 0, x_1341);
lean::cnstr_set(x_1342, 1, x_1330);
x_1343 = l_lean_elaborator_to__pexpr___main___closed__37;
lean::inc(x_1343);
x_1345 = l_lean_elaborator_expr_mk__annotation(x_1343, x_1342);
if (lean::is_scalar(x_1308)) {
 x_1346 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1346 = x_1308;
}
lean::cnstr_set(x_1346, 0, x_1345);
lean::cnstr_set(x_1346, 1, x_1332);
x_16 = x_1346;
goto lbl_17;
}
}
}
}
else
{
obj* x_1350; obj* x_1351; obj* x_1354; obj* x_1355; obj* x_1357; obj* x_1360; 
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_44);
x_1350 = l_lean_parser_term_have_has__view;
x_1351 = lean::cnstr_get(x_1350, 0);
lean::inc(x_1351);
lean::inc(x_0);
x_1354 = lean::apply_1(x_1351, x_0);
x_1357 = lean::cnstr_get(x_1354, 2);
lean::inc(x_1357);
lean::inc(x_1);
x_1360 = l_lean_elaborator_to__pexpr___main(x_1357, x_1, x_2);
if (lean::obj_tag(x_1360) == 0)
{
obj* x_1365; obj* x_1367; obj* x_1368; 
lean::dec(x_1354);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1365 = lean::cnstr_get(x_1360, 0);
lean::inc(x_1365);
if (lean::is_shared(x_1360)) {
 lean::dec(x_1360);
 x_1367 = lean::box(0);
} else {
 lean::cnstr_release(x_1360, 0);
 x_1367 = x_1360;
}
if (lean::is_scalar(x_1367)) {
 x_1368 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1368 = x_1367;
}
lean::cnstr_set(x_1368, 0, x_1365);
return x_1368;
}
else
{
obj* x_1369; obj* x_1371; obj* x_1372; obj* x_1374; obj* x_1376; obj* x_1377; obj* x_1380; 
x_1369 = lean::cnstr_get(x_1360, 0);
lean::inc(x_1369);
if (lean::is_shared(x_1360)) {
 lean::dec(x_1360);
 x_1371 = lean::box(0);
} else {
 lean::cnstr_release(x_1360, 0);
 x_1371 = x_1360;
}
x_1372 = lean::cnstr_get(x_1369, 0);
lean::inc(x_1372);
x_1374 = lean::cnstr_get(x_1369, 1);
lean::inc(x_1374);
if (lean::is_shared(x_1369)) {
 lean::dec(x_1369);
 x_1376 = lean::box(0);
} else {
 lean::cnstr_release(x_1369, 0);
 lean::cnstr_release(x_1369, 1);
 x_1376 = x_1369;
}
x_1377 = lean::cnstr_get(x_1354, 5);
lean::inc(x_1377);
lean::inc(x_1);
x_1380 = l_lean_elaborator_to__pexpr___main(x_1377, x_1, x_1374);
if (lean::obj_tag(x_1380) == 0)
{
obj* x_1387; obj* x_1390; 
lean::dec(x_1354);
lean::dec(x_1376);
lean::dec(x_1372);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1387 = lean::cnstr_get(x_1380, 0);
lean::inc(x_1387);
lean::dec(x_1380);
if (lean::is_scalar(x_1371)) {
 x_1390 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1390 = x_1371;
}
lean::cnstr_set(x_1390, 0, x_1387);
return x_1390;
}
else
{
obj* x_1392; obj* x_1395; obj* x_1397; obj* x_1400; obj* x_1402; obj* x_1404; obj* x_1405; obj* x_1407; obj* x_1408; obj* x_1410; unsigned char x_1411; obj* x_1412; obj* x_1413; obj* x_1414; 
lean::dec(x_1371);
x_1392 = lean::cnstr_get(x_1380, 0);
lean::inc(x_1392);
lean::dec(x_1380);
x_1395 = lean::cnstr_get(x_1392, 0);
lean::inc(x_1395);
x_1397 = lean::cnstr_get(x_1392, 1);
lean::inc(x_1397);
lean::dec(x_1392);
x_1400 = lean::cnstr_get(x_1354, 1);
lean::inc(x_1400);
x_1402 = l_lean_elaborator_to__pexpr___main___closed__39;
lean::inc(x_1402);
x_1404 = l_option_map___rarg(x_1402, x_1400);
x_1405 = l_lean_elaborator_to__pexpr___main___closed__28;
lean::inc(x_1405);
x_1407 = l_option_map___rarg(x_1405, x_1404);
x_1408 = l_lean_elaborator_to__pexpr___main___closed__35;
lean::inc(x_1408);
x_1410 = l_option_get__or__else___main___rarg(x_1407, x_1408);
x_1411 = 0;
x_1412 = lean::alloc_cnstr(6, 3, 1);
lean::cnstr_set(x_1412, 0, x_1410);
lean::cnstr_set(x_1412, 1, x_1372);
lean::cnstr_set(x_1412, 2, x_1395);
lean::cnstr_set_scalar(x_1412, sizeof(void*)*3, x_1411);
x_1413 = x_1412;
if (lean::is_scalar(x_1376)) {
 x_1414 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1414 = x_1376;
}
lean::cnstr_set(x_1414, 0, x_1413);
lean::cnstr_set(x_1414, 1, x_1397);
x_1355 = x_1414;
goto lbl_1356;
}
}
lbl_1356:
{
obj* x_1415; obj* x_1417; obj* x_1419; obj* x_1420; 
x_1415 = lean::cnstr_get(x_1355, 0);
lean::inc(x_1415);
x_1417 = lean::cnstr_get(x_1355, 1);
lean::inc(x_1417);
if (lean::is_shared(x_1355)) {
 lean::dec(x_1355);
 x_1419 = lean::box(0);
} else {
 lean::cnstr_release(x_1355, 0);
 lean::cnstr_release(x_1355, 1);
 x_1419 = x_1355;
}
x_1420 = lean::cnstr_get(x_1354, 3);
lean::inc(x_1420);
lean::dec(x_1354);
if (lean::obj_tag(x_1420) == 0)
{
obj* x_1423; obj* x_1426; obj* x_1430; 
x_1423 = lean::cnstr_get(x_1420, 0);
lean::inc(x_1423);
lean::dec(x_1420);
x_1426 = lean::cnstr_get(x_1423, 1);
lean::inc(x_1426);
lean::dec(x_1423);
lean::inc(x_1);
x_1430 = l_lean_elaborator_to__pexpr___main(x_1426, x_1, x_1417);
if (lean::obj_tag(x_1430) == 0)
{
obj* x_1436; obj* x_1438; obj* x_1439; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1419);
lean::dec(x_1415);
x_1436 = lean::cnstr_get(x_1430, 0);
lean::inc(x_1436);
if (lean::is_shared(x_1430)) {
 lean::dec(x_1430);
 x_1438 = lean::box(0);
} else {
 lean::cnstr_release(x_1430, 0);
 x_1438 = x_1430;
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
obj* x_1440; obj* x_1443; obj* x_1445; obj* x_1448; obj* x_1450; obj* x_1451; obj* x_1452; 
x_1440 = lean::cnstr_get(x_1430, 0);
lean::inc(x_1440);
lean::dec(x_1430);
x_1443 = lean::cnstr_get(x_1440, 0);
lean::inc(x_1443);
x_1445 = lean::cnstr_get(x_1440, 1);
lean::inc(x_1445);
lean::dec(x_1440);
x_1448 = l_lean_elaborator_to__pexpr___main___closed__38;
lean::inc(x_1448);
x_1450 = l_lean_elaborator_expr_mk__annotation(x_1448, x_1415);
x_1451 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_1451, 0, x_1450);
lean::cnstr_set(x_1451, 1, x_1443);
if (lean::is_scalar(x_1419)) {
 x_1452 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1452 = x_1419;
}
lean::cnstr_set(x_1452, 0, x_1451);
lean::cnstr_set(x_1452, 1, x_1445);
x_16 = x_1452;
goto lbl_17;
}
}
else
{
obj* x_1453; obj* x_1456; obj* x_1459; obj* x_1463; 
x_1453 = lean::cnstr_get(x_1420, 0);
lean::inc(x_1453);
lean::dec(x_1420);
x_1456 = lean::cnstr_get(x_1453, 1);
lean::inc(x_1456);
lean::dec(x_1453);
x_1459 = lean::cnstr_get(x_1456, 1);
lean::inc(x_1459);
lean::dec(x_1456);
lean::inc(x_1);
x_1463 = l_lean_elaborator_to__pexpr___main(x_1459, x_1, x_1417);
if (lean::obj_tag(x_1463) == 0)
{
obj* x_1469; obj* x_1471; obj* x_1472; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1419);
lean::dec(x_1415);
x_1469 = lean::cnstr_get(x_1463, 0);
lean::inc(x_1469);
if (lean::is_shared(x_1463)) {
 lean::dec(x_1463);
 x_1471 = lean::box(0);
} else {
 lean::cnstr_release(x_1463, 0);
 x_1471 = x_1463;
}
if (lean::is_scalar(x_1471)) {
 x_1472 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1472 = x_1471;
}
lean::cnstr_set(x_1472, 0, x_1469);
return x_1472;
}
else
{
obj* x_1473; obj* x_1476; obj* x_1478; obj* x_1481; obj* x_1483; obj* x_1484; obj* x_1485; 
x_1473 = lean::cnstr_get(x_1463, 0);
lean::inc(x_1473);
lean::dec(x_1463);
x_1476 = lean::cnstr_get(x_1473, 0);
lean::inc(x_1476);
x_1478 = lean::cnstr_get(x_1473, 1);
lean::inc(x_1478);
lean::dec(x_1473);
x_1481 = l_lean_elaborator_to__pexpr___main___closed__38;
lean::inc(x_1481);
x_1483 = l_lean_elaborator_expr_mk__annotation(x_1481, x_1415);
x_1484 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_1484, 0, x_1483);
lean::cnstr_set(x_1484, 1, x_1476);
if (lean::is_scalar(x_1419)) {
 x_1485 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1485 = x_1419;
}
lean::cnstr_set(x_1485, 0, x_1484);
lean::cnstr_set(x_1485, 1, x_1478);
x_16 = x_1485;
goto lbl_17;
}
}
}
}
}
else
{
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_41);
if (lean::obj_tag(x_24) == 0)
{
obj* x_1490; 
lean::dec(x_24);
x_1490 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1490) == 0)
{
obj* x_1493; obj* x_1495; obj* x_1496; 
lean::dec(x_1);
lean::dec(x_1490);
x_1493 = l_lean_elaborator_to__pexpr___main___closed__40;
lean::inc(x_1493);
x_1495 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1495, 0, x_1493);
lean::cnstr_set(x_1495, 1, x_2);
x_1496 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1496, 0, x_1495);
return x_1496;
}
else
{
obj* x_1497; obj* x_1500; obj* x_1503; obj* x_1506; obj* x_1507; obj* x_1508; obj* x_1510; obj* x_1512; obj* x_1513; obj* x_1516; obj* x_1518; obj* x_1519; obj* x_1521; obj* x_1522; obj* x_1523; 
x_1497 = lean::cnstr_get(x_1490, 0);
lean::inc(x_1497);
lean::dec(x_1490);
x_1500 = lean::cnstr_get(x_1, 0);
lean::inc(x_1500);
lean::dec(x_1);
x_1503 = lean::cnstr_get(x_1500, 2);
lean::inc(x_1503);
lean::dec(x_1500);
x_1506 = l_lean_file__map_to__position(x_1503, x_1497);
x_1507 = lean::box(0);
x_1508 = lean::cnstr_get(x_1506, 1);
lean::inc(x_1508);
x_1510 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1510);
x_1512 = l_lean_kvmap_set__nat(x_1507, x_1510, x_1508);
x_1513 = lean::cnstr_get(x_1506, 0);
lean::inc(x_1513);
lean::dec(x_1506);
x_1516 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1516);
x_1518 = l_lean_kvmap_set__nat(x_1512, x_1516, x_1513);
x_1519 = l_lean_elaborator_to__pexpr___main___closed__40;
lean::inc(x_1519);
x_1521 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_1521, 0, x_1518);
lean::cnstr_set(x_1521, 1, x_1519);
x_1522 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1522, 0, x_1521);
lean::cnstr_set(x_1522, 1, x_2);
x_1523 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1523, 0, x_1522);
return x_1523;
}
}
else
{
obj* x_1527; obj* x_1529; obj* x_1530; 
lean::dec(x_24);
lean::dec(x_1);
lean::dec(x_0);
x_1527 = l_lean_elaborator_to__pexpr___main___closed__40;
lean::inc(x_1527);
x_1529 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1529, 0, x_1527);
lean::cnstr_set(x_1529, 1, x_2);
x_1530 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1530, 0, x_1529);
return x_1530;
}
}
}
else
{
obj* x_1534; obj* x_1535; obj* x_1538; obj* x_1539; obj* x_1542; obj* x_1543; obj* x_1545; obj* x_1547; 
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_38);
x_1534 = l_lean_parser_term_anonymous__constructor_has__view;
x_1535 = lean::cnstr_get(x_1534, 0);
lean::inc(x_1535);
lean::inc(x_0);
x_1538 = lean::apply_1(x_1535, x_0);
x_1539 = lean::cnstr_get(x_1538, 1);
lean::inc(x_1539);
lean::dec(x_1538);
x_1542 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_1539);
x_1543 = l_lean_expander_get__opt__type___main___closed__1;
lean::inc(x_1543);
x_1545 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_1543, x_1542);
lean::inc(x_1);
x_1547 = l_lean_elaborator_to__pexpr___main(x_1545, x_1, x_2);
if (lean::obj_tag(x_1547) == 0)
{
obj* x_1551; obj* x_1553; obj* x_1554; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1551 = lean::cnstr_get(x_1547, 0);
lean::inc(x_1551);
if (lean::is_shared(x_1547)) {
 lean::dec(x_1547);
 x_1553 = lean::box(0);
} else {
 lean::cnstr_release(x_1547, 0);
 x_1553 = x_1547;
}
if (lean::is_scalar(x_1553)) {
 x_1554 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1554 = x_1553;
}
lean::cnstr_set(x_1554, 0, x_1551);
return x_1554;
}
else
{
obj* x_1555; obj* x_1558; obj* x_1560; obj* x_1562; obj* x_1563; obj* x_1565; obj* x_1566; 
x_1555 = lean::cnstr_get(x_1547, 0);
lean::inc(x_1555);
lean::dec(x_1547);
x_1558 = lean::cnstr_get(x_1555, 0);
lean::inc(x_1558);
x_1560 = lean::cnstr_get(x_1555, 1);
lean::inc(x_1560);
if (lean::is_shared(x_1555)) {
 lean::dec(x_1555);
 x_1562 = lean::box(0);
} else {
 lean::cnstr_release(x_1555, 0);
 lean::cnstr_release(x_1555, 1);
 x_1562 = x_1555;
}
x_1563 = l_lean_elaborator_to__pexpr___main___closed__41;
lean::inc(x_1563);
x_1565 = l_lean_elaborator_expr_mk__annotation(x_1563, x_1558);
if (lean::is_scalar(x_1562)) {
 x_1566 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1566 = x_1562;
}
lean::cnstr_set(x_1566, 0, x_1565);
lean::cnstr_set(x_1566, 1, x_1560);
x_16 = x_1566;
goto lbl_17;
}
}
}
else
{
obj* x_1570; obj* x_1571; obj* x_1574; obj* x_1575; obj* x_1576; obj* x_1578; obj* x_1580; 
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_35);
x_1570 = l_lean_parser_term_sort__app_has__view;
x_1571 = lean::cnstr_get(x_1570, 0);
lean::inc(x_1571);
lean::inc(x_0);
x_1574 = lean::apply_1(x_1571, x_0);
x_1575 = l_lean_parser_term_sort_has__view;
x_1576 = lean::cnstr_get(x_1575, 0);
lean::inc(x_1576);
x_1578 = lean::cnstr_get(x_1574, 0);
lean::inc(x_1578);
x_1580 = lean::apply_1(x_1576, x_1578);
if (lean::obj_tag(x_1580) == 0)
{
obj* x_1582; obj* x_1586; 
lean::dec(x_1580);
x_1582 = lean::cnstr_get(x_1574, 1);
lean::inc(x_1582);
lean::dec(x_1574);
lean::inc(x_1);
x_1586 = l_lean_elaborator_to__level___main(x_1582, x_1, x_2);
if (lean::obj_tag(x_1586) == 0)
{
obj* x_1590; obj* x_1592; obj* x_1593; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1590 = lean::cnstr_get(x_1586, 0);
lean::inc(x_1590);
if (lean::is_shared(x_1586)) {
 lean::dec(x_1586);
 x_1592 = lean::box(0);
} else {
 lean::cnstr_release(x_1586, 0);
 x_1592 = x_1586;
}
if (lean::is_scalar(x_1592)) {
 x_1593 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1593 = x_1592;
}
lean::cnstr_set(x_1593, 0, x_1590);
return x_1593;
}
else
{
obj* x_1594; obj* x_1597; obj* x_1599; obj* x_1601; obj* x_1602; obj* x_1603; 
x_1594 = lean::cnstr_get(x_1586, 0);
lean::inc(x_1594);
lean::dec(x_1586);
x_1597 = lean::cnstr_get(x_1594, 0);
lean::inc(x_1597);
x_1599 = lean::cnstr_get(x_1594, 1);
lean::inc(x_1599);
if (lean::is_shared(x_1594)) {
 lean::dec(x_1594);
 x_1601 = lean::box(0);
} else {
 lean::cnstr_release(x_1594, 0);
 lean::cnstr_release(x_1594, 1);
 x_1601 = x_1594;
}
x_1602 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1602, 0, x_1597);
if (lean::is_scalar(x_1601)) {
 x_1603 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1603 = x_1601;
}
lean::cnstr_set(x_1603, 0, x_1602);
lean::cnstr_set(x_1603, 1, x_1599);
x_16 = x_1603;
goto lbl_17;
}
}
else
{
obj* x_1605; obj* x_1609; 
lean::dec(x_1580);
x_1605 = lean::cnstr_get(x_1574, 1);
lean::inc(x_1605);
lean::dec(x_1574);
lean::inc(x_1);
x_1609 = l_lean_elaborator_to__level___main(x_1605, x_1, x_2);
if (lean::obj_tag(x_1609) == 0)
{
obj* x_1613; obj* x_1615; obj* x_1616; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1613 = lean::cnstr_get(x_1609, 0);
lean::inc(x_1613);
if (lean::is_shared(x_1609)) {
 lean::dec(x_1609);
 x_1615 = lean::box(0);
} else {
 lean::cnstr_release(x_1609, 0);
 x_1615 = x_1609;
}
if (lean::is_scalar(x_1615)) {
 x_1616 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1616 = x_1615;
}
lean::cnstr_set(x_1616, 0, x_1613);
return x_1616;
}
else
{
obj* x_1617; obj* x_1620; obj* x_1622; obj* x_1624; obj* x_1625; obj* x_1626; obj* x_1627; 
x_1617 = lean::cnstr_get(x_1609, 0);
lean::inc(x_1617);
lean::dec(x_1609);
x_1620 = lean::cnstr_get(x_1617, 0);
lean::inc(x_1620);
x_1622 = lean::cnstr_get(x_1617, 1);
lean::inc(x_1622);
if (lean::is_shared(x_1617)) {
 lean::dec(x_1617);
 x_1624 = lean::box(0);
} else {
 lean::cnstr_release(x_1617, 0);
 lean::cnstr_release(x_1617, 1);
 x_1624 = x_1617;
}
x_1625 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1625, 0, x_1620);
x_1626 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1626, 0, x_1625);
if (lean::is_scalar(x_1624)) {
 x_1627 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1627 = x_1624;
}
lean::cnstr_set(x_1627, 0, x_1626);
lean::cnstr_set(x_1627, 1, x_1622);
x_16 = x_1627;
goto lbl_17;
}
}
}
}
else
{
obj* x_1631; obj* x_1632; obj* x_1635; 
lean::dec(x_11);
lean::dec(x_32);
lean::dec(x_9);
x_1631 = l_lean_parser_term_sort_has__view;
x_1632 = lean::cnstr_get(x_1631, 0);
lean::inc(x_1632);
lean::inc(x_0);
x_1635 = lean::apply_1(x_1632, x_0);
if (lean::obj_tag(x_1635) == 0)
{
lean::dec(x_1635);
if (lean::obj_tag(x_24) == 0)
{
obj* x_1638; 
lean::dec(x_24);
x_1638 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1638) == 0)
{
obj* x_1641; obj* x_1643; obj* x_1644; 
lean::dec(x_1);
lean::dec(x_1638);
x_1641 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_1641);
x_1643 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1643, 0, x_1641);
lean::cnstr_set(x_1643, 1, x_2);
x_1644 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1644, 0, x_1643);
return x_1644;
}
else
{
obj* x_1645; obj* x_1648; obj* x_1651; obj* x_1654; obj* x_1655; obj* x_1656; obj* x_1658; obj* x_1660; obj* x_1661; obj* x_1664; obj* x_1666; obj* x_1667; obj* x_1669; obj* x_1670; obj* x_1671; 
x_1645 = lean::cnstr_get(x_1638, 0);
lean::inc(x_1645);
lean::dec(x_1638);
x_1648 = lean::cnstr_get(x_1, 0);
lean::inc(x_1648);
lean::dec(x_1);
x_1651 = lean::cnstr_get(x_1648, 2);
lean::inc(x_1651);
lean::dec(x_1648);
x_1654 = l_lean_file__map_to__position(x_1651, x_1645);
x_1655 = lean::box(0);
x_1656 = lean::cnstr_get(x_1654, 1);
lean::inc(x_1656);
x_1658 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1658);
x_1660 = l_lean_kvmap_set__nat(x_1655, x_1658, x_1656);
x_1661 = lean::cnstr_get(x_1654, 0);
lean::inc(x_1661);
lean::dec(x_1654);
x_1664 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1664);
x_1666 = l_lean_kvmap_set__nat(x_1660, x_1664, x_1661);
x_1667 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_1667);
x_1669 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_1669, 0, x_1666);
lean::cnstr_set(x_1669, 1, x_1667);
x_1670 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1670, 0, x_1669);
lean::cnstr_set(x_1670, 1, x_2);
x_1671 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1671, 0, x_1670);
return x_1671;
}
}
else
{
obj* x_1675; obj* x_1677; obj* x_1678; 
lean::dec(x_24);
lean::dec(x_1);
lean::dec(x_0);
x_1675 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_1675);
x_1677 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1677, 0, x_1675);
lean::cnstr_set(x_1677, 1, x_2);
x_1678 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1678, 0, x_1677);
return x_1678;
}
}
else
{
lean::dec(x_1635);
if (lean::obj_tag(x_24) == 0)
{
obj* x_1681; 
lean::dec(x_24);
x_1681 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1681) == 0)
{
obj* x_1684; obj* x_1686; obj* x_1687; 
lean::dec(x_1);
lean::dec(x_1681);
x_1684 = l_lean_elaborator_to__pexpr___main___closed__43;
lean::inc(x_1684);
x_1686 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1686, 0, x_1684);
lean::cnstr_set(x_1686, 1, x_2);
x_1687 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1687, 0, x_1686);
return x_1687;
}
else
{
obj* x_1688; obj* x_1691; obj* x_1694; obj* x_1697; obj* x_1698; obj* x_1699; obj* x_1701; obj* x_1703; obj* x_1704; obj* x_1707; obj* x_1709; obj* x_1710; obj* x_1712; obj* x_1713; obj* x_1714; 
x_1688 = lean::cnstr_get(x_1681, 0);
lean::inc(x_1688);
lean::dec(x_1681);
x_1691 = lean::cnstr_get(x_1, 0);
lean::inc(x_1691);
lean::dec(x_1);
x_1694 = lean::cnstr_get(x_1691, 2);
lean::inc(x_1694);
lean::dec(x_1691);
x_1697 = l_lean_file__map_to__position(x_1694, x_1688);
x_1698 = lean::box(0);
x_1699 = lean::cnstr_get(x_1697, 1);
lean::inc(x_1699);
x_1701 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_1701);
x_1703 = l_lean_kvmap_set__nat(x_1698, x_1701, x_1699);
x_1704 = lean::cnstr_get(x_1697, 0);
lean::inc(x_1704);
lean::dec(x_1697);
x_1707 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_1707);
x_1709 = l_lean_kvmap_set__nat(x_1703, x_1707, x_1704);
x_1710 = l_lean_elaborator_to__pexpr___main___closed__43;
lean::inc(x_1710);
x_1712 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_1712, 0, x_1709);
lean::cnstr_set(x_1712, 1, x_1710);
x_1713 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1713, 0, x_1712);
lean::cnstr_set(x_1713, 1, x_2);
x_1714 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1714, 0, x_1713);
return x_1714;
}
}
else
{
obj* x_1718; obj* x_1720; obj* x_1721; 
lean::dec(x_24);
lean::dec(x_1);
lean::dec(x_0);
x_1718 = l_lean_elaborator_to__pexpr___main___closed__43;
lean::inc(x_1718);
x_1720 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1720, 0, x_1718);
lean::cnstr_set(x_1720, 1, x_2);
x_1721 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1721, 0, x_1720);
return x_1721;
}
}
}
}
else
{
obj* x_1725; obj* x_1726; obj* x_1729; obj* x_1730; 
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_29);
x_1725 = l_lean_parser_term_pi_has__view;
x_1726 = lean::cnstr_get(x_1725, 0);
lean::inc(x_1726);
lean::inc(x_0);
x_1729 = lean::apply_1(x_1726, x_0);
x_1730 = lean::cnstr_get(x_1729, 1);
lean::inc(x_1730);
if (lean::obj_tag(x_1730) == 0)
{
obj* x_1734; obj* x_1738; 
lean::dec(x_1729);
lean::dec(x_1730);
x_1734 = l_lean_elaborator_to__pexpr___main___closed__44;
lean::inc(x_1);
lean::inc(x_1734);
lean::inc(x_0);
x_1738 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1734, x_1, x_2);
if (lean::obj_tag(x_1738) == 0)
{
obj* x_1742; obj* x_1744; obj* x_1745; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1742 = lean::cnstr_get(x_1738, 0);
lean::inc(x_1742);
if (lean::is_shared(x_1738)) {
 lean::dec(x_1738);
 x_1744 = lean::box(0);
} else {
 lean::cnstr_release(x_1738, 0);
 x_1744 = x_1738;
}
if (lean::is_scalar(x_1744)) {
 x_1745 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1745 = x_1744;
}
lean::cnstr_set(x_1745, 0, x_1742);
return x_1745;
}
else
{
obj* x_1746; 
x_1746 = lean::cnstr_get(x_1738, 0);
lean::inc(x_1746);
lean::dec(x_1738);
x_16 = x_1746;
goto lbl_17;
}
}
else
{
obj* x_1749; obj* x_1752; obj* x_1753; obj* x_1755; obj* x_1757; obj* x_1758; obj* x_1760; obj* x_1764; 
x_1749 = lean::cnstr_get(x_1730, 0);
lean::inc(x_1749);
lean::dec(x_1730);
x_1752 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1749);
x_1753 = lean::cnstr_get(x_1752, 0);
lean::inc(x_1753);
x_1755 = lean::cnstr_get(x_1752, 1);
lean::inc(x_1755);
if (lean::is_shared(x_1752)) {
 lean::dec(x_1752);
 x_1757 = lean::box(0);
} else {
 lean::cnstr_release(x_1752, 0);
 lean::cnstr_release(x_1752, 1);
 x_1757 = x_1752;
}
x_1758 = lean::cnstr_get(x_1755, 0);
lean::inc(x_1758);
x_1760 = lean::cnstr_get(x_1755, 1);
lean::inc(x_1760);
lean::dec(x_1755);
lean::inc(x_1);
x_1764 = l_lean_elaborator_to__pexpr___main(x_1760, x_1, x_2);
if (lean::obj_tag(x_1764) == 0)
{
obj* x_1772; obj* x_1774; obj* x_1775; 
lean::dec(x_1729);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1753);
lean::dec(x_1758);
lean::dec(x_1757);
x_1772 = lean::cnstr_get(x_1764, 0);
lean::inc(x_1772);
if (lean::is_shared(x_1764)) {
 lean::dec(x_1764);
 x_1774 = lean::box(0);
} else {
 lean::cnstr_release(x_1764, 0);
 x_1774 = x_1764;
}
if (lean::is_scalar(x_1774)) {
 x_1775 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1775 = x_1774;
}
lean::cnstr_set(x_1775, 0, x_1772);
return x_1775;
}
else
{
obj* x_1776; obj* x_1778; obj* x_1779; obj* x_1781; obj* x_1784; obj* x_1788; 
x_1776 = lean::cnstr_get(x_1764, 0);
lean::inc(x_1776);
if (lean::is_shared(x_1764)) {
 lean::dec(x_1764);
 x_1778 = lean::box(0);
} else {
 lean::cnstr_release(x_1764, 0);
 x_1778 = x_1764;
}
x_1779 = lean::cnstr_get(x_1776, 0);
lean::inc(x_1779);
x_1781 = lean::cnstr_get(x_1776, 1);
lean::inc(x_1781);
lean::dec(x_1776);
x_1784 = lean::cnstr_get(x_1729, 3);
lean::inc(x_1784);
lean::dec(x_1729);
lean::inc(x_1);
x_1788 = l_lean_elaborator_to__pexpr___main(x_1784, x_1, x_1781);
if (lean::obj_tag(x_1788) == 0)
{
obj* x_1796; obj* x_1799; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1753);
lean::dec(x_1779);
lean::dec(x_1758);
lean::dec(x_1757);
x_1796 = lean::cnstr_get(x_1788, 0);
lean::inc(x_1796);
lean::dec(x_1788);
if (lean::is_scalar(x_1778)) {
 x_1799 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1799 = x_1778;
}
lean::cnstr_set(x_1799, 0, x_1796);
return x_1799;
}
else
{
obj* x_1801; obj* x_1804; obj* x_1806; obj* x_1809; obj* x_1810; unsigned char x_1811; obj* x_1813; obj* x_1814; 
lean::dec(x_1778);
x_1801 = lean::cnstr_get(x_1788, 0);
lean::inc(x_1801);
lean::dec(x_1788);
x_1804 = lean::cnstr_get(x_1801, 0);
lean::inc(x_1804);
x_1806 = lean::cnstr_get(x_1801, 1);
lean::inc(x_1806);
lean::dec(x_1801);
x_1809 = l_lean_elaborator_mangle__ident(x_1758);
x_1810 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_1810, 0, x_1809);
lean::cnstr_set(x_1810, 1, x_1779);
lean::cnstr_set(x_1810, 2, x_1804);
x_1811 = lean::unbox(x_1753);
lean::dec(x_1753);
lean::cnstr_set_scalar(x_1810, sizeof(void*)*3, x_1811);
x_1813 = x_1810;
if (lean::is_scalar(x_1757)) {
 x_1814 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1814 = x_1757;
}
lean::cnstr_set(x_1814, 0, x_1813);
lean::cnstr_set(x_1814, 1, x_1806);
x_16 = x_1814;
goto lbl_17;
}
}
}
}
}
else
{
obj* x_1818; obj* x_1819; obj* x_1822; obj* x_1823; 
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_26);
x_1818 = l_lean_parser_term_lambda_has__view;
x_1819 = lean::cnstr_get(x_1818, 0);
lean::inc(x_1819);
lean::inc(x_0);
x_1822 = lean::apply_1(x_1819, x_0);
x_1823 = lean::cnstr_get(x_1822, 1);
lean::inc(x_1823);
if (lean::obj_tag(x_1823) == 0)
{
obj* x_1827; obj* x_1831; 
lean::dec(x_1822);
lean::dec(x_1823);
x_1827 = l_lean_elaborator_to__pexpr___main___closed__45;
lean::inc(x_1);
lean::inc(x_1827);
lean::inc(x_0);
x_1831 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_1827, x_1, x_2);
if (lean::obj_tag(x_1831) == 0)
{
obj* x_1835; obj* x_1837; obj* x_1838; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1835 = lean::cnstr_get(x_1831, 0);
lean::inc(x_1835);
if (lean::is_shared(x_1831)) {
 lean::dec(x_1831);
 x_1837 = lean::box(0);
} else {
 lean::cnstr_release(x_1831, 0);
 x_1837 = x_1831;
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
obj* x_1839; 
x_1839 = lean::cnstr_get(x_1831, 0);
lean::inc(x_1839);
lean::dec(x_1831);
x_16 = x_1839;
goto lbl_17;
}
}
else
{
obj* x_1842; obj* x_1845; obj* x_1846; obj* x_1848; obj* x_1850; obj* x_1851; obj* x_1853; obj* x_1857; 
x_1842 = lean::cnstr_get(x_1823, 0);
lean::inc(x_1842);
lean::dec(x_1823);
x_1845 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_1842);
x_1846 = lean::cnstr_get(x_1845, 0);
lean::inc(x_1846);
x_1848 = lean::cnstr_get(x_1845, 1);
lean::inc(x_1848);
if (lean::is_shared(x_1845)) {
 lean::dec(x_1845);
 x_1850 = lean::box(0);
} else {
 lean::cnstr_release(x_1845, 0);
 lean::cnstr_release(x_1845, 1);
 x_1850 = x_1845;
}
x_1851 = lean::cnstr_get(x_1848, 0);
lean::inc(x_1851);
x_1853 = lean::cnstr_get(x_1848, 1);
lean::inc(x_1853);
lean::dec(x_1848);
lean::inc(x_1);
x_1857 = l_lean_elaborator_to__pexpr___main(x_1853, x_1, x_2);
if (lean::obj_tag(x_1857) == 0)
{
obj* x_1865; obj* x_1867; obj* x_1868; 
lean::dec(x_1846);
lean::dec(x_1850);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1851);
lean::dec(x_1822);
x_1865 = lean::cnstr_get(x_1857, 0);
lean::inc(x_1865);
if (lean::is_shared(x_1857)) {
 lean::dec(x_1857);
 x_1867 = lean::box(0);
} else {
 lean::cnstr_release(x_1857, 0);
 x_1867 = x_1857;
}
if (lean::is_scalar(x_1867)) {
 x_1868 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1868 = x_1867;
}
lean::cnstr_set(x_1868, 0, x_1865);
return x_1868;
}
else
{
obj* x_1869; obj* x_1871; obj* x_1872; obj* x_1874; obj* x_1877; obj* x_1881; 
x_1869 = lean::cnstr_get(x_1857, 0);
lean::inc(x_1869);
if (lean::is_shared(x_1857)) {
 lean::dec(x_1857);
 x_1871 = lean::box(0);
} else {
 lean::cnstr_release(x_1857, 0);
 x_1871 = x_1857;
}
x_1872 = lean::cnstr_get(x_1869, 0);
lean::inc(x_1872);
x_1874 = lean::cnstr_get(x_1869, 1);
lean::inc(x_1874);
lean::dec(x_1869);
x_1877 = lean::cnstr_get(x_1822, 3);
lean::inc(x_1877);
lean::dec(x_1822);
lean::inc(x_1);
x_1881 = l_lean_elaborator_to__pexpr___main(x_1877, x_1, x_1874);
if (lean::obj_tag(x_1881) == 0)
{
obj* x_1889; obj* x_1892; 
lean::dec(x_1846);
lean::dec(x_1850);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1851);
lean::dec(x_1872);
x_1889 = lean::cnstr_get(x_1881, 0);
lean::inc(x_1889);
lean::dec(x_1881);
if (lean::is_scalar(x_1871)) {
 x_1892 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1892 = x_1871;
}
lean::cnstr_set(x_1892, 0, x_1889);
return x_1892;
}
else
{
obj* x_1894; obj* x_1897; obj* x_1899; obj* x_1902; obj* x_1903; unsigned char x_1904; obj* x_1906; obj* x_1907; 
lean::dec(x_1871);
x_1894 = lean::cnstr_get(x_1881, 0);
lean::inc(x_1894);
lean::dec(x_1881);
x_1897 = lean::cnstr_get(x_1894, 0);
lean::inc(x_1897);
x_1899 = lean::cnstr_get(x_1894, 1);
lean::inc(x_1899);
lean::dec(x_1894);
x_1902 = l_lean_elaborator_mangle__ident(x_1851);
x_1903 = lean::alloc_cnstr(6, 3, 1);
lean::cnstr_set(x_1903, 0, x_1902);
lean::cnstr_set(x_1903, 1, x_1872);
lean::cnstr_set(x_1903, 2, x_1897);
x_1904 = lean::unbox(x_1846);
lean::dec(x_1846);
lean::cnstr_set_scalar(x_1903, sizeof(void*)*3, x_1904);
x_1906 = x_1903;
if (lean::is_scalar(x_1850)) {
 x_1907 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1907 = x_1850;
}
lean::cnstr_set(x_1907, 0, x_1906);
lean::cnstr_set(x_1907, 1, x_1899);
x_16 = x_1907;
goto lbl_17;
}
}
}
}
}
else
{
obj* x_1910; obj* x_1911; obj* x_1914; obj* x_1915; obj* x_1918; 
lean::dec(x_24);
lean::dec(x_11);
x_1910 = l_lean_parser_term_app_has__view;
x_1911 = lean::cnstr_get(x_1910, 0);
lean::inc(x_1911);
lean::inc(x_0);
x_1914 = lean::apply_1(x_1911, x_0);
x_1915 = lean::cnstr_get(x_1914, 0);
lean::inc(x_1915);
lean::inc(x_1);
x_1918 = l_lean_elaborator_to__pexpr___main(x_1915, x_1, x_2);
if (lean::obj_tag(x_1918) == 0)
{
obj* x_1923; obj* x_1925; obj* x_1926; 
lean::dec(x_1914);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_1923 = lean::cnstr_get(x_1918, 0);
lean::inc(x_1923);
if (lean::is_shared(x_1918)) {
 lean::dec(x_1918);
 x_1925 = lean::box(0);
} else {
 lean::cnstr_release(x_1918, 0);
 x_1925 = x_1918;
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
obj* x_1927; obj* x_1929; obj* x_1930; obj* x_1932; obj* x_1934; obj* x_1935; obj* x_1939; 
x_1927 = lean::cnstr_get(x_1918, 0);
lean::inc(x_1927);
if (lean::is_shared(x_1918)) {
 lean::dec(x_1918);
 x_1929 = lean::box(0);
} else {
 lean::cnstr_release(x_1918, 0);
 x_1929 = x_1918;
}
x_1930 = lean::cnstr_get(x_1927, 0);
lean::inc(x_1930);
x_1932 = lean::cnstr_get(x_1927, 1);
lean::inc(x_1932);
if (lean::is_shared(x_1927)) {
 lean::dec(x_1927);
 x_1934 = lean::box(0);
} else {
 lean::cnstr_release(x_1927, 0);
 lean::cnstr_release(x_1927, 1);
 x_1934 = x_1927;
}
x_1935 = lean::cnstr_get(x_1914, 1);
lean::inc(x_1935);
lean::dec(x_1914);
lean::inc(x_1);
x_1939 = l_lean_elaborator_to__pexpr___main(x_1935, x_1, x_1932);
if (lean::obj_tag(x_1939) == 0)
{
obj* x_1945; obj* x_1948; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1930);
lean::dec(x_1934);
x_1945 = lean::cnstr_get(x_1939, 0);
lean::inc(x_1945);
lean::dec(x_1939);
if (lean::is_scalar(x_1929)) {
 x_1948 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1948 = x_1929;
}
lean::cnstr_set(x_1948, 0, x_1945);
return x_1948;
}
else
{
obj* x_1950; obj* x_1953; obj* x_1955; obj* x_1958; obj* x_1959; 
lean::dec(x_1929);
x_1950 = lean::cnstr_get(x_1939, 0);
lean::inc(x_1950);
lean::dec(x_1939);
x_1953 = lean::cnstr_get(x_1950, 0);
lean::inc(x_1953);
x_1955 = lean::cnstr_get(x_1950, 1);
lean::inc(x_1955);
lean::dec(x_1950);
x_1958 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_1958, 0, x_1930);
lean::cnstr_set(x_1958, 1, x_1953);
if (lean::is_scalar(x_1934)) {
 x_1959 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1959 = x_1934;
}
lean::cnstr_set(x_1959, 0, x_1958);
lean::cnstr_set(x_1959, 1, x_1955);
x_16 = x_1959;
goto lbl_17;
}
}
}
}
else
{
obj* x_1962; obj* x_1963; obj* x_1966; obj* x_1967; obj* x_1969; 
lean::dec(x_11);
lean::dec(x_21);
x_1962 = l_lean_parser_ident__univs_has__view;
x_1963 = lean::cnstr_get(x_1962, 0);
lean::inc(x_1963);
lean::inc(x_0);
x_1966 = lean::apply_1(x_1963, x_0);
x_1967 = lean::cnstr_get(x_1966, 0);
lean::inc(x_1967);
x_1969 = lean::cnstr_get(x_1966, 1);
lean::inc(x_1969);
lean::dec(x_1966);
if (lean::obj_tag(x_1969) == 0)
{
obj* x_1974; obj* x_1975; obj* x_1977; obj* x_1978; obj* x_1981; obj* x_1982; obj* x_1983; obj* x_1985; obj* x_1986; obj* x_1987; obj* x_1988; 
lean::dec(x_1969);
lean::inc(x_1967);
x_1974 = l_lean_elaborator_mangle__ident(x_1967);
x_1975 = lean::box(0);
lean::inc(x_1975);
x_1977 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_1977, 0, x_1974);
lean::cnstr_set(x_1977, 1, x_1975);
x_1978 = lean::cnstr_get(x_1967, 3);
lean::inc(x_1978);
lean::dec(x_1967);
x_1981 = lean::mk_nat_obj(0u);
x_1982 = l_list_enum__from___main___rarg(x_1981, x_1978);
x_1983 = l_lean_elaborator_to__pexpr___main___closed__46;
lean::inc(x_1983);
x_1985 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(x_1983, x_1982);
x_1986 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_1986, 0, x_1985);
lean::cnstr_set(x_1986, 1, x_1977);
x_1987 = l_lean_elaborator_to__pexpr___main___closed__2;
x_1988 = lean::name_dec_eq(x_9, x_1987);
lean::dec(x_9);
if (lean::obj_tag(x_1988) == 0)
{
obj* x_1991; 
lean::dec(x_1988);
x_1991 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_1991) == 0)
{
obj* x_1995; obj* x_1996; 
lean::dec(x_1);
lean::dec(x_1975);
lean::dec(x_1991);
x_1995 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1995, 0, x_1986);
lean::cnstr_set(x_1995, 1, x_2);
x_1996 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1996, 0, x_1995);
return x_1996;
}
else
{
obj* x_1997; obj* x_2000; obj* x_2003; obj* x_2006; obj* x_2007; obj* x_2009; obj* x_2011; obj* x_2012; obj* x_2015; obj* x_2017; obj* x_2018; obj* x_2019; obj* x_2020; 
x_1997 = lean::cnstr_get(x_1991, 0);
lean::inc(x_1997);
lean::dec(x_1991);
x_2000 = lean::cnstr_get(x_1, 0);
lean::inc(x_2000);
lean::dec(x_1);
x_2003 = lean::cnstr_get(x_2000, 2);
lean::inc(x_2003);
lean::dec(x_2000);
x_2006 = l_lean_file__map_to__position(x_2003, x_1997);
x_2007 = lean::cnstr_get(x_2006, 1);
lean::inc(x_2007);
x_2009 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_2009);
x_2011 = l_lean_kvmap_set__nat(x_1975, x_2009, x_2007);
x_2012 = lean::cnstr_get(x_2006, 0);
lean::inc(x_2012);
lean::dec(x_2006);
x_2015 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_2015);
x_2017 = l_lean_kvmap_set__nat(x_2011, x_2015, x_2012);
x_2018 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_2018, 0, x_2017);
lean::cnstr_set(x_2018, 1, x_1986);
x_2019 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2019, 0, x_2018);
lean::cnstr_set(x_2019, 1, x_2);
x_2020 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2020, 0, x_2019);
return x_2020;
}
}
else
{
obj* x_2025; obj* x_2026; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1975);
lean::dec(x_1988);
x_2025 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2025, 0, x_1986);
lean::cnstr_set(x_2025, 1, x_2);
x_2026 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2026, 0, x_2025);
return x_2026;
}
}
else
{
obj* x_2027; obj* x_2030; obj* x_2034; 
x_2027 = lean::cnstr_get(x_1969, 0);
lean::inc(x_2027);
lean::dec(x_1969);
x_2030 = lean::cnstr_get(x_2027, 1);
lean::inc(x_2030);
lean::dec(x_2027);
lean::inc(x_1);
x_2034 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_2030, x_1, x_2);
if (lean::obj_tag(x_2034) == 0)
{
obj* x_2039; obj* x_2041; obj* x_2042; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_1967);
x_2039 = lean::cnstr_get(x_2034, 0);
lean::inc(x_2039);
if (lean::is_shared(x_2034)) {
 lean::dec(x_2034);
 x_2041 = lean::box(0);
} else {
 lean::cnstr_release(x_2034, 0);
 x_2041 = x_2034;
}
if (lean::is_scalar(x_2041)) {
 x_2042 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2042 = x_2041;
}
lean::cnstr_set(x_2042, 0, x_2039);
return x_2042;
}
else
{
obj* x_2043; obj* x_2046; obj* x_2048; obj* x_2050; obj* x_2052; obj* x_2053; obj* x_2054; obj* x_2057; obj* x_2058; obj* x_2059; obj* x_2061; obj* x_2062; obj* x_2063; 
x_2043 = lean::cnstr_get(x_2034, 0);
lean::inc(x_2043);
lean::dec(x_2034);
x_2046 = lean::cnstr_get(x_2043, 0);
lean::inc(x_2046);
x_2048 = lean::cnstr_get(x_2043, 1);
lean::inc(x_2048);
if (lean::is_shared(x_2043)) {
 lean::dec(x_2043);
 x_2050 = lean::box(0);
} else {
 lean::cnstr_release(x_2043, 0);
 lean::cnstr_release(x_2043, 1);
 x_2050 = x_2043;
}
lean::inc(x_1967);
x_2052 = l_lean_elaborator_mangle__ident(x_1967);
x_2053 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_2053, 0, x_2052);
lean::cnstr_set(x_2053, 1, x_2046);
x_2054 = lean::cnstr_get(x_1967, 3);
lean::inc(x_2054);
lean::dec(x_1967);
x_2057 = lean::mk_nat_obj(0u);
x_2058 = l_list_enum__from___main___rarg(x_2057, x_2054);
x_2059 = l_lean_elaborator_to__pexpr___main___closed__46;
lean::inc(x_2059);
x_2061 = l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__24(x_2059, x_2058);
x_2062 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_2062, 0, x_2061);
lean::cnstr_set(x_2062, 1, x_2053);
if (lean::is_scalar(x_2050)) {
 x_2063 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2063 = x_2050;
}
lean::cnstr_set(x_2063, 0, x_2062);
lean::cnstr_set(x_2063, 1, x_2048);
x_16 = x_2063;
goto lbl_17;
}
}
}
lbl_15:
{
if (lean::obj_tag(x_14) == 0)
{
obj* x_2067; obj* x_2069; obj* x_2070; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_2067 = lean::cnstr_get(x_14, 0);
lean::inc(x_2067);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_2069 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_2069 = x_14;
}
if (lean::is_scalar(x_2069)) {
 x_2070 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2070 = x_2069;
}
lean::cnstr_set(x_2070, 0, x_2067);
return x_2070;
}
else
{
obj* x_2071; obj* x_2073; obj* x_2074; obj* x_2076; obj* x_2078; obj* x_2079; obj* x_2080; 
x_2071 = lean::cnstr_get(x_14, 0);
lean::inc(x_2071);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_2073 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_2073 = x_14;
}
x_2074 = lean::cnstr_get(x_2071, 0);
lean::inc(x_2074);
x_2076 = lean::cnstr_get(x_2071, 1);
lean::inc(x_2076);
if (lean::is_shared(x_2071)) {
 lean::dec(x_2071);
 x_2078 = lean::box(0);
} else {
 lean::cnstr_release(x_2071, 0);
 lean::cnstr_release(x_2071, 1);
 x_2078 = x_2071;
}
x_2079 = l_lean_elaborator_to__pexpr___main___closed__2;
x_2080 = lean::name_dec_eq(x_9, x_2079);
lean::dec(x_9);
if (lean::obj_tag(x_2080) == 0)
{
obj* x_2083; 
lean::dec(x_2080);
x_2083 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_2083) == 0)
{
obj* x_2086; obj* x_2087; 
lean::dec(x_1);
lean::dec(x_2083);
if (lean::is_scalar(x_2078)) {
 x_2086 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2086 = x_2078;
}
lean::cnstr_set(x_2086, 0, x_2074);
lean::cnstr_set(x_2086, 1, x_2076);
if (lean::is_scalar(x_2073)) {
 x_2087 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2087 = x_2073;
}
lean::cnstr_set(x_2087, 0, x_2086);
return x_2087;
}
else
{
obj* x_2088; obj* x_2091; obj* x_2094; obj* x_2097; obj* x_2098; obj* x_2099; obj* x_2101; obj* x_2103; obj* x_2104; obj* x_2107; obj* x_2109; obj* x_2110; obj* x_2111; obj* x_2112; 
x_2088 = lean::cnstr_get(x_2083, 0);
lean::inc(x_2088);
lean::dec(x_2083);
x_2091 = lean::cnstr_get(x_1, 0);
lean::inc(x_2091);
lean::dec(x_1);
x_2094 = lean::cnstr_get(x_2091, 2);
lean::inc(x_2094);
lean::dec(x_2091);
x_2097 = l_lean_file__map_to__position(x_2094, x_2088);
x_2098 = lean::box(0);
x_2099 = lean::cnstr_get(x_2097, 1);
lean::inc(x_2099);
x_2101 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_2101);
x_2103 = l_lean_kvmap_set__nat(x_2098, x_2101, x_2099);
x_2104 = lean::cnstr_get(x_2097, 0);
lean::inc(x_2104);
lean::dec(x_2097);
x_2107 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_2107);
x_2109 = l_lean_kvmap_set__nat(x_2103, x_2107, x_2104);
x_2110 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_2110, 0, x_2109);
lean::cnstr_set(x_2110, 1, x_2074);
if (lean::is_scalar(x_2078)) {
 x_2111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2111 = x_2078;
}
lean::cnstr_set(x_2111, 0, x_2110);
lean::cnstr_set(x_2111, 1, x_2076);
if (lean::is_scalar(x_2073)) {
 x_2112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2112 = x_2073;
}
lean::cnstr_set(x_2112, 0, x_2111);
return x_2112;
}
}
else
{
obj* x_2116; obj* x_2117; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2080);
if (lean::is_scalar(x_2078)) {
 x_2116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2116 = x_2078;
}
lean::cnstr_set(x_2116, 0, x_2074);
lean::cnstr_set(x_2116, 1, x_2076);
if (lean::is_scalar(x_2073)) {
 x_2117 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2117 = x_2073;
}
lean::cnstr_set(x_2117, 0, x_2116);
return x_2117;
}
}
}
lbl_17:
{
obj* x_2118; obj* x_2120; obj* x_2122; obj* x_2123; obj* x_2124; 
x_2118 = lean::cnstr_get(x_16, 0);
lean::inc(x_2118);
x_2120 = lean::cnstr_get(x_16, 1);
lean::inc(x_2120);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_2122 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_2122 = x_16;
}
x_2123 = l_lean_elaborator_to__pexpr___main___closed__2;
x_2124 = lean::name_dec_eq(x_9, x_2123);
lean::dec(x_9);
if (lean::obj_tag(x_2124) == 0)
{
obj* x_2127; 
lean::dec(x_2124);
x_2127 = l_lean_parser_syntax_get__pos(x_0);
if (lean::obj_tag(x_2127) == 0)
{
obj* x_2130; obj* x_2131; 
lean::dec(x_1);
lean::dec(x_2127);
if (lean::is_scalar(x_2122)) {
 x_2130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2130 = x_2122;
}
lean::cnstr_set(x_2130, 0, x_2118);
lean::cnstr_set(x_2130, 1, x_2120);
x_2131 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2131, 0, x_2130);
return x_2131;
}
else
{
obj* x_2132; obj* x_2135; obj* x_2138; obj* x_2141; obj* x_2142; obj* x_2143; obj* x_2145; obj* x_2147; obj* x_2148; obj* x_2151; obj* x_2153; obj* x_2154; obj* x_2155; obj* x_2156; 
x_2132 = lean::cnstr_get(x_2127, 0);
lean::inc(x_2132);
lean::dec(x_2127);
x_2135 = lean::cnstr_get(x_1, 0);
lean::inc(x_2135);
lean::dec(x_1);
x_2138 = lean::cnstr_get(x_2135, 2);
lean::inc(x_2138);
lean::dec(x_2135);
x_2141 = l_lean_file__map_to__position(x_2138, x_2132);
x_2142 = lean::box(0);
x_2143 = lean::cnstr_get(x_2141, 1);
lean::inc(x_2143);
x_2145 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_2145);
x_2147 = l_lean_kvmap_set__nat(x_2142, x_2145, x_2143);
x_2148 = lean::cnstr_get(x_2141, 0);
lean::inc(x_2148);
lean::dec(x_2141);
x_2151 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_2151);
x_2153 = l_lean_kvmap_set__nat(x_2147, x_2151, x_2148);
x_2154 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_2154, 0, x_2153);
lean::cnstr_set(x_2154, 1, x_2118);
if (lean::is_scalar(x_2122)) {
 x_2155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2155 = x_2122;
}
lean::cnstr_set(x_2155, 0, x_2154);
lean::cnstr_set(x_2155, 1, x_2120);
x_2156 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2156, 0, x_2155);
return x_2156;
}
}
else
{
obj* x_2160; obj* x_2161; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2124);
if (lean::is_scalar(x_2122)) {
 x_2160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2160 = x_2122;
}
lean::cnstr_set(x_2160, 0, x_2118);
lean::cnstr_set(x_2160, 1, x_2120);
x_2161 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2161, 0, x_2160);
return x_2161;
}
}
lbl_19:
{
obj* x_2162; obj* x_2164; obj* x_2166; 
x_2162 = lean::cnstr_get(x_18, 0);
lean::inc(x_2162);
x_2164 = lean::cnstr_get(x_18, 1);
lean::inc(x_2164);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_2166 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 x_2166 = x_18;
}
if (lean::obj_tag(x_2162) == 0)
{
obj* x_2170; obj* x_2174; 
lean::dec(x_11);
lean::dec(x_2166);
lean::dec(x_2162);
x_2170 = l_lean_elaborator_to__pexpr___main___closed__5;
lean::inc(x_1);
lean::inc(x_2170);
lean::inc(x_0);
x_2174 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2170, x_1, x_2164);
if (lean::obj_tag(x_2174) == 0)
{
obj* x_2178; obj* x_2180; obj* x_2181; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_2178 = lean::cnstr_get(x_2174, 0);
lean::inc(x_2178);
if (lean::is_shared(x_2174)) {
 lean::dec(x_2174);
 x_2180 = lean::box(0);
} else {
 lean::cnstr_release(x_2174, 0);
 x_2180 = x_2174;
}
if (lean::is_scalar(x_2180)) {
 x_2181 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2181 = x_2180;
}
lean::cnstr_set(x_2181, 0, x_2178);
return x_2181;
}
else
{
obj* x_2182; 
x_2182 = lean::cnstr_get(x_2174, 0);
lean::inc(x_2182);
lean::dec(x_2174);
x_16 = x_2182;
goto lbl_17;
}
}
else
{
obj* x_2185; obj* x_2187; obj* x_2190; obj* x_2191; obj* x_2192; obj* x_2194; obj* x_2195; obj* x_2196; obj* x_2197; obj* x_2198; 
x_2185 = lean::cnstr_get(x_2162, 0);
lean::inc(x_2185);
x_2187 = lean::cnstr_get(x_2162, 1);
lean::inc(x_2187);
lean::dec(x_2162);
x_2190 = lean::box(0);
x_2191 = l_list_length___main___rarg(x_11);
x_2192 = l_lean_elaborator_to__pexpr___main___closed__6;
lean::inc(x_2192);
x_2194 = l_lean_kvmap_set__nat(x_2190, x_2192, x_2191);
x_2195 = l_list_reverse___rarg(x_2187);
x_2196 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(x_2185, x_2195);
x_2197 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_2197, 0, x_2194);
lean::cnstr_set(x_2197, 1, x_2196);
if (lean::is_scalar(x_2166)) {
 x_2198 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2198 = x_2166;
}
lean::cnstr_set(x_2198, 0, x_2197);
lean::cnstr_set(x_2198, 1, x_2164);
x_16 = x_2198;
goto lbl_17;
}
}
}
default:
{
obj* x_2199; 
x_2199 = lean::box(0);
x_3 = x_2199;
goto lbl_4;
}
}
lbl_4:
{
obj* x_2202; obj* x_2203; obj* x_2204; obj* x_2205; obj* x_2207; obj* x_2209; 
lean::dec(x_3);
lean::inc(x_0);
x_2202 = l_lean_parser_syntax_to__format___main(x_0);
x_2203 = lean::mk_nat_obj(80u);
x_2204 = l_lean_format_pretty(x_2202, x_2203);
x_2205 = l_lean_elaborator_to__pexpr___main___closed__1;
lean::inc(x_2205);
x_2207 = lean::string_append(x_2205, x_2204);
lean::dec(x_2204);
x_2209 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_2207, x_1, x_2);
return x_2209;
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
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("app");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("column");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("row");
x_2 = lean::name_mk_string(x_0, x_1);
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
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("ident_univs");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("lambda");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__9() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("pi");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__10() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("sort_app");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__11() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("anonymous_constructor");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__12() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("hole");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__13() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("have");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__14() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("show");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__15() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("let");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__16() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("projection");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__17() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("explicit");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__18() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("inaccessible");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__19() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("choice");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__20() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("struct_inst");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__21() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("term");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("match");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__22() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("to_pexpr: unexpected node: ");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__23() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("to_pexpr: unreachable");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__24() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("match");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__25() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("structure instance");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__26() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("catchall");
x_2 = lean::name_mk_string(x_0, x_1);
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
x_2 = lean::name_mk_string(x_0, x_1);
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
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("innaccessible");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__32() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@@");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__33() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("field_notation");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__34() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed let");
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__35() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__36() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__37() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("show");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__38() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("have");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__39() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_to__pexpr___main___lambda__2), 1, 0);
return x_0;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__40() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_lean_elaborator_dummy;
lean::inc(x_1);
x_3 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__41() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("anonymous_constructor");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__42() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_elaborator_to__pexpr___main___closed__43() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("annotation");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string("preresolved");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
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
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
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
x_9 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
lean::inc(x_1);
x_17 = l_lean_elaborator_to__pexpr___main(x_13, x_1, x_2);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_23 = x_17;
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
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_27 = x_17;
}
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_32 = x_25;
}
x_33 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(x_10, x_1, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_40; 
lean::dec(x_12);
lean::dec(x_28);
lean::dec(x_32);
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_27;
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_33, 0);
lean::inc(x_41);
lean::dec(x_33);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
lean::dec(x_41);
if (lean::is_scalar(x_12)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_12;
}
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_44);
if (lean::is_scalar(x_32)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_32;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
if (lean::is_scalar(x_27)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_27;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
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
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__3(x_5);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_16; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::inc(x_1);
x_16 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__2(x_13, x_1, x_2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_23 = x_16;
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
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_37; 
x_25 = lean::cnstr_get(x_16, 0);
lean::inc(x_25);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_27 = x_16;
}
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_32 = x_25;
}
x_33 = lean::cnstr_get(x_8, 2);
lean::inc(x_33);
lean::dec(x_8);
lean::inc(x_1);
x_37 = l_lean_elaborator_to__pexpr___main(x_33, x_1, x_30);
if (lean::obj_tag(x_37) == 0)
{
obj* x_43; obj* x_46; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_28);
lean::dec(x_32);
x_43 = lean::cnstr_get(x_37, 0);
lean::inc(x_43);
lean::dec(x_37);
if (lean::is_scalar(x_27)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_27;
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
x_55 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4(x_10, x_1, x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_61; obj* x_64; 
lean::dec(x_12);
lean::dec(x_50);
lean::dec(x_28);
lean::dec(x_32);
lean::dec(x_54);
x_61 = lean::cnstr_get(x_55, 0);
lean::inc(x_61);
lean::dec(x_55);
if (lean::is_scalar(x_27)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_27;
}
lean::cnstr_set(x_64, 0, x_61);
return x_64;
}
else
{
obj* x_65; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_65 = lean::cnstr_get(x_55, 0);
lean::inc(x_65);
lean::dec(x_55);
x_68 = lean::cnstr_get(x_65, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_65, 1);
lean::inc(x_70);
if (lean::is_shared(x_65)) {
 lean::dec(x_65);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_72 = x_65;
}
if (lean::is_scalar(x_32)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_32;
}
lean::cnstr_set(x_73, 0, x_28);
lean::cnstr_set(x_73, 1, x_50);
x_74 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1;
lean::inc(x_74);
if (lean::is_scalar(x_54)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_54;
}
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_73);
if (lean::is_scalar(x_12)) {
 x_77 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_77 = x_12;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_68);
if (lean::is_scalar(x_72)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_72;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_70);
if (lean::is_scalar(x_27)) {
 x_79 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_79 = x_27;
}
lean::cnstr_set(x_79, 0, x_78);
return x_79;
}
}
}
}
}
}
obj* _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_match_fn");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
lean::inc(x_1);
x_17 = l_lean_elaborator_to__pexpr___main(x_13, x_1, x_2);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_23 = x_17;
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
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_27 = x_17;
}
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_32 = x_25;
}
x_33 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__5(x_10, x_1, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_40; 
lean::dec(x_12);
lean::dec(x_28);
lean::dec(x_32);
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_27;
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_33, 0);
lean::inc(x_41);
lean::dec(x_33);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
lean::dec(x_41);
if (lean::is_scalar(x_12)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_12;
}
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_44);
if (lean::is_scalar(x_32)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_32;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
if (lean::is_scalar(x_27)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_27;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
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
obj* x_2; 
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
unsigned char x_10; obj* x_11; 
lean::dec(x_7);
x_10 = 1;
x_11 = l_coe__decidable__eq(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_16; 
lean::dec(x_11);
lean::dec(x_5);
lean::dec(x_3);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_0);
return x_16;
}
else
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_11);
lean::dec(x_0);
x_19 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_5);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 lean::cnstr_release(x_19, 1);
 x_24 = x_19;
}
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_3);
lean::cnstr_set(x_25, 1, x_20);
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_22);
return x_26;
}
}
else
{
unsigned char x_28; obj* x_29; 
lean::dec(x_7);
x_28 = 0;
x_29 = l_coe__decidable__eq(x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_29);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_0);
return x_34;
}
else
{
obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
lean::dec(x_29);
x_37 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__6(x_5);
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
lean::cnstr_set(x_43, 0, x_3);
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
}
}
}
obj* l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
unsigned char x_10; obj* x_11; 
lean::dec(x_7);
x_10 = 0;
x_11 = l_coe__decidable__eq(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_16; 
lean::dec(x_11);
lean::dec(x_5);
lean::dec(x_3);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_0);
return x_16;
}
else
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_11);
lean::dec(x_0);
x_19 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_5);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 lean::cnstr_release(x_19, 1);
 x_24 = x_19;
}
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_3);
lean::cnstr_set(x_25, 1, x_20);
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_22);
return x_26;
}
}
else
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_7, 0);
lean::inc(x_27);
lean::dec(x_7);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
unsigned char x_34; obj* x_35; 
lean::dec(x_30);
x_34 = 0;
x_35 = l_coe__decidable__eq(x_34);
if (lean::obj_tag(x_35) == 0)
{
obj* x_39; obj* x_40; 
lean::dec(x_35);
lean::dec(x_5);
lean::dec(x_3);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_0);
return x_40;
}
else
{
obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_35);
lean::dec(x_0);
x_43 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_5);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
if (lean::is_shared(x_43)) {
 lean::dec(x_43);
 x_48 = lean::box(0);
} else {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 x_48 = x_43;
}
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_3);
lean::cnstr_set(x_49, 1, x_44);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
return x_50;
}
}
else
{
unsigned char x_52; obj* x_53; 
lean::dec(x_30);
x_52 = 1;
x_53 = l_coe__decidable__eq(x_52);
if (lean::obj_tag(x_53) == 0)
{
obj* x_57; obj* x_58; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_53);
x_57 = lean::box(0);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_0);
return x_58;
}
else
{
obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_0);
lean::dec(x_53);
x_61 = l_list_span___main___at_lean_elaborator_to__pexpr___main___spec__7(x_5);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
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
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_3);
lean::cnstr_set(x_67, 1, x_62);
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_64);
return x_68;
}
}
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; obj* x_21; obj* x_24; 
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_2);
x_24 = l_lean_elaborator_to__pexpr___main(x_21, x_2, x_3);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_14);
lean::dec(x_18);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_24, 0);
lean::inc(x_30);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_32 = x_24;
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
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_36 = x_24;
}
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 x_41 = x_34;
}
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_12, x_2, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; obj* x_50; 
lean::dec(x_14);
lean::dec(x_18);
lean::dec(x_37);
lean::dec(x_41);
x_47 = lean::cnstr_get(x_42, 0);
lean::inc(x_47);
lean::dec(x_42);
if (lean::is_scalar(x_36)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_36;
}
lean::cnstr_set(x_50, 0, x_47);
return x_50;
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_51 = lean::cnstr_get(x_42, 0);
lean::inc(x_51);
lean::dec(x_42);
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
x_59 = lean::box(0);
x_60 = lean::cnstr_get(x_18, 0);
lean::inc(x_60);
lean::dec(x_18);
x_63 = l_lean_elaborator_mangle__ident(x_60);
x_64 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
lean::inc(x_64);
x_66 = l_lean_kvmap_set__name(x_59, x_64, x_63);
x_67 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_37);
if (lean::is_scalar(x_14)) {
 x_68 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_68 = x_14;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_54);
if (lean::is_scalar(x_41)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_41;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_56);
if (lean::is_scalar(x_36)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_36;
}
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
obj* x_72; obj* x_76; 
lean::dec(x_15);
x_72 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_72);
lean::inc(x_0);
x_76 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_72, x_2, x_3);
if (lean::obj_tag(x_76) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_81 = lean::cnstr_get(x_76, 0);
lean::inc(x_81);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_83 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_83 = x_76;
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
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_92; obj* x_93; 
x_85 = lean::cnstr_get(x_76, 0);
lean::inc(x_85);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_87 = x_76;
}
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_85, 1);
lean::inc(x_90);
if (lean::is_shared(x_85)) {
 lean::dec(x_85);
 x_92 = lean::box(0);
} else {
 lean::cnstr_release(x_85, 0);
 lean::cnstr_release(x_85, 1);
 x_92 = x_85;
}
x_93 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8(x_0, x_12, x_2, x_90);
if (lean::obj_tag(x_93) == 0)
{
obj* x_97; obj* x_100; 
lean::dec(x_14);
lean::dec(x_88);
lean::dec(x_92);
x_97 = lean::cnstr_get(x_93, 0);
lean::inc(x_97);
lean::dec(x_93);
if (lean::is_scalar(x_87)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_87;
}
lean::cnstr_set(x_100, 0, x_97);
return x_100;
}
else
{
obj* x_101; obj* x_104; obj* x_106; obj* x_109; obj* x_110; obj* x_111; 
x_101 = lean::cnstr_get(x_93, 0);
lean::inc(x_101);
lean::dec(x_93);
x_104 = lean::cnstr_get(x_101, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
lean::dec(x_101);
if (lean::is_scalar(x_14)) {
 x_109 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_109 = x_14;
}
lean::cnstr_set(x_109, 0, x_88);
lean::cnstr_set(x_109, 1, x_104);
if (lean::is_scalar(x_92)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_92;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_106);
if (lean::is_scalar(x_87)) {
 x_111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_111 = x_87;
}
lean::cnstr_set(x_111, 0, x_110);
return x_111;
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
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__9(x_6);
x_10 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_23; 
lean::dec(x_15);
x_19 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_19);
lean::inc(x_0);
x_23 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_19, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_30 = x_23;
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
return x_31;
}
else
{
obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; 
x_32 = lean::cnstr_get(x_23, 0);
lean::inc(x_32);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_34 = x_23;
}
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 x_39 = x_32;
}
x_40 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_12, x_2, x_37);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; obj* x_47; 
lean::dec(x_14);
lean::dec(x_39);
lean::dec(x_35);
x_44 = lean::cnstr_get(x_40, 0);
lean::inc(x_44);
lean::dec(x_40);
if (lean::is_scalar(x_34)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_34;
}
lean::cnstr_set(x_47, 0, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; 
x_48 = lean::cnstr_get(x_40, 0);
lean::inc(x_48);
lean::dec(x_40);
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
lean::dec(x_48);
if (lean::is_scalar(x_14)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_14;
}
lean::cnstr_set(x_56, 0, x_35);
lean::cnstr_set(x_56, 1, x_51);
if (lean::is_scalar(x_39)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_39;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
if (lean::is_scalar(x_34)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_34;
}
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
obj* x_59; obj* x_62; 
x_59 = lean::cnstr_get(x_15, 0);
lean::inc(x_59);
lean::dec(x_15);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; obj* x_70; 
lean::dec(x_62);
x_66 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_66);
lean::inc(x_0);
x_70 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_66, x_2, x_3);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_75 = lean::cnstr_get(x_70, 0);
lean::inc(x_75);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_77 = x_70;
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
obj* x_79; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_87; 
x_79 = lean::cnstr_get(x_70, 0);
lean::inc(x_79);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_81 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_81 = x_70;
}
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
x_87 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_12, x_2, x_84);
if (lean::obj_tag(x_87) == 0)
{
obj* x_91; obj* x_94; 
lean::dec(x_14);
lean::dec(x_86);
lean::dec(x_82);
x_91 = lean::cnstr_get(x_87, 0);
lean::inc(x_91);
lean::dec(x_87);
if (lean::is_scalar(x_81)) {
 x_94 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_94 = x_81;
}
lean::cnstr_set(x_94, 0, x_91);
return x_94;
}
else
{
obj* x_95; obj* x_98; obj* x_100; obj* x_103; obj* x_104; obj* x_105; 
x_95 = lean::cnstr_get(x_87, 0);
lean::inc(x_95);
lean::dec(x_87);
x_98 = lean::cnstr_get(x_95, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_95, 1);
lean::inc(x_100);
lean::dec(x_95);
if (lean::is_scalar(x_14)) {
 x_103 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_103 = x_14;
}
lean::cnstr_set(x_103, 0, x_82);
lean::cnstr_set(x_103, 1, x_98);
if (lean::is_scalar(x_86)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_86;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_100);
if (lean::is_scalar(x_81)) {
 x_105 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_105 = x_81;
}
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
obj* x_106; obj* x_110; 
x_106 = lean::cnstr_get(x_62, 0);
lean::inc(x_106);
lean::dec(x_62);
lean::inc(x_2);
x_110 = l_lean_elaborator_to__pexpr___main(x_106, x_2, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_115 = lean::cnstr_get(x_110, 0);
lean::inc(x_115);
if (lean::is_shared(x_110)) {
 lean::dec(x_110);
 x_117 = lean::box(0);
} else {
 lean::cnstr_release(x_110, 0);
 x_117 = x_110;
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
obj* x_119; obj* x_121; obj* x_122; obj* x_124; obj* x_126; obj* x_127; 
x_119 = lean::cnstr_get(x_110, 0);
lean::inc(x_119);
if (lean::is_shared(x_110)) {
 lean::dec(x_110);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_110, 0);
 x_121 = x_110;
}
x_122 = lean::cnstr_get(x_119, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 1);
lean::inc(x_124);
if (lean::is_shared(x_119)) {
 lean::dec(x_119);
 x_126 = lean::box(0);
} else {
 lean::cnstr_release(x_119, 0);
 lean::cnstr_release(x_119, 1);
 x_126 = x_119;
}
x_127 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__10(x_0, x_12, x_2, x_124);
if (lean::obj_tag(x_127) == 0)
{
obj* x_131; obj* x_134; 
lean::dec(x_14);
lean::dec(x_126);
lean::dec(x_122);
x_131 = lean::cnstr_get(x_127, 0);
lean::inc(x_131);
lean::dec(x_127);
if (lean::is_scalar(x_121)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_121;
}
lean::cnstr_set(x_134, 0, x_131);
return x_134;
}
else
{
obj* x_135; obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_145; 
x_135 = lean::cnstr_get(x_127, 0);
lean::inc(x_135);
lean::dec(x_127);
x_138 = lean::cnstr_get(x_135, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_135, 1);
lean::inc(x_140);
lean::dec(x_135);
if (lean::is_scalar(x_14)) {
 x_143 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_143 = x_14;
}
lean::cnstr_set(x_143, 0, x_122);
lean::cnstr_set(x_143, 1, x_138);
if (lean::is_scalar(x_126)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_126;
}
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_140);
if (lean::is_scalar(x_121)) {
 x_145 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_145 = x_121;
}
lean::cnstr_set(x_145, 0, x_144);
return x_145;
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
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; obj* x_21; obj* x_24; 
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_2);
x_24 = l_lean_elaborator_to__pexpr___main(x_21, x_2, x_3);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_14);
lean::dec(x_18);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_24, 0);
lean::inc(x_30);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_32 = x_24;
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
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_36 = x_24;
}
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 x_41 = x_34;
}
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_12, x_2, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; obj* x_50; 
lean::dec(x_14);
lean::dec(x_18);
lean::dec(x_37);
lean::dec(x_41);
x_47 = lean::cnstr_get(x_42, 0);
lean::inc(x_47);
lean::dec(x_42);
if (lean::is_scalar(x_36)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_36;
}
lean::cnstr_set(x_50, 0, x_47);
return x_50;
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_51 = lean::cnstr_get(x_42, 0);
lean::inc(x_51);
lean::dec(x_42);
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
x_59 = lean::box(0);
x_60 = lean::cnstr_get(x_18, 0);
lean::inc(x_60);
lean::dec(x_18);
x_63 = l_lean_elaborator_mangle__ident(x_60);
x_64 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
lean::inc(x_64);
x_66 = l_lean_kvmap_set__name(x_59, x_64, x_63);
x_67 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_37);
if (lean::is_scalar(x_14)) {
 x_68 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_68 = x_14;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_54);
if (lean::is_scalar(x_41)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_41;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_56);
if (lean::is_scalar(x_36)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_36;
}
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
obj* x_72; obj* x_76; 
lean::dec(x_15);
x_72 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_72);
lean::inc(x_0);
x_76 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_72, x_2, x_3);
if (lean::obj_tag(x_76) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_81 = lean::cnstr_get(x_76, 0);
lean::inc(x_81);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_83 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_83 = x_76;
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
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_92; obj* x_93; 
x_85 = lean::cnstr_get(x_76, 0);
lean::inc(x_85);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_87 = x_76;
}
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_85, 1);
lean::inc(x_90);
if (lean::is_shared(x_85)) {
 lean::dec(x_85);
 x_92 = lean::box(0);
} else {
 lean::cnstr_release(x_85, 0);
 lean::cnstr_release(x_85, 1);
 x_92 = x_85;
}
x_93 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__11(x_0, x_12, x_2, x_90);
if (lean::obj_tag(x_93) == 0)
{
obj* x_97; obj* x_100; 
lean::dec(x_14);
lean::dec(x_88);
lean::dec(x_92);
x_97 = lean::cnstr_get(x_93, 0);
lean::inc(x_97);
lean::dec(x_93);
if (lean::is_scalar(x_87)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_87;
}
lean::cnstr_set(x_100, 0, x_97);
return x_100;
}
else
{
obj* x_101; obj* x_104; obj* x_106; obj* x_109; obj* x_110; obj* x_111; 
x_101 = lean::cnstr_get(x_93, 0);
lean::inc(x_101);
lean::dec(x_93);
x_104 = lean::cnstr_get(x_101, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
lean::dec(x_101);
if (lean::is_scalar(x_14)) {
 x_109 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_109 = x_14;
}
lean::cnstr_set(x_109, 0, x_88);
lean::cnstr_set(x_109, 1, x_104);
if (lean::is_scalar(x_92)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_92;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_106);
if (lean::is_scalar(x_87)) {
 x_111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_111 = x_87;
}
lean::cnstr_set(x_111, 0, x_110);
return x_111;
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
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__12(x_6);
x_10 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_23; 
lean::dec(x_15);
x_19 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_19);
lean::inc(x_0);
x_23 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_19, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_30 = x_23;
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
return x_31;
}
else
{
obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; 
x_32 = lean::cnstr_get(x_23, 0);
lean::inc(x_32);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_34 = x_23;
}
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 x_39 = x_32;
}
x_40 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_12, x_2, x_37);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; obj* x_47; 
lean::dec(x_14);
lean::dec(x_39);
lean::dec(x_35);
x_44 = lean::cnstr_get(x_40, 0);
lean::inc(x_44);
lean::dec(x_40);
if (lean::is_scalar(x_34)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_34;
}
lean::cnstr_set(x_47, 0, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; 
x_48 = lean::cnstr_get(x_40, 0);
lean::inc(x_48);
lean::dec(x_40);
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
lean::dec(x_48);
if (lean::is_scalar(x_14)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_14;
}
lean::cnstr_set(x_56, 0, x_35);
lean::cnstr_set(x_56, 1, x_51);
if (lean::is_scalar(x_39)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_39;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
if (lean::is_scalar(x_34)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_34;
}
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
obj* x_59; obj* x_62; 
x_59 = lean::cnstr_get(x_15, 0);
lean::inc(x_59);
lean::dec(x_15);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; obj* x_70; 
lean::dec(x_62);
x_66 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_66);
lean::inc(x_0);
x_70 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_66, x_2, x_3);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_75 = lean::cnstr_get(x_70, 0);
lean::inc(x_75);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_77 = x_70;
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
obj* x_79; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_87; 
x_79 = lean::cnstr_get(x_70, 0);
lean::inc(x_79);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_81 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_81 = x_70;
}
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
x_87 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_12, x_2, x_84);
if (lean::obj_tag(x_87) == 0)
{
obj* x_91; obj* x_94; 
lean::dec(x_14);
lean::dec(x_86);
lean::dec(x_82);
x_91 = lean::cnstr_get(x_87, 0);
lean::inc(x_91);
lean::dec(x_87);
if (lean::is_scalar(x_81)) {
 x_94 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_94 = x_81;
}
lean::cnstr_set(x_94, 0, x_91);
return x_94;
}
else
{
obj* x_95; obj* x_98; obj* x_100; obj* x_103; obj* x_104; obj* x_105; 
x_95 = lean::cnstr_get(x_87, 0);
lean::inc(x_95);
lean::dec(x_87);
x_98 = lean::cnstr_get(x_95, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_95, 1);
lean::inc(x_100);
lean::dec(x_95);
if (lean::is_scalar(x_14)) {
 x_103 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_103 = x_14;
}
lean::cnstr_set(x_103, 0, x_82);
lean::cnstr_set(x_103, 1, x_98);
if (lean::is_scalar(x_86)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_86;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_100);
if (lean::is_scalar(x_81)) {
 x_105 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_105 = x_81;
}
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
obj* x_106; obj* x_110; 
x_106 = lean::cnstr_get(x_62, 0);
lean::inc(x_106);
lean::dec(x_62);
lean::inc(x_2);
x_110 = l_lean_elaborator_to__pexpr___main(x_106, x_2, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_115 = lean::cnstr_get(x_110, 0);
lean::inc(x_115);
if (lean::is_shared(x_110)) {
 lean::dec(x_110);
 x_117 = lean::box(0);
} else {
 lean::cnstr_release(x_110, 0);
 x_117 = x_110;
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
obj* x_119; obj* x_121; obj* x_122; obj* x_124; obj* x_126; obj* x_127; 
x_119 = lean::cnstr_get(x_110, 0);
lean::inc(x_119);
if (lean::is_shared(x_110)) {
 lean::dec(x_110);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_110, 0);
 x_121 = x_110;
}
x_122 = lean::cnstr_get(x_119, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 1);
lean::inc(x_124);
if (lean::is_shared(x_119)) {
 lean::dec(x_119);
 x_126 = lean::box(0);
} else {
 lean::cnstr_release(x_119, 0);
 lean::cnstr_release(x_119, 1);
 x_126 = x_119;
}
x_127 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__13(x_0, x_12, x_2, x_124);
if (lean::obj_tag(x_127) == 0)
{
obj* x_131; obj* x_134; 
lean::dec(x_14);
lean::dec(x_126);
lean::dec(x_122);
x_131 = lean::cnstr_get(x_127, 0);
lean::inc(x_131);
lean::dec(x_127);
if (lean::is_scalar(x_121)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_121;
}
lean::cnstr_set(x_134, 0, x_131);
return x_134;
}
else
{
obj* x_135; obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_145; 
x_135 = lean::cnstr_get(x_127, 0);
lean::inc(x_135);
lean::dec(x_127);
x_138 = lean::cnstr_get(x_135, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_135, 1);
lean::inc(x_140);
lean::dec(x_135);
if (lean::is_scalar(x_14)) {
 x_143 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_143 = x_14;
}
lean::cnstr_set(x_143, 0, x_122);
lean::cnstr_set(x_143, 1, x_138);
if (lean::is_scalar(x_126)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_126;
}
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_140);
if (lean::is_scalar(x_121)) {
 x_145 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_145 = x_121;
}
lean::cnstr_set(x_145, 0, x_144);
return x_145;
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
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; obj* x_21; obj* x_24; 
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_2);
x_24 = l_lean_elaborator_to__pexpr___main(x_21, x_2, x_3);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_14);
lean::dec(x_18);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_24, 0);
lean::inc(x_30);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_32 = x_24;
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
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_36 = x_24;
}
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 x_41 = x_34;
}
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_12, x_2, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; obj* x_50; 
lean::dec(x_14);
lean::dec(x_18);
lean::dec(x_37);
lean::dec(x_41);
x_47 = lean::cnstr_get(x_42, 0);
lean::inc(x_47);
lean::dec(x_42);
if (lean::is_scalar(x_36)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_36;
}
lean::cnstr_set(x_50, 0, x_47);
return x_50;
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_51 = lean::cnstr_get(x_42, 0);
lean::inc(x_51);
lean::dec(x_42);
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
x_59 = lean::box(0);
x_60 = lean::cnstr_get(x_18, 0);
lean::inc(x_60);
lean::dec(x_18);
x_63 = l_lean_elaborator_mangle__ident(x_60);
x_64 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
lean::inc(x_64);
x_66 = l_lean_kvmap_set__name(x_59, x_64, x_63);
x_67 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_37);
if (lean::is_scalar(x_14)) {
 x_68 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_68 = x_14;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_54);
if (lean::is_scalar(x_41)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_41;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_56);
if (lean::is_scalar(x_36)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_36;
}
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
obj* x_72; obj* x_76; 
lean::dec(x_15);
x_72 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_72);
lean::inc(x_0);
x_76 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_72, x_2, x_3);
if (lean::obj_tag(x_76) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_81 = lean::cnstr_get(x_76, 0);
lean::inc(x_81);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_83 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_83 = x_76;
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
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_92; obj* x_93; 
x_85 = lean::cnstr_get(x_76, 0);
lean::inc(x_85);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_87 = x_76;
}
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_85, 1);
lean::inc(x_90);
if (lean::is_shared(x_85)) {
 lean::dec(x_85);
 x_92 = lean::box(0);
} else {
 lean::cnstr_release(x_85, 0);
 lean::cnstr_release(x_85, 1);
 x_92 = x_85;
}
x_93 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__14(x_0, x_12, x_2, x_90);
if (lean::obj_tag(x_93) == 0)
{
obj* x_97; obj* x_100; 
lean::dec(x_14);
lean::dec(x_88);
lean::dec(x_92);
x_97 = lean::cnstr_get(x_93, 0);
lean::inc(x_97);
lean::dec(x_93);
if (lean::is_scalar(x_87)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_87;
}
lean::cnstr_set(x_100, 0, x_97);
return x_100;
}
else
{
obj* x_101; obj* x_104; obj* x_106; obj* x_109; obj* x_110; obj* x_111; 
x_101 = lean::cnstr_get(x_93, 0);
lean::inc(x_101);
lean::dec(x_93);
x_104 = lean::cnstr_get(x_101, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
lean::dec(x_101);
if (lean::is_scalar(x_14)) {
 x_109 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_109 = x_14;
}
lean::cnstr_set(x_109, 0, x_88);
lean::cnstr_set(x_109, 1, x_104);
if (lean::is_scalar(x_92)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_92;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_106);
if (lean::is_scalar(x_87)) {
 x_111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_111 = x_87;
}
lean::cnstr_set(x_111, 0, x_110);
return x_111;
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
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__15(x_6);
x_10 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_23; 
lean::dec(x_15);
x_19 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_19);
lean::inc(x_0);
x_23 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_19, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_30 = x_23;
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
return x_31;
}
else
{
obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; 
x_32 = lean::cnstr_get(x_23, 0);
lean::inc(x_32);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_34 = x_23;
}
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 x_39 = x_32;
}
x_40 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_12, x_2, x_37);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; obj* x_47; 
lean::dec(x_14);
lean::dec(x_39);
lean::dec(x_35);
x_44 = lean::cnstr_get(x_40, 0);
lean::inc(x_44);
lean::dec(x_40);
if (lean::is_scalar(x_34)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_34;
}
lean::cnstr_set(x_47, 0, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; 
x_48 = lean::cnstr_get(x_40, 0);
lean::inc(x_48);
lean::dec(x_40);
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
lean::dec(x_48);
if (lean::is_scalar(x_14)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_14;
}
lean::cnstr_set(x_56, 0, x_35);
lean::cnstr_set(x_56, 1, x_51);
if (lean::is_scalar(x_39)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_39;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
if (lean::is_scalar(x_34)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_34;
}
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
obj* x_59; obj* x_62; 
x_59 = lean::cnstr_get(x_15, 0);
lean::inc(x_59);
lean::dec(x_15);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; obj* x_70; 
lean::dec(x_62);
x_66 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_66);
lean::inc(x_0);
x_70 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_66, x_2, x_3);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_75 = lean::cnstr_get(x_70, 0);
lean::inc(x_75);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_77 = x_70;
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
obj* x_79; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_87; 
x_79 = lean::cnstr_get(x_70, 0);
lean::inc(x_79);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_81 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_81 = x_70;
}
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
x_87 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_12, x_2, x_84);
if (lean::obj_tag(x_87) == 0)
{
obj* x_91; obj* x_94; 
lean::dec(x_14);
lean::dec(x_86);
lean::dec(x_82);
x_91 = lean::cnstr_get(x_87, 0);
lean::inc(x_91);
lean::dec(x_87);
if (lean::is_scalar(x_81)) {
 x_94 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_94 = x_81;
}
lean::cnstr_set(x_94, 0, x_91);
return x_94;
}
else
{
obj* x_95; obj* x_98; obj* x_100; obj* x_103; obj* x_104; obj* x_105; 
x_95 = lean::cnstr_get(x_87, 0);
lean::inc(x_95);
lean::dec(x_87);
x_98 = lean::cnstr_get(x_95, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_95, 1);
lean::inc(x_100);
lean::dec(x_95);
if (lean::is_scalar(x_14)) {
 x_103 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_103 = x_14;
}
lean::cnstr_set(x_103, 0, x_82);
lean::cnstr_set(x_103, 1, x_98);
if (lean::is_scalar(x_86)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_86;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_100);
if (lean::is_scalar(x_81)) {
 x_105 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_105 = x_81;
}
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
obj* x_106; obj* x_110; 
x_106 = lean::cnstr_get(x_62, 0);
lean::inc(x_106);
lean::dec(x_62);
lean::inc(x_2);
x_110 = l_lean_elaborator_to__pexpr___main(x_106, x_2, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_115 = lean::cnstr_get(x_110, 0);
lean::inc(x_115);
if (lean::is_shared(x_110)) {
 lean::dec(x_110);
 x_117 = lean::box(0);
} else {
 lean::cnstr_release(x_110, 0);
 x_117 = x_110;
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
obj* x_119; obj* x_121; obj* x_122; obj* x_124; obj* x_126; obj* x_127; 
x_119 = lean::cnstr_get(x_110, 0);
lean::inc(x_119);
if (lean::is_shared(x_110)) {
 lean::dec(x_110);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_110, 0);
 x_121 = x_110;
}
x_122 = lean::cnstr_get(x_119, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 1);
lean::inc(x_124);
if (lean::is_shared(x_119)) {
 lean::dec(x_119);
 x_126 = lean::box(0);
} else {
 lean::cnstr_release(x_119, 0);
 lean::cnstr_release(x_119, 1);
 x_126 = x_119;
}
x_127 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__16(x_0, x_12, x_2, x_124);
if (lean::obj_tag(x_127) == 0)
{
obj* x_131; obj* x_134; 
lean::dec(x_14);
lean::dec(x_126);
lean::dec(x_122);
x_131 = lean::cnstr_get(x_127, 0);
lean::inc(x_131);
lean::dec(x_127);
if (lean::is_scalar(x_121)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_121;
}
lean::cnstr_set(x_134, 0, x_131);
return x_134;
}
else
{
obj* x_135; obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_145; 
x_135 = lean::cnstr_get(x_127, 0);
lean::inc(x_135);
lean::dec(x_127);
x_138 = lean::cnstr_get(x_135, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_135, 1);
lean::inc(x_140);
lean::dec(x_135);
if (lean::is_scalar(x_14)) {
 x_143 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_143 = x_14;
}
lean::cnstr_set(x_143, 0, x_122);
lean::cnstr_set(x_143, 1, x_138);
if (lean::is_scalar(x_126)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_126;
}
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_140);
if (lean::is_scalar(x_121)) {
 x_145 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_145 = x_121;
}
lean::cnstr_set(x_145, 0, x_144);
return x_145;
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
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; obj* x_21; obj* x_24; 
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_2);
x_24 = l_lean_elaborator_to__pexpr___main(x_21, x_2, x_3);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_14);
lean::dec(x_18);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_24, 0);
lean::inc(x_30);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_32 = x_24;
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
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_36 = x_24;
}
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 x_41 = x_34;
}
x_42 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_12, x_2, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; obj* x_50; 
lean::dec(x_14);
lean::dec(x_18);
lean::dec(x_37);
lean::dec(x_41);
x_47 = lean::cnstr_get(x_42, 0);
lean::inc(x_47);
lean::dec(x_42);
if (lean::is_scalar(x_36)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_36;
}
lean::cnstr_set(x_50, 0, x_47);
return x_50;
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_51 = lean::cnstr_get(x_42, 0);
lean::inc(x_51);
lean::dec(x_42);
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
x_59 = lean::box(0);
x_60 = lean::cnstr_get(x_18, 0);
lean::inc(x_60);
lean::dec(x_18);
x_63 = l_lean_elaborator_mangle__ident(x_60);
x_64 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1;
lean::inc(x_64);
x_66 = l_lean_kvmap_set__name(x_59, x_64, x_63);
x_67 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_37);
if (lean::is_scalar(x_14)) {
 x_68 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_68 = x_14;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_54);
if (lean::is_scalar(x_41)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_41;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_56);
if (lean::is_scalar(x_36)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_36;
}
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
obj* x_72; obj* x_76; 
lean::dec(x_15);
x_72 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_72);
lean::inc(x_0);
x_76 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_72, x_2, x_3);
if (lean::obj_tag(x_76) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_81 = lean::cnstr_get(x_76, 0);
lean::inc(x_81);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_83 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_83 = x_76;
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
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_92; obj* x_93; 
x_85 = lean::cnstr_get(x_76, 0);
lean::inc(x_85);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_87 = x_76;
}
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_85, 1);
lean::inc(x_90);
if (lean::is_shared(x_85)) {
 lean::dec(x_85);
 x_92 = lean::box(0);
} else {
 lean::cnstr_release(x_85, 0);
 lean::cnstr_release(x_85, 1);
 x_92 = x_85;
}
x_93 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__17(x_0, x_12, x_2, x_90);
if (lean::obj_tag(x_93) == 0)
{
obj* x_97; obj* x_100; 
lean::dec(x_14);
lean::dec(x_88);
lean::dec(x_92);
x_97 = lean::cnstr_get(x_93, 0);
lean::inc(x_97);
lean::dec(x_93);
if (lean::is_scalar(x_87)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_87;
}
lean::cnstr_set(x_100, 0, x_97);
return x_100;
}
else
{
obj* x_101; obj* x_104; obj* x_106; obj* x_109; obj* x_110; obj* x_111; 
x_101 = lean::cnstr_get(x_93, 0);
lean::inc(x_101);
lean::dec(x_93);
x_104 = lean::cnstr_get(x_101, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
lean::dec(x_101);
if (lean::is_scalar(x_14)) {
 x_109 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_109 = x_14;
}
lean::cnstr_set(x_109, 0, x_88);
lean::cnstr_set(x_109, 1, x_104);
if (lean::is_scalar(x_92)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_92;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_106);
if (lean::is_scalar(x_87)) {
 x_111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_111 = x_87;
}
lean::cnstr_set(x_111, 0, x_110);
return x_111;
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
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_elaborator_to__pexpr___main___closed__42;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_list_foldr___main___at_lean_elaborator_to__pexpr___main___spec__18(x_6);
x_10 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_23; 
lean::dec(x_15);
x_19 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_19);
lean::inc(x_0);
x_23 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_19, x_2, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_30 = x_23;
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
return x_31;
}
else
{
obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; 
x_32 = lean::cnstr_get(x_23, 0);
lean::inc(x_32);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_34 = x_23;
}
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 x_39 = x_32;
}
x_40 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_12, x_2, x_37);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; obj* x_47; 
lean::dec(x_14);
lean::dec(x_39);
lean::dec(x_35);
x_44 = lean::cnstr_get(x_40, 0);
lean::inc(x_44);
lean::dec(x_40);
if (lean::is_scalar(x_34)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_34;
}
lean::cnstr_set(x_47, 0, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; 
x_48 = lean::cnstr_get(x_40, 0);
lean::inc(x_48);
lean::dec(x_40);
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
lean::dec(x_48);
if (lean::is_scalar(x_14)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_14;
}
lean::cnstr_set(x_56, 0, x_35);
lean::cnstr_set(x_56, 1, x_51);
if (lean::is_scalar(x_39)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_39;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
if (lean::is_scalar(x_34)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_34;
}
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
obj* x_59; obj* x_62; 
x_59 = lean::cnstr_get(x_15, 0);
lean::inc(x_59);
lean::dec(x_15);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; obj* x_70; 
lean::dec(x_62);
x_66 = l_lean_elaborator_to__pexpr___main___closed__23;
lean::inc(x_2);
lean::inc(x_66);
lean::inc(x_0);
x_70 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_66, x_2, x_3);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_75 = lean::cnstr_get(x_70, 0);
lean::inc(x_75);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_77 = x_70;
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
obj* x_79; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_87; 
x_79 = lean::cnstr_get(x_70, 0);
lean::inc(x_79);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_81 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_81 = x_70;
}
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
x_87 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_12, x_2, x_84);
if (lean::obj_tag(x_87) == 0)
{
obj* x_91; obj* x_94; 
lean::dec(x_14);
lean::dec(x_86);
lean::dec(x_82);
x_91 = lean::cnstr_get(x_87, 0);
lean::inc(x_91);
lean::dec(x_87);
if (lean::is_scalar(x_81)) {
 x_94 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_94 = x_81;
}
lean::cnstr_set(x_94, 0, x_91);
return x_94;
}
else
{
obj* x_95; obj* x_98; obj* x_100; obj* x_103; obj* x_104; obj* x_105; 
x_95 = lean::cnstr_get(x_87, 0);
lean::inc(x_95);
lean::dec(x_87);
x_98 = lean::cnstr_get(x_95, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_95, 1);
lean::inc(x_100);
lean::dec(x_95);
if (lean::is_scalar(x_14)) {
 x_103 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_103 = x_14;
}
lean::cnstr_set(x_103, 0, x_82);
lean::cnstr_set(x_103, 1, x_98);
if (lean::is_scalar(x_86)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_86;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_100);
if (lean::is_scalar(x_81)) {
 x_105 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_105 = x_81;
}
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
obj* x_106; obj* x_110; 
x_106 = lean::cnstr_get(x_62, 0);
lean::inc(x_106);
lean::dec(x_62);
lean::inc(x_2);
x_110 = l_lean_elaborator_to__pexpr___main(x_106, x_2, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_115 = lean::cnstr_get(x_110, 0);
lean::inc(x_115);
if (lean::is_shared(x_110)) {
 lean::dec(x_110);
 x_117 = lean::box(0);
} else {
 lean::cnstr_release(x_110, 0);
 x_117 = x_110;
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
obj* x_119; obj* x_121; obj* x_122; obj* x_124; obj* x_126; obj* x_127; 
x_119 = lean::cnstr_get(x_110, 0);
lean::inc(x_119);
if (lean::is_shared(x_110)) {
 lean::dec(x_110);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_110, 0);
 x_121 = x_110;
}
x_122 = lean::cnstr_get(x_119, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 1);
lean::inc(x_124);
if (lean::is_shared(x_119)) {
 lean::dec(x_119);
 x_126 = lean::box(0);
} else {
 lean::cnstr_release(x_119, 0);
 lean::cnstr_release(x_119, 1);
 x_126 = x_119;
}
x_127 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__19(x_0, x_12, x_2, x_124);
if (lean::obj_tag(x_127) == 0)
{
obj* x_131; obj* x_134; 
lean::dec(x_14);
lean::dec(x_126);
lean::dec(x_122);
x_131 = lean::cnstr_get(x_127, 0);
lean::inc(x_131);
lean::dec(x_127);
if (lean::is_scalar(x_121)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_121;
}
lean::cnstr_set(x_134, 0, x_131);
return x_134;
}
else
{
obj* x_135; obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_145; 
x_135 = lean::cnstr_get(x_127, 0);
lean::inc(x_135);
lean::dec(x_127);
x_138 = lean::cnstr_get(x_135, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_135, 1);
lean::inc(x_140);
lean::dec(x_135);
if (lean::is_scalar(x_14)) {
 x_143 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_143 = x_14;
}
lean::cnstr_set(x_143, 0, x_122);
lean::cnstr_set(x_143, 1, x_138);
if (lean::is_scalar(x_126)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_126;
}
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_140);
if (lean::is_scalar(x_121)) {
 x_145 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_145 = x_121;
}
lean::cnstr_set(x_145, 0, x_144);
return x_145;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
lean::inc(x_1);
x_14 = l_lean_elaborator_to__pexpr___main(x_8, x_1, x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_20 = x_14;
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
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_24 = x_14;
}
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_29 = x_22;
}
x_30 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__20(x_10, x_1, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_37; 
lean::dec(x_12);
lean::dec(x_25);
lean::dec(x_29);
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
if (lean::is_scalar(x_24)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_24;
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
if (lean::is_scalar(x_12)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_12;
}
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_41);
if (lean::is_scalar(x_29)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_29;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_24)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_24;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
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
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_list_map___main___at_lean_elaborator_to__pexpr___main___spec__21(x_5);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
obj* l_list_foldl___main___at_lean_elaborator_to__pexpr___main___spec__22(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::box(0);
x_14 = lean::name_mk_numeral(x_13, x_8);
x_15 = l_lean_kvmap_set__name(x_0, x_14, x_10);
x_0 = x_15;
x_1 = x_5;
goto _start;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
lean::inc(x_1);
x_14 = l_lean_elaborator_to__level___main(x_8, x_1, x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_20 = x_14;
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
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_24 = x_14;
}
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_29 = x_22;
}
x_30 = l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__23(x_10, x_1, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_37; 
lean::dec(x_12);
lean::dec(x_25);
lean::dec(x_29);
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
if (lean::is_scalar(x_24)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_24;
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
if (lean::is_scalar(x_12)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_12;
}
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_41);
if (lean::is_scalar(x_29)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_29;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_24)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_24;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
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
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::box(0);
x_14 = lean::name_mk_numeral(x_13, x_8);
x_15 = l_lean_kvmap_set__name(x_0, x_14, x_10);
x_0 = x_15;
x_1 = x_5;
goto _start;
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
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_0);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_0);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
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
case 0:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
case 1:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
case 2:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
case 3:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
case 4:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
case 5:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
case 6:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
case 7:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
case 8:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
case 9:
{
lean::dec(x_0);
x_9 = x_1;
goto lbl_10;
}
case 10:
{
obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_40; obj* x_42; obj* x_43; 
x_21 = lean::cnstr_get(x_1, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_1, 1);
lean::inc(x_23);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_25 = x_1;
}
x_26 = lean::cnstr_get(x_4, 2);
lean::inc(x_26);
x_28 = l_lean_parser_syntax_get__pos(x_0);
x_29 = lean::mk_nat_obj(0u);
x_30 = l_option_get__or__else___main___rarg(x_28, x_29);
x_31 = l_lean_file__map_to__position(x_26, x_30);
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
x_34 = l_lean_elaborator_to__pexpr___main___closed__3;
lean::inc(x_34);
x_36 = l_lean_kvmap_set__nat(x_21, x_34, x_32);
x_37 = lean::cnstr_get(x_31, 0);
lean::inc(x_37);
lean::dec(x_31);
x_40 = l_lean_elaborator_to__pexpr___main___closed__4;
lean::inc(x_40);
x_42 = l_lean_kvmap_set__nat(x_36, x_40, x_37);
if (lean::is_scalar(x_25)) {
 x_43 = lean::alloc_cnstr(10, 2, 0);
} else {
 x_43 = x_25;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_23);
x_9 = x_43;
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
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_9);
x_48 = lean::cnstr_get(x_8, 0);
lean::inc(x_48);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_50 = x_8;
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
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_74; obj* x_75; obj* x_77; obj* x_80; obj* x_81; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_92; 
x_52 = lean::cnstr_get(x_8, 0);
lean::inc(x_52);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_54 = x_8;
}
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 1);
lean::inc(x_57);
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_59 = x_52;
}
x_60 = lean::cnstr_get(x_4, 0);
lean::inc(x_60);
lean::dec(x_4);
x_63 = lean::cnstr_get(x_3, 8);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_3, 9);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_3, 4);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_67, 1);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
lean::dec(x_69);
x_74 = l_list_reverse___rarg(x_71);
x_75 = lean::cnstr_get(x_67, 2);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_75, 0);
lean::inc(x_77);
lean::dec(x_75);
x_80 = l_list_reverse___rarg(x_77);
x_81 = lean::cnstr_get(x_67, 3);
lean::inc(x_81);
x_83 = l_rbtree_to__list___rarg(x_81);
x_84 = lean::cnstr_get(x_67, 6);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_3, 10);
lean::inc(x_86);
x_88 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_88, 0, x_63);
lean::cnstr_set(x_88, 1, x_65);
lean::cnstr_set(x_88, 2, x_74);
lean::cnstr_set(x_88, 3, x_80);
lean::cnstr_set(x_88, 4, x_83);
lean::cnstr_set(x_88, 5, x_84);
lean::cnstr_set(x_88, 6, x_86);
lean::cnstr_set(x_88, 7, x_55);
x_89 = lean_elaborator_elaborate_command(x_60, x_9, x_88);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
if (lean::obj_tag(x_90) == 0)
{
obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_3);
lean::dec(x_90);
lean::dec(x_67);
x_98 = lean::cnstr_get(x_57, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_57, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_57, 2);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_57, 3);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_57, 4);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_57, 5);
lean::inc(x_108);
x_110 = l_list_append___main___rarg(x_92, x_108);
x_111 = lean::cnstr_get(x_57, 6);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_57, 7);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_57, 8);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_57, 9);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_57, 10);
lean::inc(x_119);
lean::dec(x_57);
x_122 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_122, 0, x_98);
lean::cnstr_set(x_122, 1, x_100);
lean::cnstr_set(x_122, 2, x_102);
lean::cnstr_set(x_122, 3, x_104);
lean::cnstr_set(x_122, 4, x_106);
lean::cnstr_set(x_122, 5, x_110);
lean::cnstr_set(x_122, 6, x_111);
lean::cnstr_set(x_122, 7, x_113);
lean::cnstr_set(x_122, 8, x_115);
lean::cnstr_set(x_122, 9, x_117);
lean::cnstr_set(x_122, 10, x_119);
x_123 = lean::box(0);
if (lean::is_scalar(x_59)) {
 x_124 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_124 = x_59;
}
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_122);
if (lean::is_scalar(x_54)) {
 x_125 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_125 = x_54;
}
lean::cnstr_set(x_125, 0, x_124);
return x_125;
}
else
{
obj* x_127; obj* x_130; obj* x_132; obj* x_134; obj* x_136; obj* x_138; obj* x_140; obj* x_142; obj* x_144; obj* x_145; obj* x_147; obj* x_149; obj* x_150; obj* x_152; obj* x_153; obj* x_155; obj* x_158; obj* x_160; obj* x_161; obj* x_163; obj* x_165; obj* x_168; obj* x_170; obj* x_172; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_57);
x_127 = lean::cnstr_get(x_90, 0);
lean::inc(x_127);
lean::dec(x_90);
x_130 = lean::cnstr_get(x_3, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_3, 1);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_3, 2);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_3, 3);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_67, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_127, 2);
lean::inc(x_140);
x_142 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1;
lean::inc(x_142);
x_144 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__7(x_142, x_140);
x_145 = lean::cnstr_get(x_127, 3);
lean::inc(x_145);
x_147 = l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1;
lean::inc(x_147);
x_149 = l_list_foldl___main___at_lean_elaborator_old__elab__command___spec__14(x_147, x_145);
x_150 = lean::cnstr_get(x_127, 4);
lean::inc(x_150);
x_152 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(x_150);
x_153 = lean::cnstr_get(x_67, 4);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_67, 5);
lean::inc(x_155);
lean::dec(x_67);
x_158 = lean::cnstr_get(x_127, 5);
lean::inc(x_158);
x_160 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_160, 0, x_138);
lean::cnstr_set(x_160, 1, x_144);
lean::cnstr_set(x_160, 2, x_149);
lean::cnstr_set(x_160, 3, x_152);
lean::cnstr_set(x_160, 4, x_153);
lean::cnstr_set(x_160, 5, x_155);
lean::cnstr_set(x_160, 6, x_158);
x_161 = lean::cnstr_get(x_3, 5);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_3, 6);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_3, 7);
lean::inc(x_165);
lean::dec(x_3);
x_168 = lean::cnstr_get(x_127, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_127, 1);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_127, 6);
lean::inc(x_172);
lean::dec(x_127);
x_175 = l_list_append___main___rarg(x_92, x_161);
x_176 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_176, 0, x_130);
lean::cnstr_set(x_176, 1, x_132);
lean::cnstr_set(x_176, 2, x_134);
lean::cnstr_set(x_176, 3, x_136);
lean::cnstr_set(x_176, 4, x_160);
lean::cnstr_set(x_176, 5, x_175);
lean::cnstr_set(x_176, 6, x_163);
lean::cnstr_set(x_176, 7, x_165);
lean::cnstr_set(x_176, 8, x_168);
lean::cnstr_set(x_176, 9, x_170);
lean::cnstr_set(x_176, 10, x_172);
x_177 = lean::box(0);
if (lean::is_scalar(x_59)) {
 x_178 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_178 = x_59;
}
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_176);
if (lean::is_scalar(x_54)) {
 x_179 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_179 = x_54;
}
lean::cnstr_set(x_179, 0, x_178);
return x_179;
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; unsigned char x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; unsigned char x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
unsigned char x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
unsigned char x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__5(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
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
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__2(x_0, x_8, x_10);
x_0 = x_13;
x_1 = x_5;
goto _start;
}
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
obj* _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__6;
lean::inc(x_0);
return x_0;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; unsigned char x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; unsigned char x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
unsigned char x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
unsigned char x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__12(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
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
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_old__elab__command___spec__9(x_0, x_8, x_10);
x_0 = x_13;
x_1 = x_5;
goto _start;
}
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
obj* _init_l_lean_elaborator_ordered__rbmap_of__list___at_lean_elaborator_old__elab__command___spec__8___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_old__elab__command___spec__13;
lean::inc(x_0);
return x_0;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; unsigned char x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; unsigned char x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
unsigned char x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
unsigned char x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_old__elab__command___spec__18(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_rbtree_of__list___main___at_lean_elaborator_old__elab__command___spec__15(x_5);
x_9 = lean::box(0);
x_10 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(x_8, x_3, x_9);
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
obj* l_list_map___main___at_lean_elaborator_names__to__pexpr___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
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
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_list_map___main___at_lean_elaborator_names__to__pexpr___spec__1(x_5);
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
obj* l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
lean::inc(x_1);
x_14 = l_lean_elaborator_to__pexpr___main(x_8, x_1, x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_20 = x_14;
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
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_24 = x_14;
}
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_29 = x_22;
}
x_30 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_10, x_1, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_37; 
lean::dec(x_12);
lean::dec(x_25);
lean::dec(x_29);
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
if (lean::is_scalar(x_24)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_24;
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
if (lean::is_scalar(x_12)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_12;
}
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_41);
if (lean::is_scalar(x_29)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_29;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_24)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_24;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::inc(x_1);
x_19 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__1(x_16, x_1, x_2);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_24 = lean::cnstr_get(x_19, 0);
lean::inc(x_24);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_26 = x_19;
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
obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_36; 
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_30 = x_19;
}
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_release(x_28, 1);
 x_35 = x_28;
}
x_36 = l_list_mmap___main___at_lean_elaborator_attrs__to__pexpr___spec__2(x_10, x_1, x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_41; obj* x_44; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_35);
lean::dec(x_31);
x_41 = lean::cnstr_get(x_36, 0);
lean::inc(x_41);
lean::dec(x_36);
if (lean::is_scalar(x_30)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_30;
}
lean::cnstr_set(x_44, 0, x_41);
return x_44;
}
else
{
obj* x_45; obj* x_48; obj* x_50; obj* x_53; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_45 = lean::cnstr_get(x_36, 0);
lean::inc(x_45);
lean::dec(x_36);
x_48 = lean::cnstr_get(x_45, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
lean::dec(x_45);
x_53 = lean::cnstr_get(x_13, 0);
lean::inc(x_53);
lean::dec(x_13);
x_56 = lean::cnstr_get(x_53, 2);
lean::inc(x_56);
lean::dec(x_53);
x_59 = l_lean_expr_mk__capp(x_56, x_31);
if (lean::is_scalar(x_12)) {
 x_60 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_60 = x_12;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_48);
if (lean::is_scalar(x_35)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_35;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_50);
if (lean::is_scalar(x_30)) {
 x_62 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_62 = x_30;
}
lean::cnstr_set(x_62, 0, x_61);
return x_62;
}
}
}
}
}
obj* l_lean_elaborator_decl__modifiers__to__pexpr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; unsigned char x_10; obj* x_11; unsigned char x_13; obj* x_14; obj* x_17; 
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
lean::dec(x_4);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_6);
x_17 = x_3;
goto lbl_18;
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
lean::inc(x_25);
x_17 = x_25;
goto lbl_18;
}
else
{
obj* x_28; 
lean::dec(x_21);
x_28 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
lean::inc(x_28);
x_17 = x_28;
goto lbl_18;
}
}
}
else
{
obj* x_30; obj* x_33; 
x_30 = lean::cnstr_get(x_4, 0);
lean::inc(x_30);
lean::dec(x_4);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
if (lean::obj_tag(x_33) == 0)
{
lean::dec(x_33);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_6);
x_17 = x_3;
goto lbl_18;
}
else
{
obj* x_38; 
x_38 = lean::cnstr_get(x_6, 0);
lean::inc(x_38);
lean::dec(x_6);
if (lean::obj_tag(x_38) == 0)
{
obj* x_42; 
lean::dec(x_38);
x_42 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__3;
lean::inc(x_42);
x_17 = x_42;
goto lbl_18;
}
else
{
obj* x_45; 
lean::dec(x_38);
x_45 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__4;
lean::inc(x_45);
x_17 = x_45;
goto lbl_18;
}
}
}
else
{
obj* x_47; obj* x_50; obj* x_53; obj* x_56; 
x_47 = lean::cnstr_get(x_33, 0);
lean::inc(x_47);
lean::dec(x_33);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
lean::dec(x_47);
x_53 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__5;
lean::inc(x_53);
lean::inc(x_3);
x_56 = l_lean_kvmap_set__string(x_3, x_53, x_50);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_6);
x_17 = x_56;
goto lbl_18;
}
else
{
obj* x_58; 
x_58 = lean::cnstr_get(x_6, 0);
lean::inc(x_58);
lean::dec(x_6);
if (lean::obj_tag(x_58) == 0)
{
obj* x_62; unsigned char x_63; obj* x_65; 
lean::dec(x_58);
x_62 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__6;
x_63 = 1;
lean::inc(x_62);
x_65 = l_lean_kvmap_set__bool(x_56, x_62, x_63);
x_17 = x_65;
goto lbl_18;
}
else
{
obj* x_67; unsigned char x_68; obj* x_70; 
lean::dec(x_58);
x_67 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__7;
x_68 = 1;
lean::inc(x_67);
x_70 = l_lean_kvmap_set__bool(x_56, x_67, x_68);
x_17 = x_70;
goto lbl_18;
}
}
}
}
lbl_18:
{
obj* x_71; obj* x_73; obj* x_74; obj* x_76; 
x_71 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__1;
lean::inc(x_71);
x_73 = l_lean_kvmap_set__bool(x_17, x_71, x_10);
x_74 = l_lean_elaborator_decl__modifiers__to__pexpr___closed__2;
lean::inc(x_74);
x_76 = l_lean_kvmap_set__bool(x_73, x_74, x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_78; 
lean::dec(x_14);
x_78 = l_lean_elaborator_attrs__to__pexpr(x_3, x_1, x_2);
if (lean::obj_tag(x_78) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_76);
x_80 = lean::cnstr_get(x_78, 0);
lean::inc(x_80);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_82 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 x_82 = x_78;
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
obj* x_84; obj* x_86; obj* x_87; obj* x_89; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_84 = lean::cnstr_get(x_78, 0);
lean::inc(x_84);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 x_86 = x_78;
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
x_92 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_92, 0, x_76);
lean::cnstr_set(x_92, 1, x_87);
if (lean::is_scalar(x_91)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_91;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_89);
if (lean::is_scalar(x_86)) {
 x_94 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_94 = x_86;
}
lean::cnstr_set(x_94, 0, x_93);
return x_94;
}
}
else
{
obj* x_96; obj* x_99; obj* x_102; 
lean::dec(x_3);
x_96 = lean::cnstr_get(x_14, 0);
lean::inc(x_96);
lean::dec(x_14);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::dec(x_96);
x_102 = l_lean_elaborator_attrs__to__pexpr(x_99, x_1, x_2);
if (lean::obj_tag(x_102) == 0)
{
obj* x_104; obj* x_106; obj* x_107; 
lean::dec(x_76);
x_104 = lean::cnstr_get(x_102, 0);
lean::inc(x_104);
if (lean::is_shared(x_102)) {
 lean::dec(x_102);
 x_106 = lean::box(0);
} else {
 lean::cnstr_release(x_102, 0);
 x_106 = x_102;
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
x_108 = lean::cnstr_get(x_102, 0);
lean::inc(x_108);
if (lean::is_shared(x_102)) {
 lean::dec(x_102);
 x_110 = lean::box(0);
} else {
 lean::cnstr_release(x_102, 0);
 x_110 = x_102;
}
x_111 = lean::cnstr_get(x_108, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_108, 1);
lean::inc(x_113);
if (lean::is_shared(x_108)) {
 lean::dec(x_108);
 x_115 = lean::box(0);
} else {
 lean::cnstr_release(x_108, 0);
 lean::cnstr_release(x_108, 1);
 x_115 = x_108;
}
x_116 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_116, 0, x_76);
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
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("noncomputable");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("meta");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; unsigned char x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("private");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = 1;
x_5 = l_lean_kvmap_set__bool(x_0, x_3, x_4);
return x_5;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; unsigned char x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("protected");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
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
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("private");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_decl__modifiers__to__pexpr___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("protected");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
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
obj* x_8; obj* x_9; 
lean::dec(x_4);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l_list_map___main___at_lean_elaborator_ident__univ__params__to__pexpr___spec__1(x_13);
x_17 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_17, 0, x_3);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* l_list_map___main___at_lean_elaborator_ident__univ__params__to__pexpr___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = l_list_map___main___at_lean_elaborator_ident__univ__params__to__pexpr___spec__1(x_5);
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
obj* _init_l_lean_elaborator_locally___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg___lambda__1), 1, 0);
return x_0;
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
obj* l_lean_elaborator_locally(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_locally___rarg), 3, 0);
return x_2;
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
obj* l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_25; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
x_13 = l_lean_parser_term_simple__binder_view_to__binder__info___main(x_8);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_16, 1);
lean::inc(x_21);
lean::dec(x_16);
lean::inc(x_1);
x_25 = l_lean_elaborator_to__pexpr___main(x_21, x_1, x_2);
if (lean::obj_tag(x_25) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_12);
lean::dec(x_14);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_18);
lean::dec(x_19);
x_32 = lean::cnstr_get(x_25, 0);
lean::inc(x_32);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 x_34 = x_25;
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_44; 
x_36 = lean::cnstr_get(x_25, 0);
lean::inc(x_36);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 x_38 = x_25;
}
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
lean::dec(x_36);
x_44 = l_list_mmap___main___at_lean_elaborator_simple__binders__to__pexpr___spec__1(x_10, x_1, x_41);
if (lean::obj_tag(x_44) == 0)
{
obj* x_50; obj* x_53; 
lean::dec(x_12);
lean::dec(x_14);
lean::dec(x_18);
lean::dec(x_19);
lean::dec(x_39);
x_50 = lean::cnstr_get(x_44, 0);
lean::inc(x_50);
lean::dec(x_44);
if (lean::is_scalar(x_38)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_38;
}
lean::cnstr_set(x_53, 0, x_50);
return x_53;
}
else
{
obj* x_54; obj* x_57; obj* x_59; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_54 = lean::cnstr_get(x_44, 0);
lean::inc(x_54);
lean::dec(x_44);
x_57 = lean::cnstr_get(x_54, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_54, 1);
lean::inc(x_59);
lean::dec(x_54);
x_62 = l_lean_elaborator_mangle__ident(x_19);
lean::inc(x_62);
x_64 = lean_expr_local(x_62, x_62, x_39, x_14);
if (lean::is_scalar(x_12)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_12;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_57);
if (lean::is_scalar(x_18)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_18;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_59);
if (lean::is_scalar(x_38)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_38;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
}
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
lean::dec(x_30);
lean::dec(x_12);
lean::dec(x_17);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
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
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_3);
x_57 = lean::alloc_cnstr(9, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
if (lean::obj_tag(x_6) == 0)
{
obj* x_61; obj* x_63; 
x_61 = l_lean_expander_get__opt__type___main(x_17);
lean::inc(x_4);
x_63 = l_lean_elaborator_to__pexpr___main(x_61, x_4, x_52);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_6);
if (lean::obj_tag(x_63) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_30);
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_55);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_57);
x_75 = lean::cnstr_get(x_63, 0);
lean::inc(x_75);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_77 = x_63;
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
obj* x_79; 
x_79 = lean::cnstr_get(x_63, 0);
lean::inc(x_79);
lean::dec(x_63);
x_58 = x_55;
x_59 = x_79;
goto lbl_60;
}
}
else
{
obj* x_82; 
x_82 = lean::cnstr_get(x_6, 0);
lean::inc(x_82);
lean::dec(x_6);
if (lean::obj_tag(x_63) == 0)
{
obj* x_96; obj* x_98; obj* x_99; 
lean::dec(x_30);
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_55);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_57);
lean::dec(x_82);
x_96 = lean::cnstr_get(x_63, 0);
lean::inc(x_96);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_98 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_98 = x_63;
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
obj* x_100; obj* x_103; obj* x_106; 
x_100 = lean::cnstr_get(x_63, 0);
lean::inc(x_100);
lean::dec(x_63);
x_103 = lean::cnstr_get(x_82, 1);
lean::inc(x_103);
lean::dec(x_82);
x_106 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(x_103);
x_58 = x_106;
x_59 = x_100;
goto lbl_60;
}
}
}
else
{
obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_127; obj* x_128; obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_137; obj* x_140; obj* x_141; obj* x_143; obj* x_145; obj* x_147; obj* x_149; obj* x_151; obj* x_154; obj* x_155; obj* x_157; 
x_107 = lean::cnstr_get(x_6, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_52, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_52, 1);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_52, 2);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_52, 3);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_52, 4);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_117, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_117, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_107, 1);
lean::inc(x_123);
lean::dec(x_107);
lean::inc(x_123);
x_127 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(x_123);
x_128 = l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(x_121, x_127);
x_129 = lean::cnstr_get(x_117, 2);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_117, 3);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_117, 4);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_117, 5);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_117, 6);
lean::inc(x_137);
lean::dec(x_117);
x_140 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_140, 0, x_119);
lean::cnstr_set(x_140, 1, x_128);
lean::cnstr_set(x_140, 2, x_129);
lean::cnstr_set(x_140, 3, x_131);
lean::cnstr_set(x_140, 4, x_133);
lean::cnstr_set(x_140, 5, x_135);
lean::cnstr_set(x_140, 6, x_137);
x_141 = lean::cnstr_get(x_52, 5);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_52, 6);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_52, 7);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_52, 8);
lean::inc(x_147);
x_149 = lean::cnstr_get(x_52, 9);
lean::inc(x_149);
x_151 = lean::cnstr_get(x_52, 10);
lean::inc(x_151);
lean::dec(x_52);
x_154 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_154, 0, x_109);
lean::cnstr_set(x_154, 1, x_111);
lean::cnstr_set(x_154, 2, x_113);
lean::cnstr_set(x_154, 3, x_115);
lean::cnstr_set(x_154, 4, x_140);
lean::cnstr_set(x_154, 5, x_141);
lean::cnstr_set(x_154, 6, x_143);
lean::cnstr_set(x_154, 7, x_145);
lean::cnstr_set(x_154, 8, x_147);
lean::cnstr_set(x_154, 9, x_149);
lean::cnstr_set(x_154, 10, x_151);
x_155 = l_lean_expander_get__opt__type___main(x_17);
lean::inc(x_4);
x_157 = l_lean_elaborator_to__pexpr___main(x_155, x_4, x_154);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_6);
lean::dec(x_123);
if (lean::obj_tag(x_157) == 0)
{
obj* x_170; obj* x_172; obj* x_173; 
lean::dec(x_30);
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_55);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_57);
x_170 = lean::cnstr_get(x_157, 0);
lean::inc(x_170);
if (lean::is_shared(x_157)) {
 lean::dec(x_157);
 x_172 = lean::box(0);
} else {
 lean::cnstr_release(x_157, 0);
 x_172 = x_157;
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_170);
return x_173;
}
else
{
obj* x_174; 
x_174 = lean::cnstr_get(x_157, 0);
lean::inc(x_174);
lean::dec(x_157);
x_58 = x_55;
x_59 = x_174;
goto lbl_60;
}
}
else
{
lean::dec(x_6);
if (lean::obj_tag(x_157) == 0)
{
obj* x_189; obj* x_191; obj* x_192; 
lean::dec(x_30);
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_123);
lean::dec(x_54);
lean::dec(x_55);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_57);
x_189 = lean::cnstr_get(x_157, 0);
lean::inc(x_189);
if (lean::is_shared(x_157)) {
 lean::dec(x_157);
 x_191 = lean::box(0);
} else {
 lean::cnstr_release(x_157, 0);
 x_191 = x_157;
}
if (lean::is_scalar(x_191)) {
 x_192 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_192 = x_191;
}
lean::cnstr_set(x_192, 0, x_189);
return x_192;
}
else
{
obj* x_193; obj* x_196; 
x_193 = lean::cnstr_get(x_157, 0);
lean::inc(x_193);
lean::dec(x_157);
x_196 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(x_123);
x_58 = x_196;
x_59 = x_193;
goto lbl_60;
}
}
}
lbl_60:
{
obj* x_197; obj* x_199; obj* x_202; obj* x_203; obj* x_205; unsigned char x_206; obj* x_207; obj* x_210; obj* x_212; obj* x_213; obj* x_215; obj* x_216; 
x_197 = lean::cnstr_get(x_59, 0);
lean::inc(x_197);
x_199 = lean::cnstr_get(x_59, 1);
lean::inc(x_199);
lean::dec(x_59);
x_202 = l_lean_elaborator_names__to__pexpr(x_58);
x_203 = lean::cnstr_get(x_8, 0);
lean::inc(x_203);
x_205 = l_lean_elaborator_mangle__ident(x_203);
x_206 = 4;
x_207 = lean::box(x_206);
lean::inc(x_197);
lean::inc(x_205);
x_210 = lean_expr_local(x_205, x_205, x_197, x_207);
lean::inc(x_55);
x_212 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_212, 0, x_210);
lean::cnstr_set(x_212, 1, x_55);
x_213 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_213);
x_215 = l_lean_expr_mk__capp(x_213, x_212);
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_221; obj* x_224; obj* x_228; 
lean::dec(x_8);
lean::dec(x_54);
lean::dec(x_197);
x_221 = lean::cnstr_get(x_12, 0);
lean::inc(x_221);
lean::dec(x_12);
x_224 = lean::cnstr_get(x_221, 1);
lean::inc(x_224);
lean::dec(x_221);
lean::inc(x_4);
x_228 = l_lean_elaborator_to__pexpr___main(x_224, x_4, x_199);
if (lean::obj_tag(x_228) == 0)
{
obj* x_238; obj* x_240; obj* x_241; 
lean::dec(x_30);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_55);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_57);
lean::dec(x_202);
lean::dec(x_215);
x_238 = lean::cnstr_get(x_228, 0);
lean::inc(x_238);
if (lean::is_shared(x_228)) {
 lean::dec(x_228);
 x_240 = lean::box(0);
} else {
 lean::cnstr_release(x_228, 0);
 x_240 = x_228;
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
obj* x_242; 
x_242 = lean::cnstr_get(x_228, 0);
lean::inc(x_242);
lean::dec(x_228);
x_216 = x_242;
goto lbl_217;
}
}
case 1:
{
obj* x_248; obj* x_249; 
lean::dec(x_12);
lean::dec(x_8);
lean::inc(x_55);
x_248 = l_lean_elaborator_mk__eqns(x_197, x_55);
if (lean::is_scalar(x_54)) {
 x_249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_249 = x_54;
}
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_199);
x_216 = x_249;
goto lbl_217;
}
default:
{
obj* x_250; obj* x_254; 
x_250 = lean::cnstr_get(x_12, 0);
lean::inc(x_250);
lean::dec(x_12);
lean::inc(x_4);
x_254 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_8, x_250, x_4, x_199);
if (lean::obj_tag(x_254) == 0)
{
obj* x_266; obj* x_268; obj* x_269; 
lean::dec(x_30);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_55);
lean::dec(x_49);
lean::dec(x_50);
lean::dec(x_57);
lean::dec(x_202);
lean::dec(x_197);
lean::dec(x_215);
x_266 = lean::cnstr_get(x_254, 0);
lean::inc(x_266);
if (lean::is_shared(x_254)) {
 lean::dec(x_254);
 x_268 = lean::box(0);
} else {
 lean::cnstr_release(x_254, 0);
 x_268 = x_254;
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
obj* x_270; obj* x_273; obj* x_275; obj* x_278; obj* x_279; 
x_270 = lean::cnstr_get(x_254, 0);
lean::inc(x_270);
lean::dec(x_254);
x_273 = lean::cnstr_get(x_270, 0);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_270, 1);
lean::inc(x_275);
lean::dec(x_270);
x_278 = l_lean_elaborator_mk__eqns(x_197, x_273);
if (lean::is_scalar(x_54)) {
 x_279 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_279 = x_54;
}
lean::cnstr_set(x_279, 0, x_278);
lean::cnstr_set(x_279, 1, x_275);
x_216 = x_279;
goto lbl_217;
}
}
}
lbl_217:
{
obj* x_280; obj* x_282; obj* x_286; 
x_280 = lean::cnstr_get(x_216, 0);
lean::inc(x_280);
x_282 = lean::cnstr_get(x_216, 1);
lean::inc(x_282);
lean::dec(x_216);
lean::inc(x_4);
x_286 = l_lean_elaborator_simple__binders__to__pexpr(x_30, x_4, x_282);
if (lean::obj_tag(x_286) == 0)
{
obj* x_295; obj* x_298; 
lean::dec(x_280);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_55);
lean::dec(x_50);
lean::dec(x_57);
lean::dec(x_202);
lean::dec(x_215);
x_295 = lean::cnstr_get(x_286, 0);
lean::inc(x_295);
lean::dec(x_286);
if (lean::is_scalar(x_49)) {
 x_298 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_298 = x_49;
}
lean::cnstr_set(x_298, 0, x_295);
return x_298;
}
else
{
obj* x_300; obj* x_303; obj* x_305; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_315; obj* x_316; obj* x_318; obj* x_319; 
lean::dec(x_49);
x_300 = lean::cnstr_get(x_286, 0);
lean::inc(x_300);
lean::dec(x_286);
x_303 = lean::cnstr_get(x_300, 0);
lean::inc(x_303);
x_305 = lean::cnstr_get(x_300, 1);
lean::inc(x_305);
lean::dec(x_300);
x_308 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_308, 0, x_280);
lean::cnstr_set(x_308, 1, x_55);
x_309 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_309, 0, x_303);
lean::cnstr_set(x_309, 1, x_308);
x_310 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_310, 0, x_215);
lean::cnstr_set(x_310, 1, x_309);
x_311 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_311, 0, x_202);
lean::cnstr_set(x_311, 1, x_310);
x_312 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_312, 0, x_57);
lean::cnstr_set(x_312, 1, x_311);
x_313 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_313, 0, x_50);
lean::cnstr_set(x_313, 1, x_312);
lean::inc(x_213);
x_315 = l_lean_expr_mk__capp(x_213, x_313);
x_316 = l_lean_elaborator_elab__def__like___closed__2;
lean::inc(x_316);
x_318 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_318, 0, x_316);
lean::cnstr_set(x_318, 1, x_315);
x_319 = l_lean_elaborator_old__elab__command(x_0, x_318, x_4, x_305);
return x_319;
}
}
}
}
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
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string("defs");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
}
}
obj* l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
lean::inc(x_1);
x_14 = l_lean_elaborator_to__pexpr___main(x_8, x_1, x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_20 = x_14;
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
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_24 = x_14;
}
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_29 = x_22;
}
x_30 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_10, x_1, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_37; 
lean::dec(x_12);
lean::dec(x_25);
lean::dec(x_29);
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
if (lean::is_scalar(x_24)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_24;
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
if (lean::is_scalar(x_12)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_12;
}
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_41);
if (lean::is_scalar(x_29)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_29;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_24)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_24;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
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
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_18; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::inc(x_2);
x_18 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__1(x_15, x_2, x_3);
if (lean::obj_tag(x_18) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_18, 0);
lean::inc(x_24);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_26 = x_18;
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
obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_40; 
x_28 = lean::cnstr_get(x_18, 0);
lean::inc(x_28);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_30 = x_18;
}
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_release(x_28, 1);
 x_35 = x_28;
}
x_36 = lean::cnstr_get(x_10, 3);
lean::inc(x_36);
lean::dec(x_10);
lean::inc(x_2);
x_40 = l_lean_elaborator_to__pexpr___main(x_36, x_2, x_33);
if (lean::obj_tag(x_40) == 0)
{
obj* x_47; obj* x_50; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_35);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_31);
x_47 = lean::cnstr_get(x_40, 0);
lean::inc(x_47);
lean::dec(x_40);
if (lean::is_scalar(x_30)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_30;
}
lean::cnstr_set(x_50, 0, x_47);
return x_50;
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; 
x_51 = lean::cnstr_get(x_40, 0);
lean::inc(x_51);
lean::dec(x_40);
x_54 = lean::cnstr_get(x_0, 0);
lean::inc(x_54);
x_56 = l_lean_elaborator_mangle__ident(x_54);
x_57 = lean::cnstr_get(x_51, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_51, 1);
lean::inc(x_59);
if (lean::is_shared(x_51)) {
 lean::dec(x_51);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_61 = x_51;
}
x_62 = l_list_mmap___main___at_lean_elaborator_elab__def__like___spec__2(x_0, x_12, x_2, x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_69; obj* x_72; 
lean::dec(x_14);
lean::dec(x_35);
lean::dec(x_57);
lean::dec(x_31);
lean::dec(x_56);
lean::dec(x_61);
x_69 = lean::cnstr_get(x_62, 0);
lean::inc(x_69);
lean::dec(x_62);
if (lean::is_scalar(x_30)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_30;
}
lean::cnstr_set(x_72, 0, x_69);
return x_72;
}
else
{
obj* x_73; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_73 = lean::cnstr_get(x_62, 0);
lean::inc(x_73);
lean::dec(x_62);
x_76 = lean::cnstr_get(x_73, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_73, 1);
lean::inc(x_78);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 x_80 = x_73;
}
if (lean::is_scalar(x_35)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_35;
}
lean::cnstr_set(x_81, 0, x_31);
lean::cnstr_set(x_81, 1, x_57);
if (lean::is_scalar(x_61)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_61;
}
lean::cnstr_set(x_82, 0, x_56);
lean::cnstr_set(x_82, 1, x_81);
if (lean::is_scalar(x_14)) {
 x_83 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_83 = x_14;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_76);
if (lean::is_scalar(x_80)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_80;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_78);
if (lean::is_scalar(x_30)) {
 x_85 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_85 = x_30;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__3(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__5(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_foldl___main___at_lean_elaborator_elab__def__like___spec__6(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
lean::inc(x_3);
x_9 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_9, 0, x_3);
x_10 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_0, x_3, x_9);
x_0 = x_10;
x_1 = x_5;
goto _start;
}
}
}
obj* l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = l_list_map___main___at_lean_elaborator_elab__def__like___spec__7(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_lean_elaborator_infer__mod__to__pexpr(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_elaborator_infer__mod__to__pexpr___closed__1;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; 
lean::dec(x_4);
x_8 = l_lean_elaborator_infer__mod__to__pexpr___closed__2;
lean::inc(x_8);
return x_8;
}
else
{
obj* x_11; 
lean::dec(x_4);
x_11 = l_lean_elaborator_infer__mod__to__pexpr___closed__3;
lean::inc(x_11);
return x_11;
}
}
}
}
obj* _init_l_lean_elaborator_infer__mod__to__pexpr___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(9, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_infer__mod__to__pexpr___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(9, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_elaborator_infer__mod__to__pexpr___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(2u);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(9, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
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
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_17 = lean::cnstr_get(x_10, 3);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_17, 1);
lean::inc(x_21);
lean::dec(x_17);
if (lean::obj_tag(x_19) == 0)
{
obj* x_27; obj* x_31; 
lean::dec(x_10);
lean::dec(x_19);
lean::dec(x_21);
x_27 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_27);
lean::inc(x_0);
x_31 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_27, x_2, x_3);
if (lean::obj_tag(x_31) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_36 = lean::cnstr_get(x_31, 0);
lean::inc(x_36);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 x_38 = x_31;
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
obj* x_40; 
x_40 = lean::cnstr_get(x_31, 0);
lean::inc(x_40);
lean::dec(x_31);
x_15 = x_40;
goto lbl_16;
}
}
else
{
obj* x_43; 
x_43 = lean::cnstr_get(x_19, 0);
lean::inc(x_43);
lean::dec(x_19);
if (lean::obj_tag(x_43) == 0)
{
lean::dec(x_43);
if (lean::obj_tag(x_21) == 0)
{
obj* x_49; obj* x_53; 
lean::dec(x_10);
lean::dec(x_21);
x_49 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_49);
lean::inc(x_0);
x_53 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_49, x_2, x_3);
if (lean::obj_tag(x_53) == 0)
{
obj* x_58; obj* x_60; obj* x_61; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_58 = lean::cnstr_get(x_53, 0);
lean::inc(x_58);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_60 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_60 = x_53;
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
obj* x_62; 
x_62 = lean::cnstr_get(x_53, 0);
lean::inc(x_62);
lean::dec(x_53);
x_15 = x_62;
goto lbl_16;
}
}
else
{
obj* x_65; obj* x_68; obj* x_72; 
x_65 = lean::cnstr_get(x_21, 0);
lean::inc(x_65);
lean::dec(x_21);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
lean::dec(x_65);
lean::inc(x_2);
x_72 = l_lean_elaborator_to__pexpr___main(x_68, x_2, x_3);
if (lean::obj_tag(x_72) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_2);
x_78 = lean::cnstr_get(x_72, 0);
lean::inc(x_78);
if (lean::is_shared(x_72)) {
 lean::dec(x_72);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_72, 0);
 x_80 = x_72;
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
obj* x_82; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_93; unsigned char x_94; obj* x_95; obj* x_97; obj* x_98; 
x_82 = lean::cnstr_get(x_72, 0);
lean::inc(x_82);
lean::dec(x_72);
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_82, 1);
lean::inc(x_87);
if (lean::is_shared(x_82)) {
 lean::dec(x_82);
 x_89 = lean::box(0);
} else {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 x_89 = x_82;
}
x_90 = lean::cnstr_get(x_10, 1);
lean::inc(x_90);
lean::dec(x_10);
x_93 = l_lean_elaborator_mangle__ident(x_90);
x_94 = 0;
x_95 = lean::box(x_94);
lean::inc(x_93);
x_97 = lean_expr_local(x_93, x_93, x_85, x_95);
if (lean::is_scalar(x_89)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_89;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_87);
x_15 = x_98;
goto lbl_16;
}
}
}
else
{
obj* x_102; obj* x_106; 
lean::dec(x_10);
lean::dec(x_21);
lean::dec(x_43);
x_102 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_102);
lean::inc(x_0);
x_106 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_102, x_2, x_3);
if (lean::obj_tag(x_106) == 0)
{
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_111 = lean::cnstr_get(x_106, 0);
lean::inc(x_111);
if (lean::is_shared(x_106)) {
 lean::dec(x_106);
 x_113 = lean::box(0);
} else {
 lean::cnstr_release(x_106, 0);
 x_113 = x_106;
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
obj* x_115; 
x_115 = lean::cnstr_get(x_106, 0);
lean::inc(x_115);
lean::dec(x_106);
x_15 = x_115;
goto lbl_16;
}
}
}
lbl_16:
{
obj* x_118; obj* x_120; obj* x_122; obj* x_123; 
x_118 = lean::cnstr_get(x_15, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_15, 1);
lean::inc(x_120);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_122 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_122 = x_15;
}
x_123 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_12, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_127; obj* x_129; obj* x_130; 
lean::dec(x_14);
lean::dec(x_122);
lean::dec(x_118);
x_127 = lean::cnstr_get(x_123, 0);
lean::inc(x_127);
if (lean::is_shared(x_123)) {
 lean::dec(x_123);
 x_129 = lean::box(0);
} else {
 lean::cnstr_release(x_123, 0);
 x_129 = x_123;
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
obj* x_131; obj* x_133; obj* x_134; obj* x_136; obj* x_139; obj* x_140; obj* x_141; 
x_131 = lean::cnstr_get(x_123, 0);
lean::inc(x_131);
if (lean::is_shared(x_123)) {
 lean::dec(x_123);
 x_133 = lean::box(0);
} else {
 lean::cnstr_release(x_123, 0);
 x_133 = x_123;
}
x_134 = lean::cnstr_get(x_131, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_131, 1);
lean::inc(x_136);
lean::dec(x_131);
if (lean::is_scalar(x_14)) {
 x_139 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_139 = x_14;
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
if (lean::is_scalar(x_133)) {
 x_141 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_141 = x_133;
}
lean::cnstr_set(x_141, 0, x_140);
return x_141;
}
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
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
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
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_lean_elaborator_infer__mod__to__pexpr(x_8);
x_12 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_7;
}
lean::cnstr_set(x_13, 0, x_11);
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
lean::inc(x_3);
x_9 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_9, 0, x_3);
x_10 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_0, x_3, x_9);
x_0 = x_10;
x_1 = x_5;
goto _start;
}
}
}
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
lean::inc(x_1);
x_17 = l_lean_elaborator_to__pexpr___main(x_13, x_1, x_2);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_23 = x_17;
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
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_27 = x_17;
}
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_32 = x_25;
}
x_33 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_10, x_1, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_40; 
lean::dec(x_12);
lean::dec(x_28);
lean::dec(x_32);
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_27;
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_33, 0);
lean::inc(x_41);
lean::dec(x_33);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
lean::dec(x_41);
if (lean::is_scalar(x_12)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_12;
}
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_44);
if (lean::is_scalar(x_32)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_32;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
if (lean::is_scalar(x_27)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_27;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_17; obj* x_20; 
x_17 = lean::cnstr_get(x_10, 0);
lean::inc(x_17);
lean::dec(x_10);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; obj* x_28; 
lean::dec(x_20);
x_24 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_2);
lean::inc(x_24);
lean::inc(x_0);
x_28 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_24, x_2, x_3);
if (lean::obj_tag(x_28) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_33 = lean::cnstr_get(x_28, 0);
lean::inc(x_33);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 x_35 = x_28;
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
obj* x_37; 
x_37 = lean::cnstr_get(x_28, 0);
lean::inc(x_37);
lean::dec(x_28);
x_15 = x_37;
goto lbl_16;
}
}
else
{
obj* x_40; unsigned char x_43; obj* x_44; obj* x_45; obj* x_46; 
x_40 = lean::cnstr_get(x_20, 0);
lean::inc(x_40);
lean::dec(x_20);
x_43 = 0;
x_44 = lean::box(x_43);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_40);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_3);
x_15 = x_46;
goto lbl_16;
}
}
case 1:
{
obj* x_47; obj* x_50; unsigned char x_53; obj* x_54; obj* x_55; obj* x_56; 
x_47 = lean::cnstr_get(x_10, 0);
lean::inc(x_47);
lean::dec(x_10);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
lean::dec(x_47);
x_53 = 1;
x_54 = lean::box(x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_50);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_3);
x_15 = x_56;
goto lbl_16;
}
case 2:
{
obj* x_57; obj* x_60; unsigned char x_63; obj* x_64; obj* x_65; obj* x_66; 
x_57 = lean::cnstr_get(x_10, 0);
lean::inc(x_57);
lean::dec(x_10);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
x_63 = 2;
x_64 = lean::box(x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_60);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_3);
x_15 = x_66;
goto lbl_16;
}
default:
{
obj* x_67; obj* x_70; unsigned char x_73; obj* x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_10, 0);
lean::inc(x_67);
lean::dec(x_10);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
x_73 = 3;
x_74 = lean::box(x_73);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_70);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_3);
x_15 = x_76;
goto lbl_16;
}
}
lbl_16:
{
obj* x_77; obj* x_79; obj* x_81; obj* x_82; obj* x_84; obj* x_87; obj* x_89; obj* x_92; obj* x_94; 
x_77 = lean::cnstr_get(x_15, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_15, 1);
lean::inc(x_79);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_81 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_81 = x_15;
}
x_82 = lean::cnstr_get(x_77, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_77, 1);
lean::inc(x_84);
lean::dec(x_77);
x_87 = lean::cnstr_get(x_84, 2);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_87, 1);
lean::inc(x_89);
lean::dec(x_87);
x_92 = l_lean_expander_get__opt__type___main(x_89);
lean::inc(x_2);
x_94 = l_lean_elaborator_to__pexpr___main(x_92, x_2, x_79);
if (lean::obj_tag(x_94) == 0)
{
obj* x_102; obj* x_104; obj* x_105; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_82);
lean::dec(x_81);
lean::dec(x_84);
x_102 = lean::cnstr_get(x_94, 0);
lean::inc(x_102);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 x_104 = x_94;
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
obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_114; 
x_106 = lean::cnstr_get(x_94, 0);
lean::inc(x_106);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_108 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 x_108 = x_94;
}
x_109 = lean::cnstr_get(x_106, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_106, 1);
lean::inc(x_111);
lean::dec(x_106);
x_114 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_12, x_2, x_111);
if (lean::obj_tag(x_114) == 0)
{
obj* x_120; obj* x_123; 
lean::dec(x_14);
lean::dec(x_82);
lean::dec(x_81);
lean::dec(x_84);
lean::dec(x_109);
x_120 = lean::cnstr_get(x_114, 0);
lean::inc(x_120);
lean::dec(x_114);
if (lean::is_scalar(x_108)) {
 x_123 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_123 = x_108;
}
lean::cnstr_set(x_123, 0, x_120);
return x_123;
}
else
{
obj* x_124; obj* x_127; obj* x_129; obj* x_132; obj* x_133; obj* x_137; obj* x_138; obj* x_140; obj* x_141; obj* x_142; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_152; obj* x_153; obj* x_154; obj* x_155; 
x_124 = lean::cnstr_get(x_114, 0);
lean::inc(x_124);
lean::dec(x_114);
x_127 = lean::cnstr_get(x_124, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_124, 1);
lean::inc(x_129);
lean::dec(x_124);
x_132 = l_lean_elaborator_mk__eqns___closed__1;
x_133 = l_lean_elaborator_dummy;
lean::inc(x_133);
lean::inc(x_132);
lean::inc(x_132);
x_137 = lean_expr_local(x_132, x_132, x_133, x_82);
x_138 = lean::cnstr_get(x_84, 0);
lean::inc(x_138);
x_140 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__8(x_138);
x_141 = l_lean_elaborator_names__to__pexpr(x_140);
x_142 = lean::cnstr_get(x_84, 1);
lean::inc(x_142);
lean::dec(x_84);
x_145 = l_lean_elaborator_infer__mod__to__pexpr(x_142);
x_146 = lean::box(0);
if (lean::is_scalar(x_14)) {
 x_147 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_147 = x_14;
}
lean::cnstr_set(x_147, 0, x_109);
lean::cnstr_set(x_147, 1, x_146);
x_148 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_148, 0, x_145);
lean::cnstr_set(x_148, 1, x_147);
x_149 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_149, 0, x_141);
lean::cnstr_set(x_149, 1, x_148);
x_150 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_150, 0, x_137);
lean::cnstr_set(x_150, 1, x_149);
lean::inc(x_132);
x_152 = l_lean_expr_mk__capp(x_132, x_150);
x_153 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_153, 0, x_152);
lean::cnstr_set(x_153, 1, x_127);
if (lean::is_scalar(x_81)) {
 x_154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_154 = x_81;
}
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_129);
if (lean::is_scalar(x_108)) {
 x_155 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_155 = x_108;
}
lean::cnstr_set(x_155, 0, x_154);
return x_155;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
lean::inc(x_3);
x_9 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_9, 0, x_3);
x_10 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_0, x_3, x_9);
x_0 = x_10;
x_1 = x_5;
goto _start;
}
}
}
obj* l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
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
lean::dec(x_96);
lean::dec(x_94);
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
obj* x_110; obj* x_114; 
lean::dec(x_106);
x_110 = lean::cnstr_get(x_11, 0);
lean::inc(x_110);
lean::dec(x_11);
lean::inc(x_1);
x_114 = l_lean_elaborator_decl__modifiers__to__pexpr(x_110, x_1, x_2);
if (lean::obj_tag(x_114) == 0)
{
obj* x_119; obj* x_121; obj* x_122; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_89);
lean::dec(x_96);
x_119 = lean::cnstr_get(x_114, 0);
lean::inc(x_119);
if (lean::is_shared(x_114)) {
 lean::dec(x_114);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_114, 0);
 x_121 = x_114;
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_119);
x_5 = x_122;
goto lbl_6;
}
else
{
obj* x_123; obj* x_125; obj* x_126; obj* x_128; obj* x_131; obj* x_135; 
x_123 = lean::cnstr_get(x_114, 0);
lean::inc(x_123);
if (lean::is_shared(x_114)) {
 lean::dec(x_114);
 x_125 = lean::box(0);
} else {
 lean::cnstr_release(x_114, 0);
 x_125 = x_114;
}
x_126 = lean::cnstr_get(x_123, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_123, 1);
lean::inc(x_128);
lean::dec(x_123);
x_131 = lean::cnstr_get(x_96, 1);
lean::inc(x_131);
lean::dec(x_96);
lean::inc(x_1);
x_135 = l_lean_elaborator_to__pexpr___main(x_131, x_1, x_128);
if (lean::obj_tag(x_135) == 0)
{
obj* x_140; obj* x_143; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_89);
lean::dec(x_126);
x_140 = lean::cnstr_get(x_135, 0);
lean::inc(x_140);
lean::dec(x_135);
if (lean::is_scalar(x_125)) {
 x_143 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_143 = x_125;
}
lean::cnstr_set(x_143, 0, x_140);
x_5 = x_143;
goto lbl_6;
}
else
{
obj* x_145; obj* x_148; obj* x_150; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_160; obj* x_161; obj* x_163; obj* x_164; 
lean::dec(x_125);
x_145 = lean::cnstr_get(x_135, 0);
lean::inc(x_145);
lean::dec(x_135);
x_148 = lean::cnstr_get(x_145, 0);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_145, 1);
lean::inc(x_150);
lean::dec(x_145);
x_153 = lean::box(0);
x_154 = l_lean_elaborator_ident__univ__params__to__pexpr(x_89);
x_155 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_155, 0, x_148);
lean::cnstr_set(x_155, 1, x_153);
x_156 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_156, 0, x_154);
lean::cnstr_set(x_156, 1, x_155);
x_157 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_157, 0, x_126);
lean::cnstr_set(x_157, 1, x_156);
x_158 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_158);
x_160 = l_lean_expr_mk__capp(x_158, x_157);
x_161 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__3;
lean::inc(x_161);
x_163 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_163, 0, x_161);
lean::cnstr_set(x_163, 1, x_160);
x_164 = l_lean_elaborator_old__elab__command(x_0, x_163, x_1, x_150);
x_5 = x_164;
goto lbl_6;
}
}
}
else
{
obj* x_169; obj* x_171; 
lean::dec(x_11);
lean::dec(x_89);
lean::dec(x_106);
lean::dec(x_96);
x_169 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_169);
x_171 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_169, x_1, x_2);
x_5 = x_171;
goto lbl_6;
}
}
}
case 4:
{
obj* x_172; obj* x_175; obj* x_177; obj* x_179; obj* x_181; obj* x_183; 
x_172 = lean::cnstr_get(x_12, 0);
lean::inc(x_172);
lean::dec(x_12);
x_175 = lean::cnstr_get(x_172, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_172, 2);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_172, 3);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_172, 4);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_172, 6);
lean::inc(x_183);
lean::dec(x_172);
if (lean::obj_tag(x_175) == 0)
{
obj* x_187; obj* x_189; 
lean::dec(x_175);
x_187 = lean::cnstr_get(x_181, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_181, 1);
lean::inc(x_189);
lean::dec(x_181);
if (lean::obj_tag(x_187) == 0)
{
obj* x_198; obj* x_200; 
lean::dec(x_189);
lean::dec(x_187);
lean::dec(x_183);
lean::dec(x_179);
lean::dec(x_177);
lean::dec(x_11);
x_198 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_198);
x_200 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_198, x_1, x_2);
x_5 = x_200;
goto lbl_6;
}
else
{
obj* x_201; obj* x_204; obj* x_209; 
x_201 = lean::cnstr_get(x_187, 0);
lean::inc(x_201);
lean::dec(x_187);
x_204 = lean::cnstr_get(x_11, 0);
lean::inc(x_204);
lean::dec(x_11);
lean::inc(x_1);
lean::inc(x_204);
x_209 = l_lean_elaborator_decl__modifiers__to__pexpr(x_204, x_1, x_2);
if (lean::obj_tag(x_209) == 0)
{
obj* x_218; obj* x_220; obj* x_221; 
lean::dec(x_204);
lean::dec(x_189);
lean::dec(x_201);
lean::dec(x_183);
lean::dec(x_179);
lean::dec(x_177);
lean::dec(x_1);
lean::dec(x_0);
x_218 = lean::cnstr_get(x_209, 0);
lean::inc(x_218);
if (lean::is_shared(x_209)) {
 lean::dec(x_209);
 x_220 = lean::box(0);
} else {
 lean::cnstr_release(x_209, 0);
 x_220 = x_209;
}
if (lean::is_scalar(x_220)) {
 x_221 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_221 = x_220;
}
lean::cnstr_set(x_221, 0, x_218);
x_5 = x_221;
goto lbl_6;
}
else
{
obj* x_222; obj* x_224; obj* x_225; obj* x_227; obj* x_230; obj* x_231; obj* x_233; 
x_222 = lean::cnstr_get(x_209, 0);
lean::inc(x_222);
if (lean::is_shared(x_209)) {
 lean::dec(x_209);
 x_224 = lean::box(0);
} else {
 lean::cnstr_release(x_209, 0);
 x_224 = x_209;
}
x_225 = lean::cnstr_get(x_222, 0);
lean::inc(x_225);
x_227 = lean::cnstr_get(x_222, 1);
lean::inc(x_227);
lean::dec(x_222);
x_230 = lean::box(0);
x_233 = lean::cnstr_get(x_204, 1);
lean::inc(x_233);
lean::dec(x_204);
if (lean::obj_tag(x_233) == 0)
{
lean::dec(x_233);
x_231 = x_230;
goto lbl_232;
}
else
{
obj* x_237; obj* x_240; 
x_237 = lean::cnstr_get(x_233, 0);
lean::inc(x_237);
lean::dec(x_233);
x_240 = lean::cnstr_get(x_237, 1);
lean::inc(x_240);
lean::dec(x_237);
x_231 = x_240;
goto lbl_232;
}
lbl_232:
{
obj* x_244; 
lean::inc(x_1);
x_244 = l_lean_elaborator_attrs__to__pexpr(x_231, x_1, x_227);
if (lean::obj_tag(x_244) == 0)
{
obj* x_254; obj* x_257; 
lean::dec(x_189);
lean::dec(x_201);
lean::dec(x_183);
lean::dec(x_179);
lean::dec(x_177);
lean::dec(x_230);
lean::dec(x_225);
lean::dec(x_1);
lean::dec(x_0);
x_254 = lean::cnstr_get(x_244, 0);
lean::inc(x_254);
lean::dec(x_244);
if (lean::is_scalar(x_224)) {
 x_257 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_257 = x_224;
}
lean::cnstr_set(x_257, 0, x_254);
x_5 = x_257;
goto lbl_6;
}
else
{
obj* x_258; obj* x_260; obj* x_261; obj* x_263; obj* x_267; obj* x_268; obj* x_270; obj* x_271; obj* x_272; 
x_258 = lean::cnstr_get(x_244, 0);
lean::inc(x_258);
if (lean::is_shared(x_244)) {
 lean::dec(x_244);
 x_260 = lean::box(0);
} else {
 lean::cnstr_release(x_244, 0);
 x_260 = x_244;
}
x_261 = lean::cnstr_get(x_258, 0);
lean::inc(x_261);
x_263 = lean::cnstr_get(x_258, 1);
lean::inc(x_263);
lean::dec(x_258);
lean::inc(x_230);
x_267 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_267, 0, x_261);
lean::cnstr_set(x_267, 1, x_230);
x_268 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_268);
x_270 = l_lean_expr_mk__capp(x_268, x_267);
if (lean::obj_tag(x_177) == 0)
{
obj* x_274; obj* x_276; 
x_274 = l_lean_expander_get__opt__type___main(x_189);
lean::inc(x_1);
x_276 = l_lean_elaborator_to__pexpr___main(x_274, x_1, x_263);
if (lean::obj_tag(x_177) == 0)
{
lean::dec(x_177);
if (lean::obj_tag(x_276) == 0)
{
obj* x_287; obj* x_290; 
lean::dec(x_270);
lean::dec(x_201);
lean::dec(x_183);
lean::dec(x_179);
lean::dec(x_230);
lean::dec(x_225);
lean::dec(x_224);
lean::dec(x_1);
lean::dec(x_0);
x_287 = lean::cnstr_get(x_276, 0);
lean::inc(x_287);
lean::dec(x_276);
if (lean::is_scalar(x_260)) {
 x_290 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_290 = x_260;
}
lean::cnstr_set(x_290, 0, x_287);
x_5 = x_290;
goto lbl_6;
}
else
{
obj* x_292; 
lean::dec(x_260);
x_292 = lean::cnstr_get(x_276, 0);
lean::inc(x_292);
lean::dec(x_276);
x_271 = x_230;
x_272 = x_292;
goto lbl_273;
}
}
else
{
obj* x_295; 
x_295 = lean::cnstr_get(x_177, 0);
lean::inc(x_295);
lean::dec(x_177);
if (lean::obj_tag(x_276) == 0)
{
obj* x_308; obj* x_311; 
lean::dec(x_270);
lean::dec(x_295);
lean::dec(x_201);
lean::dec(x_183);
lean::dec(x_179);
lean::dec(x_230);
lean::dec(x_225);
lean::dec(x_224);
lean::dec(x_1);
lean::dec(x_0);
x_308 = lean::cnstr_get(x_276, 0);
lean::inc(x_308);
lean::dec(x_276);
if (lean::is_scalar(x_260)) {
 x_311 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_311 = x_260;
}
lean::cnstr_set(x_311, 0, x_308);
x_5 = x_311;
goto lbl_6;
}
else
{
obj* x_313; obj* x_316; obj* x_319; 
lean::dec(x_260);
x_313 = lean::cnstr_get(x_276, 0);
lean::inc(x_313);
lean::dec(x_276);
x_316 = lean::cnstr_get(x_295, 1);
lean::inc(x_316);
lean::dec(x_295);
x_319 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__3(x_316);
x_271 = x_319;
x_272 = x_313;
goto lbl_273;
}
}
}
else
{
obj* x_320; obj* x_322; obj* x_324; obj* x_326; obj* x_328; obj* x_330; obj* x_332; obj* x_334; obj* x_336; obj* x_340; obj* x_341; obj* x_342; obj* x_344; obj* x_346; obj* x_348; obj* x_350; obj* x_353; obj* x_354; obj* x_356; obj* x_358; obj* x_360; obj* x_362; obj* x_364; obj* x_367; obj* x_368; obj* x_370; 
x_320 = lean::cnstr_get(x_177, 0);
lean::inc(x_320);
x_322 = lean::cnstr_get(x_263, 0);
lean::inc(x_322);
x_324 = lean::cnstr_get(x_263, 1);
lean::inc(x_324);
x_326 = lean::cnstr_get(x_263, 2);
lean::inc(x_326);
x_328 = lean::cnstr_get(x_263, 3);
lean::inc(x_328);
x_330 = lean::cnstr_get(x_263, 4);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_330, 0);
lean::inc(x_332);
x_334 = lean::cnstr_get(x_330, 1);
lean::inc(x_334);
x_336 = lean::cnstr_get(x_320, 1);
lean::inc(x_336);
lean::dec(x_320);
lean::inc(x_336);
x_340 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__4(x_336);
x_341 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__5(x_334, x_340);
x_342 = lean::cnstr_get(x_330, 2);
lean::inc(x_342);
x_344 = lean::cnstr_get(x_330, 3);
lean::inc(x_344);
x_346 = lean::cnstr_get(x_330, 4);
lean::inc(x_346);
x_348 = lean::cnstr_get(x_330, 5);
lean::inc(x_348);
x_350 = lean::cnstr_get(x_330, 6);
lean::inc(x_350);
lean::dec(x_330);
x_353 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_353, 0, x_332);
lean::cnstr_set(x_353, 1, x_341);
lean::cnstr_set(x_353, 2, x_342);
lean::cnstr_set(x_353, 3, x_344);
lean::cnstr_set(x_353, 4, x_346);
lean::cnstr_set(x_353, 5, x_348);
lean::cnstr_set(x_353, 6, x_350);
x_354 = lean::cnstr_get(x_263, 5);
lean::inc(x_354);
x_356 = lean::cnstr_get(x_263, 6);
lean::inc(x_356);
x_358 = lean::cnstr_get(x_263, 7);
lean::inc(x_358);
x_360 = lean::cnstr_get(x_263, 8);
lean::inc(x_360);
x_362 = lean::cnstr_get(x_263, 9);
lean::inc(x_362);
x_364 = lean::cnstr_get(x_263, 10);
lean::inc(x_364);
lean::dec(x_263);
x_367 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_367, 0, x_322);
lean::cnstr_set(x_367, 1, x_324);
lean::cnstr_set(x_367, 2, x_326);
lean::cnstr_set(x_367, 3, x_328);
lean::cnstr_set(x_367, 4, x_353);
lean::cnstr_set(x_367, 5, x_354);
lean::cnstr_set(x_367, 6, x_356);
lean::cnstr_set(x_367, 7, x_358);
lean::cnstr_set(x_367, 8, x_360);
lean::cnstr_set(x_367, 9, x_362);
lean::cnstr_set(x_367, 10, x_364);
x_368 = l_lean_expander_get__opt__type___main(x_189);
lean::inc(x_1);
x_370 = l_lean_elaborator_to__pexpr___main(x_368, x_1, x_367);
if (lean::obj_tag(x_177) == 0)
{
lean::dec(x_177);
lean::dec(x_336);
if (lean::obj_tag(x_370) == 0)
{
obj* x_382; obj* x_385; 
lean::dec(x_270);
lean::dec(x_201);
lean::dec(x_183);
lean::dec(x_179);
lean::dec(x_230);
lean::dec(x_225);
lean::dec(x_224);
lean::dec(x_1);
lean::dec(x_0);
x_382 = lean::cnstr_get(x_370, 0);
lean::inc(x_382);
lean::dec(x_370);
if (lean::is_scalar(x_260)) {
 x_385 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_385 = x_260;
}
lean::cnstr_set(x_385, 0, x_382);
x_5 = x_385;
goto lbl_6;
}
else
{
obj* x_387; 
lean::dec(x_260);
x_387 = lean::cnstr_get(x_370, 0);
lean::inc(x_387);
lean::dec(x_370);
x_271 = x_230;
x_272 = x_387;
goto lbl_273;
}
}
else
{
lean::dec(x_177);
if (lean::obj_tag(x_370) == 0)
{
obj* x_401; obj* x_404; 
lean::dec(x_270);
lean::dec(x_201);
lean::dec(x_183);
lean::dec(x_179);
lean::dec(x_230);
lean::dec(x_225);
lean::dec(x_224);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_336);
x_401 = lean::cnstr_get(x_370, 0);
lean::inc(x_401);
lean::dec(x_370);
if (lean::is_scalar(x_260)) {
 x_404 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_404 = x_260;
}
lean::cnstr_set(x_404, 0, x_401);
x_5 = x_404;
goto lbl_6;
}
else
{
obj* x_406; obj* x_409; 
lean::dec(x_260);
x_406 = lean::cnstr_get(x_370, 0);
lean::inc(x_406);
lean::dec(x_370);
x_409 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__6(x_336);
x_271 = x_409;
x_272 = x_406;
goto lbl_273;
}
}
}
lbl_273:
{
obj* x_410; obj* x_412; obj* x_416; 
x_410 = lean::cnstr_get(x_272, 0);
lean::inc(x_410);
x_412 = lean::cnstr_get(x_272, 1);
lean::inc(x_412);
lean::dec(x_272);
lean::inc(x_1);
x_416 = l_lean_elaborator_simple__binders__to__pexpr(x_201, x_1, x_412);
if (lean::obj_tag(x_416) == 0)
{
obj* x_426; obj* x_429; 
lean::dec(x_270);
lean::dec(x_183);
lean::dec(x_179);
lean::dec(x_230);
lean::dec(x_225);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_410);
lean::dec(x_271);
x_426 = lean::cnstr_get(x_416, 0);
lean::inc(x_426);
lean::dec(x_416);
if (lean::is_scalar(x_224)) {
 x_429 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_429 = x_224;
}
lean::cnstr_set(x_429, 0, x_426);
x_5 = x_429;
goto lbl_6;
}
else
{
obj* x_430; obj* x_433; obj* x_435; obj* x_441; 
x_430 = lean::cnstr_get(x_416, 0);
lean::inc(x_430);
lean::dec(x_416);
x_433 = lean::cnstr_get(x_430, 0);
lean::inc(x_433);
x_435 = lean::cnstr_get(x_430, 1);
lean::inc(x_435);
lean::dec(x_430);
lean::inc(x_1);
lean::inc(x_183);
lean::inc(x_0);
x_441 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1(x_0, x_183, x_1, x_435);
if (lean::obj_tag(x_441) == 0)
{
obj* x_452; obj* x_455; 
lean::dec(x_270);
lean::dec(x_183);
lean::dec(x_179);
lean::dec(x_230);
lean::dec(x_225);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_410);
lean::dec(x_271);
lean::dec(x_433);
x_452 = lean::cnstr_get(x_441, 0);
lean::inc(x_452);
lean::dec(x_441);
if (lean::is_scalar(x_224)) {
 x_455 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_455 = x_224;
}
lean::cnstr_set(x_455, 0, x_452);
x_5 = x_455;
goto lbl_6;
}
else
{
obj* x_457; obj* x_460; obj* x_462; obj* x_465; obj* x_466; obj* x_469; unsigned char x_470; obj* x_471; obj* x_473; obj* x_475; obj* x_477; obj* x_479; obj* x_481; obj* x_483; obj* x_484; obj* x_486; obj* x_488; obj* x_490; obj* x_491; obj* x_492; obj* x_493; obj* x_494; obj* x_495; obj* x_496; obj* x_497; obj* x_499; obj* x_500; obj* x_502; obj* x_503; 
lean::dec(x_224);
x_457 = lean::cnstr_get(x_441, 0);
lean::inc(x_457);
lean::dec(x_441);
x_460 = lean::cnstr_get(x_457, 0);
lean::inc(x_460);
x_462 = lean::cnstr_get(x_457, 1);
lean::inc(x_462);
lean::dec(x_457);
x_465 = l_lean_elaborator_names__to__pexpr(x_271);
x_466 = lean::cnstr_get(x_179, 0);
lean::inc(x_466);
lean::dec(x_179);
x_469 = l_lean_elaborator_mangle__ident(x_466);
x_470 = 0;
x_471 = lean::box(x_470);
lean::inc(x_469);
x_473 = lean_expr_local(x_469, x_469, x_410, x_471);
lean::inc(x_230);
x_475 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_475, 0, x_473);
lean::cnstr_set(x_475, 1, x_230);
lean::inc(x_268);
x_477 = l_lean_expr_mk__capp(x_268, x_475);
lean::inc(x_268);
x_479 = l_lean_expr_mk__capp(x_268, x_460);
lean::inc(x_230);
x_481 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_481, 0, x_479);
lean::cnstr_set(x_481, 1, x_230);
lean::inc(x_268);
x_483 = l_lean_expr_mk__capp(x_268, x_481);
x_484 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__2(x_183);
lean::inc(x_268);
x_486 = l_lean_expr_mk__capp(x_268, x_484);
lean::inc(x_230);
x_488 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_488, 0, x_486);
lean::cnstr_set(x_488, 1, x_230);
lean::inc(x_268);
x_490 = l_lean_expr_mk__capp(x_268, x_488);
x_491 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_491, 0, x_490);
lean::cnstr_set(x_491, 1, x_230);
x_492 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_492, 0, x_483);
lean::cnstr_set(x_492, 1, x_491);
x_493 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_493, 0, x_433);
lean::cnstr_set(x_493, 1, x_492);
x_494 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_494, 0, x_477);
lean::cnstr_set(x_494, 1, x_493);
x_495 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_495, 0, x_465);
lean::cnstr_set(x_495, 1, x_494);
x_496 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_496, 0, x_270);
lean::cnstr_set(x_496, 1, x_495);
x_497 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_497, 0, x_225);
lean::cnstr_set(x_497, 1, x_496);
lean::inc(x_268);
x_499 = l_lean_expr_mk__capp(x_268, x_497);
x_500 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__4;
lean::inc(x_500);
x_502 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_502, 0, x_500);
lean::cnstr_set(x_502, 1, x_499);
x_503 = l_lean_elaborator_old__elab__command(x_0, x_502, x_1, x_462);
x_5 = x_503;
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
obj* x_510; obj* x_512; 
lean::dec(x_183);
lean::dec(x_181);
lean::dec(x_179);
lean::dec(x_177);
lean::dec(x_11);
lean::dec(x_175);
x_510 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_510);
x_512 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_510, x_1, x_2);
x_5 = x_512;
goto lbl_6;
}
}
default:
{
obj* x_513; obj* x_516; obj* x_518; obj* x_520; obj* x_522; obj* x_524; obj* x_526; obj* x_528; 
x_513 = lean::cnstr_get(x_12, 0);
lean::inc(x_513);
lean::dec(x_12);
x_516 = lean::cnstr_get(x_513, 0);
lean::inc(x_516);
x_518 = lean::cnstr_get(x_513, 1);
lean::inc(x_518);
x_520 = lean::cnstr_get(x_513, 2);
lean::inc(x_520);
x_522 = lean::cnstr_get(x_513, 3);
lean::inc(x_522);
x_524 = lean::cnstr_get(x_513, 4);
lean::inc(x_524);
x_526 = lean::cnstr_get(x_513, 6);
lean::inc(x_526);
x_528 = lean::cnstr_get(x_513, 7);
lean::inc(x_528);
lean::dec(x_513);
if (lean::obj_tag(x_516) == 0)
{
obj* x_532; obj* x_534; 
lean::dec(x_516);
x_532 = lean::cnstr_get(x_522, 0);
lean::inc(x_532);
x_534 = lean::cnstr_get(x_522, 1);
lean::inc(x_534);
lean::dec(x_522);
if (lean::obj_tag(x_532) == 0)
{
obj* x_545; obj* x_547; 
lean::dec(x_11);
lean::dec(x_528);
lean::dec(x_534);
lean::dec(x_526);
lean::dec(x_520);
lean::dec(x_532);
lean::dec(x_524);
lean::dec(x_518);
x_545 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_545);
x_547 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_545, x_1, x_2);
x_5 = x_547;
goto lbl_6;
}
else
{
obj* x_548; obj* x_551; obj* x_555; 
x_548 = lean::cnstr_get(x_532, 0);
lean::inc(x_548);
lean::dec(x_532);
x_551 = lean::cnstr_get(x_11, 0);
lean::inc(x_551);
lean::dec(x_11);
lean::inc(x_1);
x_555 = l_lean_elaborator_decl__modifiers__to__pexpr(x_551, x_1, x_2);
if (lean::obj_tag(x_555) == 0)
{
obj* x_565; obj* x_567; obj* x_568; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_548);
lean::dec(x_528);
lean::dec(x_534);
lean::dec(x_526);
lean::dec(x_520);
lean::dec(x_524);
lean::dec(x_518);
x_565 = lean::cnstr_get(x_555, 0);
lean::inc(x_565);
if (lean::is_shared(x_555)) {
 lean::dec(x_555);
 x_567 = lean::box(0);
} else {
 lean::cnstr_release(x_555, 0);
 x_567 = x_555;
}
if (lean::is_scalar(x_567)) {
 x_568 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_568 = x_567;
}
lean::cnstr_set(x_568, 0, x_565);
x_5 = x_568;
goto lbl_6;
}
else
{
obj* x_569; obj* x_571; obj* x_572; obj* x_574; obj* x_577; obj* x_578; obj* x_579; 
x_569 = lean::cnstr_get(x_555, 0);
lean::inc(x_569);
if (lean::is_shared(x_555)) {
 lean::dec(x_555);
 x_571 = lean::box(0);
} else {
 lean::cnstr_release(x_555, 0);
 x_571 = x_555;
}
x_572 = lean::cnstr_get(x_569, 0);
lean::inc(x_572);
x_574 = lean::cnstr_get(x_569, 1);
lean::inc(x_574);
lean::dec(x_569);
x_577 = lean::box(0);
if (lean::obj_tag(x_518) == 0)
{
obj* x_581; obj* x_583; 
x_581 = l_lean_expander_get__opt__type___main(x_534);
lean::inc(x_1);
x_583 = l_lean_elaborator_to__pexpr___main(x_581, x_1, x_574);
if (lean::obj_tag(x_518) == 0)
{
lean::dec(x_518);
if (lean::obj_tag(x_583) == 0)
{
obj* x_595; obj* x_597; obj* x_598; 
lean::dec(x_572);
lean::dec(x_577);
lean::dec(x_571);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_548);
lean::dec(x_528);
lean::dec(x_526);
lean::dec(x_520);
lean::dec(x_524);
x_595 = lean::cnstr_get(x_583, 0);
lean::inc(x_595);
if (lean::is_shared(x_583)) {
 lean::dec(x_583);
 x_597 = lean::box(0);
} else {
 lean::cnstr_release(x_583, 0);
 x_597 = x_583;
}
if (lean::is_scalar(x_597)) {
 x_598 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_598 = x_597;
}
lean::cnstr_set(x_598, 0, x_595);
x_5 = x_598;
goto lbl_6;
}
else
{
obj* x_599; 
x_599 = lean::cnstr_get(x_583, 0);
lean::inc(x_599);
lean::dec(x_583);
x_578 = x_577;
x_579 = x_599;
goto lbl_580;
}
}
else
{
obj* x_602; 
x_602 = lean::cnstr_get(x_518, 0);
lean::inc(x_602);
lean::dec(x_518);
if (lean::obj_tag(x_583) == 0)
{
obj* x_616; obj* x_618; obj* x_619; 
lean::dec(x_572);
lean::dec(x_577);
lean::dec(x_571);
lean::dec(x_602);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_548);
lean::dec(x_528);
lean::dec(x_526);
lean::dec(x_520);
lean::dec(x_524);
x_616 = lean::cnstr_get(x_583, 0);
lean::inc(x_616);
if (lean::is_shared(x_583)) {
 lean::dec(x_583);
 x_618 = lean::box(0);
} else {
 lean::cnstr_release(x_583, 0);
 x_618 = x_583;
}
if (lean::is_scalar(x_618)) {
 x_619 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_619 = x_618;
}
lean::cnstr_set(x_619, 0, x_616);
x_5 = x_619;
goto lbl_6;
}
else
{
obj* x_620; obj* x_623; obj* x_626; 
x_620 = lean::cnstr_get(x_583, 0);
lean::inc(x_620);
lean::dec(x_583);
x_623 = lean::cnstr_get(x_602, 1);
lean::inc(x_623);
lean::dec(x_602);
x_626 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__10(x_623);
x_578 = x_626;
x_579 = x_620;
goto lbl_580;
}
}
}
else
{
obj* x_627; obj* x_629; obj* x_631; obj* x_633; obj* x_635; obj* x_637; obj* x_639; obj* x_641; obj* x_643; obj* x_647; obj* x_648; obj* x_649; obj* x_651; obj* x_653; obj* x_655; obj* x_657; obj* x_660; obj* x_661; obj* x_663; obj* x_665; obj* x_667; obj* x_669; obj* x_671; obj* x_674; obj* x_675; obj* x_677; 
x_627 = lean::cnstr_get(x_518, 0);
lean::inc(x_627);
x_629 = lean::cnstr_get(x_574, 0);
lean::inc(x_629);
x_631 = lean::cnstr_get(x_574, 1);
lean::inc(x_631);
x_633 = lean::cnstr_get(x_574, 2);
lean::inc(x_633);
x_635 = lean::cnstr_get(x_574, 3);
lean::inc(x_635);
x_637 = lean::cnstr_get(x_574, 4);
lean::inc(x_637);
x_639 = lean::cnstr_get(x_637, 0);
lean::inc(x_639);
x_641 = lean::cnstr_get(x_637, 1);
lean::inc(x_641);
x_643 = lean::cnstr_get(x_627, 1);
lean::inc(x_643);
lean::dec(x_627);
lean::inc(x_643);
x_647 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__11(x_643);
x_648 = l_list_foldl___main___at_lean_elaborator_declaration_elaborate___spec__12(x_641, x_647);
x_649 = lean::cnstr_get(x_637, 2);
lean::inc(x_649);
x_651 = lean::cnstr_get(x_637, 3);
lean::inc(x_651);
x_653 = lean::cnstr_get(x_637, 4);
lean::inc(x_653);
x_655 = lean::cnstr_get(x_637, 5);
lean::inc(x_655);
x_657 = lean::cnstr_get(x_637, 6);
lean::inc(x_657);
lean::dec(x_637);
x_660 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_660, 0, x_639);
lean::cnstr_set(x_660, 1, x_648);
lean::cnstr_set(x_660, 2, x_649);
lean::cnstr_set(x_660, 3, x_651);
lean::cnstr_set(x_660, 4, x_653);
lean::cnstr_set(x_660, 5, x_655);
lean::cnstr_set(x_660, 6, x_657);
x_661 = lean::cnstr_get(x_574, 5);
lean::inc(x_661);
x_663 = lean::cnstr_get(x_574, 6);
lean::inc(x_663);
x_665 = lean::cnstr_get(x_574, 7);
lean::inc(x_665);
x_667 = lean::cnstr_get(x_574, 8);
lean::inc(x_667);
x_669 = lean::cnstr_get(x_574, 9);
lean::inc(x_669);
x_671 = lean::cnstr_get(x_574, 10);
lean::inc(x_671);
lean::dec(x_574);
x_674 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_674, 0, x_629);
lean::cnstr_set(x_674, 1, x_631);
lean::cnstr_set(x_674, 2, x_633);
lean::cnstr_set(x_674, 3, x_635);
lean::cnstr_set(x_674, 4, x_660);
lean::cnstr_set(x_674, 5, x_661);
lean::cnstr_set(x_674, 6, x_663);
lean::cnstr_set(x_674, 7, x_665);
lean::cnstr_set(x_674, 8, x_667);
lean::cnstr_set(x_674, 9, x_669);
lean::cnstr_set(x_674, 10, x_671);
x_675 = l_lean_expander_get__opt__type___main(x_534);
lean::inc(x_1);
x_677 = l_lean_elaborator_to__pexpr___main(x_675, x_1, x_674);
if (lean::obj_tag(x_518) == 0)
{
lean::dec(x_643);
lean::dec(x_518);
if (lean::obj_tag(x_677) == 0)
{
obj* x_690; obj* x_692; obj* x_693; 
lean::dec(x_572);
lean::dec(x_577);
lean::dec(x_571);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_548);
lean::dec(x_528);
lean::dec(x_526);
lean::dec(x_520);
lean::dec(x_524);
x_690 = lean::cnstr_get(x_677, 0);
lean::inc(x_690);
if (lean::is_shared(x_677)) {
 lean::dec(x_677);
 x_692 = lean::box(0);
} else {
 lean::cnstr_release(x_677, 0);
 x_692 = x_677;
}
if (lean::is_scalar(x_692)) {
 x_693 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_693 = x_692;
}
lean::cnstr_set(x_693, 0, x_690);
x_5 = x_693;
goto lbl_6;
}
else
{
obj* x_694; 
x_694 = lean::cnstr_get(x_677, 0);
lean::inc(x_694);
lean::dec(x_677);
x_578 = x_577;
x_579 = x_694;
goto lbl_580;
}
}
else
{
lean::dec(x_518);
if (lean::obj_tag(x_677) == 0)
{
obj* x_709; obj* x_711; obj* x_712; 
lean::dec(x_643);
lean::dec(x_572);
lean::dec(x_577);
lean::dec(x_571);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_548);
lean::dec(x_528);
lean::dec(x_526);
lean::dec(x_520);
lean::dec(x_524);
x_709 = lean::cnstr_get(x_677, 0);
lean::inc(x_709);
if (lean::is_shared(x_677)) {
 lean::dec(x_677);
 x_711 = lean::box(0);
} else {
 lean::cnstr_release(x_677, 0);
 x_711 = x_677;
}
if (lean::is_scalar(x_711)) {
 x_712 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_712 = x_711;
}
lean::cnstr_set(x_712, 0, x_709);
x_5 = x_712;
goto lbl_6;
}
else
{
obj* x_713; obj* x_716; 
x_713 = lean::cnstr_get(x_677, 0);
lean::inc(x_713);
lean::dec(x_677);
x_716 = l_list_map___main___at_lean_elaborator_declaration_elaborate___spec__13(x_643);
x_578 = x_716;
x_579 = x_713;
goto lbl_580;
}
}
}
lbl_580:
{
obj* x_717; obj* x_719; obj* x_723; 
x_717 = lean::cnstr_get(x_579, 0);
lean::inc(x_717);
x_719 = lean::cnstr_get(x_579, 1);
lean::inc(x_719);
lean::dec(x_579);
lean::inc(x_1);
x_723 = l_lean_elaborator_simple__binders__to__pexpr(x_548, x_1, x_719);
if (lean::obj_tag(x_723) == 0)
{
obj* x_734; obj* x_737; 
lean::dec(x_572);
lean::dec(x_577);
lean::dec(x_717);
lean::dec(x_578);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_528);
lean::dec(x_526);
lean::dec(x_520);
lean::dec(x_524);
x_734 = lean::cnstr_get(x_723, 0);
lean::inc(x_734);
lean::dec(x_723);
if (lean::is_scalar(x_571)) {
 x_737 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_737 = x_571;
}
lean::cnstr_set(x_737, 0, x_734);
x_5 = x_737;
goto lbl_6;
}
else
{
obj* x_738; obj* x_741; obj* x_743; obj* x_746; obj* x_747; obj* x_750; obj* x_751; unsigned char x_752; obj* x_753; obj* x_757; obj* x_758; 
x_738 = lean::cnstr_get(x_723, 0);
lean::inc(x_738);
lean::dec(x_723);
x_741 = lean::cnstr_get(x_738, 0);
lean::inc(x_741);
x_743 = lean::cnstr_get(x_738, 1);
lean::inc(x_743);
lean::dec(x_738);
x_746 = l_lean_elaborator_names__to__pexpr(x_578);
x_747 = lean::cnstr_get(x_520, 0);
lean::inc(x_747);
lean::dec(x_520);
x_750 = l_lean_elaborator_mangle__ident(x_747);
x_751 = l_lean_elaborator_dummy;
x_752 = 0;
x_753 = lean::box(x_752);
lean::inc(x_753);
lean::inc(x_751);
lean::inc(x_750);
x_757 = lean_expr_local(x_750, x_750, x_751, x_753);
if (lean::obj_tag(x_524) == 0)
{
lean::dec(x_524);
x_758 = x_577;
goto lbl_759;
}
else
{
obj* x_761; obj* x_764; 
x_761 = lean::cnstr_get(x_524, 0);
lean::inc(x_761);
lean::dec(x_524);
x_764 = lean::cnstr_get(x_761, 1);
lean::inc(x_764);
lean::dec(x_761);
x_758 = x_764;
goto lbl_759;
}
lbl_759:
{
obj* x_768; 
lean::inc(x_1);
x_768 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__7(x_758, x_1, x_743);
if (lean::obj_tag(x_768) == 0)
{
obj* x_780; obj* x_783; 
lean::dec(x_572);
lean::dec(x_577);
lean::dec(x_717);
lean::dec(x_746);
lean::dec(x_753);
lean::dec(x_741);
lean::dec(x_757);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_528);
lean::dec(x_526);
x_780 = lean::cnstr_get(x_768, 0);
lean::inc(x_780);
lean::dec(x_768);
if (lean::is_scalar(x_571)) {
 x_783 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_783 = x_571;
}
lean::cnstr_set(x_783, 0, x_780);
x_5 = x_783;
goto lbl_6;
}
else
{
obj* x_784; obj* x_787; obj* x_789; obj* x_792; obj* x_794; obj* x_797; obj* x_798; 
x_784 = lean::cnstr_get(x_768, 0);
lean::inc(x_784);
lean::dec(x_768);
x_787 = lean::cnstr_get(x_784, 0);
lean::inc(x_787);
x_789 = lean::cnstr_get(x_784, 1);
lean::inc(x_789);
lean::dec(x_784);
x_792 = l_lean_elaborator_mk__eqns___closed__1;
lean::inc(x_792);
x_794 = l_lean_expr_mk__capp(x_792, x_787);
lean::inc(x_1);
lean::inc(x_0);
x_797 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__9(x_0, x_528, x_1, x_789);
if (lean::obj_tag(x_526) == 0)
{
obj* x_800; 
x_800 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__7;
lean::inc(x_800);
x_798 = x_800;
goto lbl_799;
}
else
{
obj* x_802; obj* x_804; obj* x_807; 
x_802 = lean::cnstr_get(x_526, 0);
lean::inc(x_802);
x_804 = lean::cnstr_get(x_802, 0);
lean::inc(x_804);
lean::dec(x_802);
x_807 = l_lean_elaborator_mangle__ident(x_804);
x_798 = x_807;
goto lbl_799;
}
lbl_799:
{
obj* x_810; 
lean::inc(x_751);
lean::inc(x_798);
x_810 = lean_expr_local(x_798, x_798, x_751, x_753);
if (lean::obj_tag(x_526) == 0)
{
lean::dec(x_526);
if (lean::obj_tag(x_797) == 0)
{
obj* x_822; obj* x_825; 
lean::dec(x_572);
lean::dec(x_577);
lean::dec(x_717);
lean::dec(x_746);
lean::dec(x_741);
lean::dec(x_757);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_794);
lean::dec(x_810);
x_822 = lean::cnstr_get(x_797, 0);
lean::inc(x_822);
lean::dec(x_797);
if (lean::is_scalar(x_571)) {
 x_825 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_825 = x_571;
}
lean::cnstr_set(x_825, 0, x_822);
x_5 = x_825;
goto lbl_6;
}
else
{
obj* x_827; obj* x_830; obj* x_832; obj* x_836; obj* x_837; obj* x_838; obj* x_840; obj* x_841; obj* x_842; obj* x_843; obj* x_844; obj* x_845; obj* x_846; obj* x_847; obj* x_849; obj* x_850; obj* x_852; obj* x_853; 
lean::dec(x_571);
x_827 = lean::cnstr_get(x_797, 0);
lean::inc(x_827);
lean::dec(x_797);
x_830 = lean::cnstr_get(x_827, 0);
lean::inc(x_830);
x_832 = lean::cnstr_get(x_827, 1);
lean::inc(x_832);
lean::dec(x_827);
lean::inc(x_792);
x_836 = l_lean_expr_mk__capp(x_792, x_830);
x_837 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_837, 0, x_836);
lean::cnstr_set(x_837, 1, x_577);
x_838 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__5;
lean::inc(x_838);
x_840 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_840, 0, x_838);
lean::cnstr_set(x_840, 1, x_837);
x_841 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_841, 0, x_810);
lean::cnstr_set(x_841, 1, x_840);
x_842 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_842, 0, x_717);
lean::cnstr_set(x_842, 1, x_841);
x_843 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_843, 0, x_794);
lean::cnstr_set(x_843, 1, x_842);
x_844 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_844, 0, x_741);
lean::cnstr_set(x_844, 1, x_843);
x_845 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_845, 0, x_757);
lean::cnstr_set(x_845, 1, x_844);
x_846 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_846, 0, x_746);
lean::cnstr_set(x_846, 1, x_845);
x_847 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_847, 0, x_572);
lean::cnstr_set(x_847, 1, x_846);
lean::inc(x_792);
x_849 = l_lean_expr_mk__capp(x_792, x_847);
x_850 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
lean::inc(x_850);
x_852 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_852, 0, x_850);
lean::cnstr_set(x_852, 1, x_849);
x_853 = l_lean_elaborator_old__elab__command(x_0, x_852, x_1, x_832);
x_5 = x_853;
goto lbl_6;
}
}
else
{
obj* x_854; 
x_854 = lean::cnstr_get(x_526, 0);
lean::inc(x_854);
lean::dec(x_526);
if (lean::obj_tag(x_797) == 0)
{
obj* x_868; obj* x_871; 
lean::dec(x_572);
lean::dec(x_577);
lean::dec(x_717);
lean::dec(x_746);
lean::dec(x_741);
lean::dec(x_757);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_854);
lean::dec(x_794);
lean::dec(x_810);
x_868 = lean::cnstr_get(x_797, 0);
lean::inc(x_868);
lean::dec(x_797);
if (lean::is_scalar(x_571)) {
 x_871 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_871 = x_571;
}
lean::cnstr_set(x_871, 0, x_868);
x_5 = x_871;
goto lbl_6;
}
else
{
obj* x_873; obj* x_876; obj* x_878; obj* x_881; obj* x_884; obj* x_886; obj* x_887; obj* x_888; obj* x_889; obj* x_890; obj* x_891; obj* x_892; obj* x_893; obj* x_894; obj* x_895; obj* x_897; obj* x_898; obj* x_900; obj* x_901; 
lean::dec(x_571);
x_873 = lean::cnstr_get(x_797, 0);
lean::inc(x_873);
lean::dec(x_797);
x_876 = lean::cnstr_get(x_873, 0);
lean::inc(x_876);
x_878 = lean::cnstr_get(x_873, 1);
lean::inc(x_878);
lean::dec(x_873);
x_881 = lean::cnstr_get(x_854, 1);
lean::inc(x_881);
lean::dec(x_854);
x_884 = l_lean_elaborator_infer__mod__to__pexpr(x_881);
lean::inc(x_792);
x_886 = l_lean_expr_mk__capp(x_792, x_876);
x_887 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_887, 0, x_886);
lean::cnstr_set(x_887, 1, x_577);
x_888 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_888, 0, x_884);
lean::cnstr_set(x_888, 1, x_887);
x_889 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_889, 0, x_810);
lean::cnstr_set(x_889, 1, x_888);
x_890 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_890, 0, x_717);
lean::cnstr_set(x_890, 1, x_889);
x_891 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_891, 0, x_794);
lean::cnstr_set(x_891, 1, x_890);
x_892 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_892, 0, x_741);
lean::cnstr_set(x_892, 1, x_891);
x_893 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_893, 0, x_757);
lean::cnstr_set(x_893, 1, x_892);
x_894 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_894, 0, x_746);
lean::cnstr_set(x_894, 1, x_893);
x_895 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_895, 0, x_572);
lean::cnstr_set(x_895, 1, x_894);
lean::inc(x_792);
x_897 = l_lean_expr_mk__capp(x_792, x_895);
x_898 = l_lean_elaborator_locally___at_lean_elaborator_declaration_elaborate___spec__14___closed__6;
lean::inc(x_898);
x_900 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_900, 0, x_898);
lean::cnstr_set(x_900, 1, x_897);
x_901 = l_lean_elaborator_old__elab__command(x_0, x_900, x_1, x_878);
x_5 = x_901;
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
obj* x_910; obj* x_912; 
lean::dec(x_11);
lean::dec(x_528);
lean::dec(x_526);
lean::dec(x_520);
lean::dec(x_524);
lean::dec(x_518);
lean::dec(x_522);
lean::dec(x_516);
x_910 = l_list_mmap___main___at_lean_elaborator_declaration_elaborate___spec__1___closed__1;
lean::inc(x_910);
x_912 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_910, x_1, x_2);
x_5 = x_912;
goto lbl_6;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_914; obj* x_916; obj* x_917; 
lean::dec(x_3);
x_914 = lean::cnstr_get(x_5, 0);
lean::inc(x_914);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_916 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_916 = x_5;
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
obj* x_918; obj* x_920; obj* x_921; obj* x_923; obj* x_924; obj* x_926; obj* x_928; obj* x_930; obj* x_932; obj* x_934; obj* x_936; obj* x_938; obj* x_940; obj* x_942; obj* x_945; obj* x_946; obj* x_947; obj* x_948; 
x_918 = lean::cnstr_get(x_5, 0);
lean::inc(x_918);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_920 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_920 = x_5;
}
x_921 = lean::cnstr_get(x_918, 1);
lean::inc(x_921);
if (lean::is_shared(x_918)) {
 lean::dec(x_918);
 x_923 = lean::box(0);
} else {
 lean::cnstr_release(x_918, 0);
 lean::cnstr_release(x_918, 1);
 x_923 = x_918;
}
x_924 = lean::cnstr_get(x_921, 0);
lean::inc(x_924);
x_926 = lean::cnstr_get(x_921, 1);
lean::inc(x_926);
x_928 = lean::cnstr_get(x_921, 2);
lean::inc(x_928);
x_930 = lean::cnstr_get(x_921, 3);
lean::inc(x_930);
x_932 = lean::cnstr_get(x_921, 5);
lean::inc(x_932);
x_934 = lean::cnstr_get(x_921, 6);
lean::inc(x_934);
x_936 = lean::cnstr_get(x_921, 7);
lean::inc(x_936);
x_938 = lean::cnstr_get(x_921, 8);
lean::inc(x_938);
x_940 = lean::cnstr_get(x_921, 9);
lean::inc(x_940);
x_942 = lean::cnstr_get(x_921, 10);
lean::inc(x_942);
lean::dec(x_921);
x_945 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_945, 0, x_924);
lean::cnstr_set(x_945, 1, x_926);
lean::cnstr_set(x_945, 2, x_928);
lean::cnstr_set(x_945, 3, x_930);
lean::cnstr_set(x_945, 4, x_3);
lean::cnstr_set(x_945, 5, x_932);
lean::cnstr_set(x_945, 6, x_934);
lean::cnstr_set(x_945, 7, x_936);
lean::cnstr_set(x_945, 8, x_938);
lean::cnstr_set(x_945, 9, x_940);
lean::cnstr_set(x_945, 10, x_942);
x_946 = lean::box(0);
if (lean::is_scalar(x_923)) {
 x_947 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_947 = x_923;
}
lean::cnstr_set(x_947, 0, x_946);
lean::cnstr_set(x_947, 1, x_945);
if (lean::is_scalar(x_920)) {
 x_948 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_948 = x_920;
}
lean::cnstr_set(x_948, 0, x_947);
return x_948;
}
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
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string("constant");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
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
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string("inductives");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
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
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string("structure");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
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
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
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
x_50 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_43);
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
x_90 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_83);
x_91 = l_lean_elaborator_old__elab__command(x_0, x_90, x_1, x_85);
return x_91;
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
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string("variables");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; unsigned char x_29; 
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
unsigned char x_33; obj* x_34; obj* x_35; 
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
obj* x_52; obj* x_54; obj* x_55; obj* x_57; unsigned char x_60; 
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
obj* x_82; obj* x_83; obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_95; 
lean::dec(x_15);
lean::dec(x_71);
lean::dec(x_73);
lean::dec(x_77);
x_82 = lean::box(0);
x_83 = l_lean_name_to__string___closed__1;
lean::inc(x_70);
lean::inc(x_83);
x_86 = l_lean_name_to__string__with__sep___main(x_83, x_70);
x_87 = l_lean_parser_substring_of__string(x_86);
lean::inc(x_82);
lean::inc(x_82);
x_90 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_90, 0, x_82);
lean::cnstr_set(x_90, 1, x_87);
lean::cnstr_set(x_90, 2, x_70);
lean::cnstr_set(x_90, 3, x_82);
lean::cnstr_set(x_90, 4, x_82);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
x_92 = l_string_join___closed__1;
lean::inc(x_1);
lean::inc(x_92);
x_95 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_91, x_92, x_1, x_2);
if (lean::obj_tag(x_95) == 0)
{
obj* x_101; obj* x_103; obj* x_104; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
lean::dec(x_19);
x_101 = lean::cnstr_get(x_95, 0);
lean::inc(x_101);
if (lean::is_shared(x_95)) {
 lean::dec(x_95);
 x_103 = lean::box(0);
} else {
 lean::cnstr_release(x_95, 0);
 x_103 = x_95;
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
obj* x_105; obj* x_108; unsigned char x_111; obj* x_112; obj* x_113; 
x_105 = lean::cnstr_get(x_95, 0);
lean::inc(x_105);
lean::dec(x_95);
x_108 = lean::cnstr_get(x_105, 1);
lean::inc(x_108);
lean::dec(x_105);
x_111 = 0;
x_112 = lean::box(x_111);
if (lean::is_scalar(x_19)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_19;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_108);
x_11 = x_113;
goto lbl_12;
}
}
else
{
obj* x_114; obj* x_117; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_134; obj* x_137; unsigned char x_138; obj* x_140; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_151; obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_160; obj* x_162; obj* x_165; unsigned char x_166; obj* x_167; obj* x_168; 
x_114 = lean::cnstr_get(x_77, 0);
lean::inc(x_114);
lean::dec(x_77);
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
x_120 = lean::cnstr_get(x_2, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_2, 1);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_2, 2);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_2, 3);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_71, 0);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_71, 1);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_117, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_117, 1);
lean::inc(x_134);
lean::dec(x_117);
x_137 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_137, 0, x_132);
lean::cnstr_set(x_137, 1, x_134);
x_138 = lean::unbox(x_15);
lean::dec(x_15);
lean::cnstr_set_scalar(x_137, sizeof(void*)*2, x_138);
x_140 = x_137;
x_141 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_variables_elaborate___spec__3(x_73, x_70, x_140);
x_142 = lean::cnstr_get(x_71, 3);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_71, 4);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_71, 5);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_71, 6);
lean::inc(x_148);
lean::dec(x_71);
x_151 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_151, 0, x_128);
lean::cnstr_set(x_151, 1, x_130);
lean::cnstr_set(x_151, 2, x_141);
lean::cnstr_set(x_151, 3, x_142);
lean::cnstr_set(x_151, 4, x_144);
lean::cnstr_set(x_151, 5, x_146);
lean::cnstr_set(x_151, 6, x_148);
x_152 = lean::cnstr_get(x_2, 5);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_2, 6);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_2, 7);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_2, 8);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_2, 9);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_2, 10);
lean::inc(x_162);
lean::dec(x_2);
x_165 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_165, 0, x_120);
lean::cnstr_set(x_165, 1, x_122);
lean::cnstr_set(x_165, 2, x_124);
lean::cnstr_set(x_165, 3, x_126);
lean::cnstr_set(x_165, 4, x_151);
lean::cnstr_set(x_165, 5, x_152);
lean::cnstr_set(x_165, 6, x_154);
lean::cnstr_set(x_165, 7, x_156);
lean::cnstr_set(x_165, 8, x_158);
lean::cnstr_set(x_165, 9, x_160);
lean::cnstr_set(x_165, 10, x_162);
x_166 = 0;
x_167 = lean::box(x_166);
if (lean::is_scalar(x_19)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_19;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_165);
x_11 = x_168;
goto lbl_12;
}
}
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
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_lean_elaborator_mangle__ident(x_3);
x_9 = lean::box(0);
x_10 = l_rbnode_insert___at_lean_elaborator_old__elab__command___spec__17(x_0, x_8, x_9);
x_0 = x_10;
x_1 = x_5;
goto _start;
}
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
obj* x_15; obj* x_17; 
lean::dec(x_10);
lean::dec(x_8);
x_15 = l_lean_elaborator_module_header_elaborate___closed__1;
lean::inc(x_15);
x_17 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_15, x_1, x_2);
return x_17;
}
else
{
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_10);
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
obj* x_26; obj* x_28; 
lean::dec(x_10);
x_26 = l_lean_elaborator_module_header_elaborate___closed__1;
lean::inc(x_26);
x_28 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_26, x_1, x_2);
return x_28;
}
}
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
obj* l_lean_elaborator_prec__to__nat___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::mk_nat_obj(0u);
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_6);
return x_9;
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
obj* l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_12; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 3);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_12) == 0)
{
obj* x_21; 
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_12);
lean::dec(x_0);
x_21 = l_list_mfoldl___main___at_lean_elaborator_command__parser__config_register__notation__tokens___spec__1___closed__1;
lean::inc(x_21);
return x_21;
}
else
{
obj* x_23; obj* x_26; obj* x_28; obj* x_30; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_52; 
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
lean::dec(x_12);
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_26, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_26, 1);
lean::inc(x_30);
lean::dec(x_26);
x_33 = lean::cnstr_get(x_23, 1);
lean::inc(x_33);
lean::dec(x_23);
x_36 = l_string_trim(x_33);
x_37 = l_lean_elaborator_prec__to__nat___main(x_14);
x_38 = lean::box(0);
lean::inc(x_36);
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set(x_40, 1, x_37);
lean::cnstr_set(x_40, 2, x_38);
x_41 = l_lean_parser_trie_insert___rarg(x_30, x_36, x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_28);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::cnstr_get(x_0, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_0, 2);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_0, 3);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_0, 4);
lean::inc(x_49);
lean::dec(x_0);
x_52 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_52, 0, x_42);
lean::cnstr_set(x_52, 1, x_43);
lean::cnstr_set(x_52, 2, x_45);
lean::cnstr_set(x_52, 3, x_47);
lean::cnstr_set(x_52, 4, x_49);
x_0 = x_52;
x_1 = x_6;
goto _start;
}
}
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
obj* x_30; 
lean::dec(x_20);
lean::dec(x_18);
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_30 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__2;
lean::inc(x_30);
return x_30;
}
else
{
obj* x_32; obj* x_35; obj* x_38; 
x_32 = lean::cnstr_get(x_5, 0);
lean::inc(x_32);
lean::dec(x_5);
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
lean::dec(x_32);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
if (lean::obj_tag(x_38) == 0)
{
obj* x_48; 
lean::dec(x_20);
lean::dec(x_18);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_38);
x_48 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__2;
lean::inc(x_48);
return x_48;
}
else
{
obj* x_50; obj* x_53; obj* x_56; 
x_50 = lean::cnstr_get(x_38, 0);
lean::inc(x_50);
lean::dec(x_38);
x_53 = lean::cnstr_get(x_50, 1);
lean::inc(x_53);
lean::dec(x_50);
x_56 = l_string_trim(x_53);
x_21 = x_56;
goto lbl_22;
}
}
lbl_22:
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(x_18);
x_58 = l_list_join___main___rarg(x_57);
x_59 = lean::cnstr_get(x_1, 0);
lean::inc(x_59);
lean::dec(x_1);
if (lean::obj_tag(x_59) == 0)
{
obj* x_63; 
lean::dec(x_59);
x_63 = lean::cnstr_get(x_3, 0);
lean::inc(x_63);
lean::dec(x_3);
if (lean::obj_tag(x_63) == 0)
{
obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_82; obj* x_83; 
lean::dec(x_63);
x_67 = lean::cnstr_get(x_2, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_2, 1);
lean::inc(x_69);
x_71 = lean::box(0);
x_72 = lean::name_mk_string(x_71, x_21);
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__5), 7, 2);
lean::closure_set(x_73, 0, x_0);
lean::closure_set(x_73, 1, x_58);
x_74 = l_lean_parser_token__map_insert___rarg(x_69, x_72, x_73);
x_75 = lean::cnstr_get(x_2, 2);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_2, 3);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_2, 4);
lean::inc(x_79);
lean::dec(x_2);
x_82 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_82, 0, x_67);
lean::cnstr_set(x_82, 1, x_74);
lean::cnstr_set(x_82, 2, x_75);
lean::cnstr_set(x_82, 3, x_77);
lean::cnstr_set(x_82, 4, x_79);
if (lean::is_scalar(x_20)) {
 x_83 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_83 = x_20;
}
lean::cnstr_set(x_83, 0, x_82);
return x_83;
}
else
{
obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_101; obj* x_104; obj* x_105; 
lean::dec(x_63);
x_85 = lean::cnstr_get(x_2, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_2, 1);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_2, 2);
lean::inc(x_89);
x_91 = lean::box(0);
x_92 = lean::name_mk_string(x_91, x_21);
x_93 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(x_58);
x_94 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
lean::inc(x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_94);
lean::cnstr_set(x_96, 1, x_93);
x_97 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser___spec__2), 8, 2);
lean::closure_set(x_97, 0, x_0);
lean::closure_set(x_97, 1, x_96);
x_98 = l_lean_parser_token__map_insert___rarg(x_89, x_92, x_97);
x_99 = lean::cnstr_get(x_2, 3);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_2, 4);
lean::inc(x_101);
lean::dec(x_2);
x_104 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_104, 0, x_85);
lean::cnstr_set(x_104, 1, x_87);
lean::cnstr_set(x_104, 2, x_98);
lean::cnstr_set(x_104, 3, x_99);
lean::cnstr_set(x_104, 4, x_101);
if (lean::is_scalar(x_20)) {
 x_105 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_105 = x_20;
}
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
}
else
{
obj* x_107; 
lean::dec(x_59);
x_107 = lean::cnstr_get(x_3, 0);
lean::inc(x_107);
lean::dec(x_3);
if (lean::obj_tag(x_107) == 0)
{
obj* x_111; obj* x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_126; obj* x_127; 
lean::dec(x_107);
x_111 = lean::cnstr_get(x_2, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_2, 1);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_2, 2);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_2, 3);
lean::inc(x_117);
x_119 = lean::box(0);
x_120 = lean::name_mk_string(x_119, x_21);
x_121 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__5), 7, 2);
lean::closure_set(x_121, 0, x_0);
lean::closure_set(x_121, 1, x_58);
x_122 = l_lean_parser_token__map_insert___rarg(x_117, x_120, x_121);
x_123 = lean::cnstr_get(x_2, 4);
lean::inc(x_123);
lean::dec(x_2);
x_126 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_126, 0, x_111);
lean::cnstr_set(x_126, 1, x_113);
lean::cnstr_set(x_126, 2, x_115);
lean::cnstr_set(x_126, 3, x_122);
lean::cnstr_set(x_126, 4, x_123);
if (lean::is_scalar(x_20)) {
 x_127 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_127 = x_20;
}
lean::cnstr_set(x_127, 0, x_126);
return x_127;
}
else
{
obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_137; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_107);
x_129 = lean::cnstr_get(x_2, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_2, 1);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_2, 2);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_2, 3);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_2, 4);
lean::inc(x_137);
lean::dec(x_2);
x_140 = lean::box(0);
x_141 = lean::name_mk_string(x_140, x_21);
x_142 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(x_58);
x_143 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__1;
lean::inc(x_143);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_143);
lean::cnstr_set(x_145, 1, x_142);
x_146 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_term_sort__app_parser___spec__2), 8, 2);
lean::closure_set(x_146, 0, x_0);
lean::closure_set(x_146, 1, x_145);
x_147 = l_lean_parser_token__map_insert___rarg(x_137, x_141, x_146);
x_148 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_148, 0, x_129);
lean::cnstr_set(x_148, 1, x_131);
lean::cnstr_set(x_148, 2, x_133);
lean::cnstr_set(x_148, 3, x_135);
lean::cnstr_set(x_148, 4, x_147);
if (lean::is_scalar(x_20)) {
 x_149 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_149 = x_20;
}
lean::cnstr_set(x_149, 0, x_148);
return x_149;
}
}
}
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
obj* _init_l_lean_elaborator_command__parser__config_register__notation__parser___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("register_notation_parser: unreachable");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
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
obj* l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_expander_expand__bracketed__binder___main___closed__4;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_8 = x_0;
}
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_20; 
lean::dec(x_15);
lean::dec(x_4);
x_20 = l_lean_elaborator_command__parser__config_register__notation__parser___closed__2;
lean::inc(x_20);
x_9 = x_20;
goto lbl_10;
}
else
{
obj* x_22; obj* x_25; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
lean::dec(x_15);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
x_28 = l_string_trim(x_25);
lean::inc(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_30, 0, x_28);
x_31 = lean::mk_nat_obj(0u);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser___spec__1), 8, 3);
lean::closure_set(x_32, 0, x_28);
lean::closure_set(x_32, 1, x_31);
lean::closure_set(x_32, 2, x_30);
x_11 = x_32;
goto lbl_12;
}
lbl_10:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_8);
lean::dec(x_6);
x_35 = lean::cnstr_get(x_9, 0);
lean::inc(x_35);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_37 = x_9;
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
obj* x_39; obj* x_41; obj* x_42; 
x_39 = lean::cnstr_get(x_9, 0);
lean::inc(x_39);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_41 = x_9;
}
x_42 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2(x_6);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; obj* x_48; 
lean::dec(x_8);
lean::dec(x_39);
x_45 = lean::cnstr_get(x_42, 0);
lean::inc(x_45);
lean::dec(x_42);
if (lean::is_scalar(x_41)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_41;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_52; obj* x_53; 
x_49 = lean::cnstr_get(x_42, 0);
lean::inc(x_49);
lean::dec(x_42);
if (lean::is_scalar(x_8)) {
 x_52 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_52 = x_8;
}
lean::cnstr_set(x_52, 0, x_39);
lean::cnstr_set(x_52, 1, x_49);
if (lean::is_scalar(x_41)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_41;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
}
lbl_12:
{
obj* x_54; obj* x_56; 
x_56 = lean::cnstr_get(x_4, 1);
lean::inc(x_56);
lean::dec(x_4);
if (lean::obj_tag(x_56) == 0)
{
obj* x_60; 
lean::dec(x_56);
x_60 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_60);
x_54 = x_60;
goto lbl_55;
}
else
{
obj* x_62; obj* x_64; 
x_62 = lean::cnstr_get(x_56, 0);
lean::inc(x_62);
if (lean::is_shared(x_56)) {
 lean::dec(x_56);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_56, 0);
 x_64 = x_56;
}
switch (lean::obj_tag(x_62)) {
case 0:
{
obj* x_67; 
lean::dec(x_62);
lean::dec(x_64);
x_67 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1;
lean::inc(x_67);
x_54 = x_67;
goto lbl_55;
}
case 1:
{
obj* x_71; 
lean::dec(x_62);
lean::dec(x_64);
x_71 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2;
lean::inc(x_71);
x_54 = x_71;
goto lbl_55;
}
default:
{
obj* x_73; obj* x_76; 
x_73 = lean::cnstr_get(x_62, 0);
lean::inc(x_73);
lean::dec(x_62);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
if (lean::obj_tag(x_76) == 0)
{
obj* x_81; 
lean::dec(x_64);
lean::dec(x_76);
x_81 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3;
lean::inc(x_81);
x_54 = x_81;
goto lbl_55;
}
else
{
obj* x_83; obj* x_86; 
x_83 = lean::cnstr_get(x_76, 0);
lean::inc(x_83);
lean::dec(x_76);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
lean::dec(x_83);
switch (lean::obj_tag(x_86)) {
case 0:
{
obj* x_89; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_89 = lean::cnstr_get(x_86, 0);
lean::inc(x_89);
lean::dec(x_86);
x_92 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_89);
x_93 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_93, 0, x_92);
if (lean::is_scalar(x_64)) {
 x_94 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_94 = x_64;
}
lean::cnstr_set(x_94, 0, x_93);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
x_54 = x_95;
goto lbl_55;
}
case 1:
{
obj* x_98; 
lean::dec(x_86);
lean::dec(x_64);
x_98 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
lean::inc(x_98);
x_54 = x_98;
goto lbl_55;
}
case 2:
{
obj* x_100; obj* x_103; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_100 = lean::cnstr_get(x_86, 0);
lean::inc(x_100);
lean::dec(x_86);
x_103 = lean::cnstr_get(x_100, 2);
lean::inc(x_103);
lean::dec(x_100);
x_106 = l_lean_elaborator_prec__to__nat___main(x_103);
x_107 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_107, 0, x_106);
if (lean::is_scalar(x_64)) {
 x_108 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_108 = x_64;
}
lean::cnstr_set(x_108, 0, x_107);
x_109 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_109, 0, x_108);
x_54 = x_109;
goto lbl_55;
}
default:
{
obj* x_112; 
lean::dec(x_86);
lean::dec(x_64);
x_112 = l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4;
lean::inc(x_112);
x_54 = x_112;
goto lbl_55;
}
}
}
}
}
}
lbl_55:
{
if (lean::obj_tag(x_54) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_11);
x_115 = lean::cnstr_get(x_54, 0);
lean::inc(x_115);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_117 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_117 = x_54;
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_115);
x_9 = x_118;
goto lbl_10;
}
else
{
obj* x_119; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_119 = lean::cnstr_get(x_54, 0);
lean::inc(x_119);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_121 = x_54;
}
x_122 = l_option_to__monad___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__1___rarg(x_119);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_11);
lean::cnstr_set(x_123, 1, x_122);
if (lean::is_scalar(x_121)) {
 x_124 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_124 = x_121;
}
lean::cnstr_set(x_124, 0, x_123);
x_9 = x_124;
goto lbl_10;
}
}
}
}
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
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
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
x_8 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__3(x_5);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4), 7, 1);
lean::closure_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__5(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_lean_elaborator_command__parser__config_register__notation__parser___spec__4), 7, 1);
lean::closure_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__6(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
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
x_35 = l_list_append___main___rarg(x_28, x_32);
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
obj* l_list_mfoldl___main___at_lean_elaborator_update__parser__config___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_3);
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
obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_24; 
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_18 = x_15;
}
x_19 = l_lean_parser_command_reserve__notation_has__view;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
x_22 = lean::apply_1(x_20, x_8);
lean::inc(x_2);
x_24 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_22, x_16, x_2, x_3);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_30; 
lean::dec(x_10);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
lean::dec(x_24);
if (lean::is_scalar(x_18)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_18;
}
lean::cnstr_set(x_30, 0, x_27);
return x_30;
}
else
{
obj* x_32; obj* x_35; obj* x_37; 
lean::dec(x_18);
x_32 = lean::cnstr_get(x_24, 0);
lean::inc(x_32);
lean::dec(x_24);
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
lean::dec(x_32);
x_0 = x_35;
x_1 = x_10;
x_3 = x_37;
goto _start;
}
}
else
{
obj* x_42; 
lean::dec(x_8);
x_42 = lean::cnstr_get(x_15, 0);
lean::inc(x_42);
lean::dec(x_15);
x_0 = x_42;
x_1 = x_10;
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
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_3);
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
obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; 
lean::dec(x_8);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_21 = x_17;
}
x_22 = l_lean_parser_command_notation_has__view;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
x_25 = lean::apply_1(x_23, x_13);
lean::inc(x_2);
x_27 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_25, x_19, x_2, x_3);
if (lean::obj_tag(x_27) == 0)
{
obj* x_30; obj* x_33; 
lean::dec(x_10);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
lean::dec(x_27);
if (lean::is_scalar(x_21)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_21;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
lean::dec(x_21);
x_35 = lean::cnstr_get(x_27, 0);
lean::inc(x_35);
lean::dec(x_27);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
x_0 = x_38;
x_1 = x_10;
x_3 = x_40;
goto _start;
}
}
else
{
obj* x_44; obj* x_46; obj* x_47; obj* x_51; 
x_44 = lean::cnstr_get(x_17, 0);
lean::inc(x_44);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_46 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_46 = x_17;
}
x_47 = lean::cnstr_get(x_8, 0);
lean::inc(x_47);
lean::dec(x_8);
lean::inc(x_13);
x_51 = l_lean_elaborator_command__parser__config_register__notation__parser(x_47, x_13, x_44);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_55; obj* x_56; obj* x_58; obj* x_60; 
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
lean::dec(x_51);
x_55 = l_lean_parser_command_notation_has__view;
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_58 = lean::apply_1(x_56, x_13);
lean::inc(x_2);
x_60 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_58, x_52, x_2, x_3);
if (lean::obj_tag(x_60) == 0)
{
obj* x_63; obj* x_66; 
lean::dec(x_10);
lean::dec(x_2);
x_63 = lean::cnstr_get(x_60, 0);
lean::inc(x_63);
lean::dec(x_60);
if (lean::is_scalar(x_46)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_46;
}
lean::cnstr_set(x_66, 0, x_63);
return x_66;
}
else
{
obj* x_68; obj* x_71; obj* x_73; 
lean::dec(x_46);
x_68 = lean::cnstr_get(x_60, 0);
lean::inc(x_68);
lean::dec(x_60);
x_71 = lean::cnstr_get(x_68, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
lean::dec(x_68);
x_0 = x_71;
x_1 = x_10;
x_3 = x_73;
goto _start;
}
}
else
{
obj* x_79; 
lean::dec(x_13);
lean::dec(x_46);
x_79 = lean::cnstr_get(x_51, 0);
lean::inc(x_79);
lean::dec(x_51);
x_0 = x_79;
x_1 = x_10;
goto _start;
}
}
}
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
lean::dec(x_1);
lean::dec(x_3);
return x_0;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_11 = x_3;
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_16 = x_7;
}
x_17 = lean::cnstr_get(x_12, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_12, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_12, 2);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_12, 3);
lean::inc(x_23);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 lean::cnstr_release(x_12, 2);
 lean::cnstr_release(x_12, 3);
 x_25 = x_12;
}
if (lean::obj_tag(x_23) == 0)
{
obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_0);
lean::dec(x_23);
x_28 = l_lean_elaborator_postprocess__notation__spec___closed__1;
lean::inc(x_28);
if (lean::is_scalar(x_25)) {
 x_30 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_30 = x_25;
}
lean::cnstr_set(x_30, 0, x_17);
lean::cnstr_set(x_30, 1, x_19);
lean::cnstr_set(x_30, 2, x_21);
lean::cnstr_set(x_30, 3, x_28);
if (lean::is_scalar(x_16)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_16;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_14);
if (lean::is_scalar(x_11)) {
 x_32 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_32 = x_11;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_9);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
else
{
lean::dec(x_11);
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_16);
lean::dec(x_19);
lean::dec(x_14);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_23);
lean::dec(x_25);
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
unsigned char l_lean_elaborator_match__precedence___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
unsigned char x_4; 
lean::dec(x_1);
x_4 = 0;
return x_4;
}
else
{
unsigned char x_6; 
lean::dec(x_1);
x_6 = 1;
return x_6;
}
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
unsigned char x_12; 
lean::dec(x_7);
lean::dec(x_1);
x_12 = 0;
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
lean::dec(x_7);
x_19 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_16);
x_20 = lean::cnstr_get(x_13, 1);
lean::inc(x_20);
lean::dec(x_13);
x_23 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_20);
x_24 = lean::nat_dec_eq(x_19, x_23);
lean::dec(x_23);
lean::dec(x_19);
if (lean::obj_tag(x_24) == 0)
{
unsigned char x_28; 
lean::dec(x_24);
x_28 = 0;
return x_28;
}
else
{
unsigned char x_30; 
lean::dec(x_24);
x_30 = 1;
return x_30;
}
}
}
}
}
obj* l_lean_elaborator_match__precedence___main___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; 
x_2 = l_lean_elaborator_match__precedence___main(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char l_lean_elaborator_match__precedence(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; 
x_2 = l_lean_elaborator_match__precedence___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_match__precedence___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; 
x_2 = l_lean_elaborator_match__precedence(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_lean_elaborator_match__spec(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; unsigned char x_7; obj* x_8; unsigned char x_10; 
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
obj* x_34; 
lean::dec(x_2);
lean::dec(x_31);
x_34 = lean::box(0);
return x_34;
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 x_37 = x_31;
}
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_2);
lean::cnstr_set(x_38, 1, x_35);
if (lean::is_scalar(x_37)) {
 x_39 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_39 = x_37;
}
lean::cnstr_set(x_39, 0, x_38);
return x_39;
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
obj* l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_parser_syntax_reprint__lst___main___closed__1;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_20; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_8 = x_0;
}
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_4, 1);
lean::inc(x_13);
lean::dec(x_4);
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_16, 3);
lean::inc(x_20);
lean::dec(x_16);
if (lean::obj_tag(x_18) == 0)
{
obj* x_29; 
lean::dec(x_8);
lean::dec(x_20);
lean::dec(x_13);
lean::dec(x_18);
lean::dec(x_11);
lean::dec(x_6);
x_29 = lean::box(0);
return x_29;
}
else
{
obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_41; 
x_30 = lean::cnstr_get(x_18, 0);
lean::inc(x_30);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_32 = x_18;
}
x_33 = lean::cnstr_get(x_13, 0);
lean::inc(x_33);
x_39 = lean::cnstr_get(x_33, 1);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_33, 3);
lean::inc(x_41);
if (lean::obj_tag(x_39) == 0)
{
obj* x_51; 
lean::dec(x_32);
lean::dec(x_33);
lean::dec(x_20);
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_30);
lean::dec(x_39);
lean::dec(x_41);
x_51 = lean::box(0);
x_9 = x_51;
goto lbl_10;
}
else
{
obj* x_52; obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; 
x_52 = lean::cnstr_get(x_39, 0);
lean::inc(x_52);
lean::dec(x_39);
x_55 = lean::cnstr_get(x_30, 1);
lean::inc(x_55);
lean::dec(x_30);
x_58 = l_string_trim(x_55);
x_59 = lean::cnstr_get(x_52, 1);
lean::inc(x_59);
lean::dec(x_52);
x_62 = l_string_trim(x_59);
x_63 = lean::string_dec_eq(x_58, x_62);
lean::dec(x_62);
lean::dec(x_58);
if (lean::obj_tag(x_63) == 0)
{
obj* x_73; 
lean::dec(x_32);
lean::dec(x_33);
lean::dec(x_20);
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_63);
lean::dec(x_41);
x_73 = lean::box(0);
x_9 = x_73;
goto lbl_10;
}
else
{
unsigned char x_75; 
lean::dec(x_63);
x_75 = l_lean_elaborator_match__precedence___main(x_20, x_41);
if (x_75 == 0)
{
obj* x_80; 
lean::dec(x_32);
lean::dec(x_33);
lean::dec(x_13);
lean::dec(x_11);
x_80 = lean::box(0);
x_9 = x_80;
goto lbl_10;
}
else
{
obj* x_81; 
x_81 = lean::box(0);
x_37 = x_81;
goto lbl_38;
}
}
}
lbl_36:
{
if (lean::obj_tag(x_35) == 0)
{
obj* x_85; 
lean::dec(x_32);
lean::dec(x_33);
lean::dec(x_35);
x_85 = lean::box(0);
x_9 = x_85;
goto lbl_10;
}
else
{
obj* x_86; obj* x_89; obj* x_90; 
x_86 = lean::cnstr_get(x_35, 0);
lean::inc(x_86);
lean::dec(x_35);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_33);
lean::cnstr_set(x_89, 1, x_86);
if (lean::is_scalar(x_32)) {
 x_90 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_90 = x_32;
}
lean::cnstr_set(x_90, 0, x_89);
x_9 = x_90;
goto lbl_10;
}
}
lbl_38:
{
obj* x_92; 
lean::dec(x_37);
x_92 = lean::cnstr_get(x_11, 1);
lean::inc(x_92);
lean::dec(x_11);
if (lean::obj_tag(x_92) == 0)
{
obj* x_96; 
lean::dec(x_92);
x_96 = lean::cnstr_get(x_13, 1);
lean::inc(x_96);
lean::dec(x_13);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; 
x_99 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_99, 0, x_96);
x_35 = x_99;
goto lbl_36;
}
else
{
obj* x_101; 
lean::dec(x_96);
x_101 = lean::box(0);
x_35 = x_101;
goto lbl_36;
}
}
else
{
obj* x_102; obj* x_104; 
x_102 = lean::cnstr_get(x_92, 0);
lean::inc(x_102);
if (lean::is_shared(x_92)) {
 lean::dec(x_92);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_92, 0);
 x_104 = x_92;
}
switch (lean::obj_tag(x_102)) {
case 0:
{
obj* x_105; obj* x_108; 
x_105 = lean::cnstr_get(x_102, 0);
lean::inc(x_105);
lean::dec(x_102);
x_108 = lean::cnstr_get(x_13, 1);
lean::inc(x_108);
lean::dec(x_13);
if (lean::obj_tag(x_108) == 0)
{
obj* x_114; 
lean::dec(x_104);
lean::dec(x_105);
lean::dec(x_108);
x_114 = lean::box(0);
x_35 = x_114;
goto lbl_36;
}
else
{
obj* x_115; 
x_115 = lean::cnstr_get(x_108, 0);
lean::inc(x_115);
switch (lean::obj_tag(x_115)) {
case 0:
{
obj* x_117; obj* x_120; obj* x_123; unsigned char x_126; 
x_117 = lean::cnstr_get(x_115, 0);
lean::inc(x_117);
lean::dec(x_115);
x_120 = lean::cnstr_get(x_105, 1);
lean::inc(x_120);
lean::dec(x_105);
x_123 = lean::cnstr_get(x_117, 1);
lean::inc(x_123);
lean::dec(x_117);
x_126 = l_lean_elaborator_match__precedence___main(x_120, x_123);
if (x_126 == 0)
{
obj* x_129; 
lean::dec(x_104);
lean::dec(x_108);
x_129 = lean::box(0);
x_35 = x_129;
goto lbl_36;
}
else
{
obj* x_130; 
if (lean::is_scalar(x_104)) {
 x_130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_130 = x_104;
}
lean::cnstr_set(x_130, 0, x_108);
x_35 = x_130;
goto lbl_36;
}
}
case 1:
{
obj* x_135; 
lean::dec(x_104);
lean::dec(x_105);
lean::dec(x_108);
lean::dec(x_115);
x_135 = lean::box(0);
x_35 = x_135;
goto lbl_36;
}
default:
{
obj* x_140; 
lean::dec(x_104);
lean::dec(x_105);
lean::dec(x_108);
lean::dec(x_115);
x_140 = lean::box(0);
x_35 = x_140;
goto lbl_36;
}
}
}
}
case 1:
{
obj* x_141; obj* x_144; 
x_141 = lean::cnstr_get(x_102, 0);
lean::inc(x_141);
lean::dec(x_102);
x_144 = lean::cnstr_get(x_13, 1);
lean::inc(x_144);
lean::dec(x_13);
if (lean::obj_tag(x_144) == 0)
{
obj* x_150; 
lean::dec(x_104);
lean::dec(x_144);
lean::dec(x_141);
x_150 = lean::box(0);
x_35 = x_150;
goto lbl_36;
}
else
{
obj* x_151; 
x_151 = lean::cnstr_get(x_144, 0);
lean::inc(x_151);
switch (lean::obj_tag(x_151)) {
case 0:
{
obj* x_157; 
lean::dec(x_104);
lean::dec(x_144);
lean::dec(x_141);
lean::dec(x_151);
x_157 = lean::box(0);
x_35 = x_157;
goto lbl_36;
}
case 1:
{
obj* x_158; obj* x_161; obj* x_164; unsigned char x_167; 
x_158 = lean::cnstr_get(x_151, 0);
lean::inc(x_158);
lean::dec(x_151);
x_161 = lean::cnstr_get(x_141, 1);
lean::inc(x_161);
lean::dec(x_141);
x_164 = lean::cnstr_get(x_158, 1);
lean::inc(x_164);
lean::dec(x_158);
x_167 = l_lean_elaborator_match__precedence___main(x_161, x_164);
if (x_167 == 0)
{
obj* x_170; 
lean::dec(x_104);
lean::dec(x_144);
x_170 = lean::box(0);
x_35 = x_170;
goto lbl_36;
}
else
{
obj* x_171; 
if (lean::is_scalar(x_104)) {
 x_171 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_171 = x_104;
}
lean::cnstr_set(x_171, 0, x_144);
x_35 = x_171;
goto lbl_36;
}
}
default:
{
obj* x_176; 
lean::dec(x_104);
lean::dec(x_144);
lean::dec(x_141);
lean::dec(x_151);
x_176 = lean::box(0);
x_35 = x_176;
goto lbl_36;
}
}
}
}
default:
{
obj* x_177; obj* x_179; obj* x_180; obj* x_182; 
x_177 = lean::cnstr_get(x_102, 0);
lean::inc(x_177);
if (lean::is_shared(x_102)) {
 lean::dec(x_102);
 x_179 = lean::box(0);
} else {
 lean::cnstr_release(x_102, 0);
 x_179 = x_102;
}
x_182 = lean::cnstr_get(x_13, 1);
lean::inc(x_182);
lean::dec(x_13);
if (lean::obj_tag(x_182) == 0)
{
obj* x_189; 
lean::dec(x_104);
lean::dec(x_182);
lean::dec(x_177);
lean::dec(x_179);
x_189 = lean::box(0);
x_35 = x_189;
goto lbl_36;
}
else
{
obj* x_190; obj* x_192; 
x_190 = lean::cnstr_get(x_182, 0);
lean::inc(x_190);
if (lean::is_shared(x_182)) {
 lean::dec(x_182);
 x_192 = lean::box(0);
} else {
 lean::cnstr_release(x_182, 0);
 x_192 = x_182;
}
switch (lean::obj_tag(x_190)) {
case 0:
{
obj* x_198; 
lean::dec(x_104);
lean::dec(x_177);
lean::dec(x_179);
lean::dec(x_192);
lean::dec(x_190);
x_198 = lean::box(0);
x_35 = x_198;
goto lbl_36;
}
case 1:
{
obj* x_204; 
lean::dec(x_104);
lean::dec(x_177);
lean::dec(x_179);
lean::dec(x_192);
lean::dec(x_190);
x_204 = lean::box(0);
x_35 = x_204;
goto lbl_36;
}
default:
{
obj* x_205; obj* x_208; obj* x_210; obj* x_213; 
x_205 = lean::cnstr_get(x_190, 0);
lean::inc(x_205);
lean::dec(x_190);
x_208 = lean::cnstr_get(x_177, 1);
lean::inc(x_208);
x_210 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1;
lean::inc(x_208);
lean::inc(x_210);
x_213 = l_option_map___rarg(x_210, x_208);
if (lean::obj_tag(x_213) == 0)
{
obj* x_216; obj* x_221; 
lean::dec(x_213);
lean::dec(x_208);
x_216 = lean::cnstr_get(x_205, 1);
lean::inc(x_216);
lean::dec(x_205);
lean::inc(x_216);
lean::inc(x_210);
x_221 = l_option_map___rarg(x_210, x_216);
if (lean::obj_tag(x_221) == 0)
{
obj* x_225; 
lean::dec(x_221);
lean::dec(x_216);
lean::dec(x_192);
x_225 = lean::box(0);
x_180 = x_225;
goto lbl_181;
}
else
{
obj* x_226; 
x_226 = lean::cnstr_get(x_221, 0);
lean::inc(x_226);
lean::dec(x_221);
switch (lean::obj_tag(x_226)) {
case 0:
{
obj* x_230; 
lean::dec(x_226);
if (lean::is_scalar(x_192)) {
 x_230 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_230 = x_192;
}
lean::cnstr_set(x_230, 0, x_216);
x_180 = x_230;
goto lbl_181;
}
case 1:
{
obj* x_234; 
lean::dec(x_226);
lean::dec(x_216);
lean::dec(x_192);
x_234 = lean::box(0);
x_180 = x_234;
goto lbl_181;
}
case 2:
{
obj* x_238; 
lean::dec(x_226);
lean::dec(x_216);
lean::dec(x_192);
x_238 = lean::box(0);
x_180 = x_238;
goto lbl_181;
}
default:
{
obj* x_242; 
lean::dec(x_226);
lean::dec(x_216);
lean::dec(x_192);
x_242 = lean::box(0);
x_180 = x_242;
goto lbl_181;
}
}
}
}
else
{
obj* x_243; 
x_243 = lean::cnstr_get(x_213, 0);
lean::inc(x_243);
lean::dec(x_213);
switch (lean::obj_tag(x_243)) {
case 0:
{
obj* x_246; obj* x_249; obj* x_253; 
x_246 = lean::cnstr_get(x_243, 0);
lean::inc(x_246);
lean::dec(x_243);
x_249 = lean::cnstr_get(x_205, 1);
lean::inc(x_249);
lean::dec(x_205);
lean::inc(x_210);
x_253 = l_option_map___rarg(x_210, x_249);
if (lean::obj_tag(x_253) == 0)
{
obj* x_258; 
lean::dec(x_253);
lean::dec(x_246);
lean::dec(x_192);
lean::dec(x_208);
x_258 = lean::box(0);
x_180 = x_258;
goto lbl_181;
}
else
{
obj* x_259; 
x_259 = lean::cnstr_get(x_253, 0);
lean::inc(x_259);
lean::dec(x_253);
switch (lean::obj_tag(x_259)) {
case 0:
{
obj* x_262; obj* x_265; obj* x_266; obj* x_267; 
x_262 = lean::cnstr_get(x_259, 0);
lean::inc(x_262);
lean::dec(x_259);
x_265 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_246);
x_266 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_262);
x_267 = lean::nat_dec_eq(x_265, x_266);
lean::dec(x_266);
lean::dec(x_265);
if (lean::obj_tag(x_267) == 0)
{
obj* x_273; 
lean::dec(x_267);
lean::dec(x_192);
lean::dec(x_208);
x_273 = lean::box(0);
x_180 = x_273;
goto lbl_181;
}
else
{
obj* x_275; 
lean::dec(x_267);
if (lean::is_scalar(x_192)) {
 x_275 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_275 = x_192;
}
lean::cnstr_set(x_275, 0, x_208);
x_180 = x_275;
goto lbl_181;
}
}
case 1:
{
obj* x_280; 
lean::dec(x_246);
lean::dec(x_259);
lean::dec(x_192);
lean::dec(x_208);
x_280 = lean::box(0);
x_180 = x_280;
goto lbl_181;
}
case 2:
{
obj* x_285; 
lean::dec(x_246);
lean::dec(x_259);
lean::dec(x_192);
lean::dec(x_208);
x_285 = lean::box(0);
x_180 = x_285;
goto lbl_181;
}
default:
{
obj* x_290; 
lean::dec(x_246);
lean::dec(x_259);
lean::dec(x_192);
lean::dec(x_208);
x_290 = lean::box(0);
x_180 = x_290;
goto lbl_181;
}
}
}
}
case 1:
{
obj* x_295; 
lean::dec(x_243);
lean::dec(x_205);
lean::dec(x_192);
lean::dec(x_208);
x_295 = lean::box(0);
x_180 = x_295;
goto lbl_181;
}
case 2:
{
obj* x_300; 
lean::dec(x_243);
lean::dec(x_205);
lean::dec(x_192);
lean::dec(x_208);
x_300 = lean::box(0);
x_180 = x_300;
goto lbl_181;
}
default:
{
obj* x_305; 
lean::dec(x_243);
lean::dec(x_205);
lean::dec(x_192);
lean::dec(x_208);
x_305 = lean::box(0);
x_180 = x_305;
goto lbl_181;
}
}
}
}
}
}
lbl_181:
{
if (lean::obj_tag(x_180) == 0)
{
obj* x_310; 
lean::dec(x_180);
lean::dec(x_104);
lean::dec(x_177);
lean::dec(x_179);
x_310 = lean::box(0);
x_35 = x_310;
goto lbl_36;
}
else
{
obj* x_311; obj* x_313; obj* x_314; obj* x_317; obj* x_318; obj* x_319; obj* x_320; 
x_311 = lean::cnstr_get(x_180, 0);
lean::inc(x_311);
if (lean::is_shared(x_180)) {
 lean::dec(x_180);
 x_313 = lean::box(0);
} else {
 lean::cnstr_release(x_180, 0);
 x_313 = x_180;
}
x_314 = lean::cnstr_get(x_177, 0);
lean::inc(x_314);
lean::dec(x_177);
x_317 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_317, 0, x_314);
lean::cnstr_set(x_317, 1, x_311);
if (lean::is_scalar(x_179)) {
 x_318 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_318 = x_179;
}
lean::cnstr_set(x_318, 0, x_317);
if (lean::is_scalar(x_104)) {
 x_319 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_319 = x_104;
}
lean::cnstr_set(x_319, 0, x_318);
if (lean::is_scalar(x_313)) {
 x_320 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_320 = x_313;
}
lean::cnstr_set(x_320, 0, x_319);
x_35 = x_320;
goto lbl_36;
}
}
}
}
}
}
}
lbl_10:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_324; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_9);
x_324 = lean::box(0);
return x_324;
}
else
{
obj* x_325; obj* x_327; obj* x_328; 
x_325 = lean::cnstr_get(x_9, 0);
lean::inc(x_325);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_327 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_327 = x_9;
}
x_328 = l_list_mmap___main___at_lean_elaborator_match__spec___spec__1(x_6);
if (lean::obj_tag(x_328) == 0)
{
obj* x_333; 
lean::dec(x_325);
lean::dec(x_327);
lean::dec(x_328);
lean::dec(x_8);
x_333 = lean::box(0);
return x_333;
}
else
{
obj* x_334; obj* x_337; obj* x_338; 
x_334 = lean::cnstr_get(x_328, 0);
lean::inc(x_334);
lean::dec(x_328);
if (lean::is_scalar(x_8)) {
 x_337 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_337 = x_8;
}
lean::cnstr_set(x_337, 0, x_325);
lean::cnstr_set(x_337, 1, x_334);
if (lean::is_scalar(x_327)) {
 x_338 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_338 = x_327;
}
lean::cnstr_set(x_338, 0, x_337);
return x_338;
}
}
}
}
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_7);
lean::dec(x_1);
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
lean::cnstr_set(x_23, 1, x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_7, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_7, 1);
lean::inc(x_27);
lean::dec(x_7);
if (lean::obj_tag(x_27) == 0)
{
obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_1);
lean::dec(x_27);
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 3);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_0, 4);
lean::inc(x_38);
lean::dec(x_0);
x_41 = l_lean_elaborator_postprocess__notation__spec(x_25);
x_42 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_42, 0, x_32);
lean::cnstr_set(x_42, 1, x_34);
lean::cnstr_set(x_42, 2, x_41);
lean::cnstr_set(x_42, 3, x_36);
lean::cnstr_set(x_42, 4, x_38);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_2);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
return x_44;
}
else
{
obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_53; 
lean::dec(x_25);
lean::dec(x_27);
x_47 = l_lean_parser_command_notation_has__view;
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
x_50 = lean::apply_1(x_48, x_0);
x_51 = l_lean_elaborator_notation_elaborate__aux___closed__1;
lean::inc(x_51);
x_53 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_50, x_51, x_1, x_2);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_56; obj* x_57; 
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_56 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_56 = x_53;
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
x_58 = lean::cnstr_get(x_53, 0);
lean::inc(x_58);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_60 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_60 = x_53;
}
x_61 = lean::cnstr_get(x_58, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_58, 1);
lean::inc(x_63);
if (lean::is_shared(x_58)) {
 lean::dec(x_58);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 x_65 = x_58;
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
obj* _init_l_lean_elaborator_notation_elaborate__aux___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid notation, matches multiple reserved notations");
return x_0;
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
x_30 = lean::name_mk_numeral(x_28, x_5);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_27);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
}
obj* _init_l_lean_elaborator_mk__notation__kind___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_notation");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
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
obj* l_rbmap_insert___main___at_lean_elaborator_register__notation__macro___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_elaborator_notation_elaborate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; unsigned char x_14; 
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
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_34; unsigned char x_35; obj* x_36; obj* x_37; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_60; 
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
obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_118; obj* x_120; obj* x_123; obj* x_124; 
lean::dec(x_95);
x_99 = lean::cnstr_get(x_92, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_92, 1);
lean::inc(x_101);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_90);
lean::cnstr_set(x_103, 1, x_101);
x_104 = lean::cnstr_get(x_92, 2);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_92, 3);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_92, 4);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_92, 5);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_92, 6);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_92, 7);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_92, 8);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_92, 9);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_92, 10);
lean::inc(x_120);
lean::dec(x_92);
x_123 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_123, 0, x_99);
lean::cnstr_set(x_123, 1, x_103);
lean::cnstr_set(x_123, 2, x_104);
lean::cnstr_set(x_123, 3, x_106);
lean::cnstr_set(x_123, 4, x_108);
lean::cnstr_set(x_123, 5, x_110);
lean::cnstr_set(x_123, 6, x_112);
lean::cnstr_set(x_123, 7, x_114);
lean::cnstr_set(x_123, 8, x_116);
lean::cnstr_set(x_123, 9, x_118);
lean::cnstr_set(x_123, 10, x_120);
x_124 = l_lean_elaborator_update__parser__config(x_1, x_123);
return x_124;
}
else
{
obj* x_126; obj* x_128; obj* x_130; obj* x_132; obj* x_134; obj* x_136; obj* x_138; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_147; obj* x_149; obj* x_152; obj* x_153; obj* x_155; obj* x_157; obj* x_159; obj* x_161; obj* x_163; obj* x_166; obj* x_167; 
lean::dec(x_95);
x_126 = lean::cnstr_get(x_92, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_92, 1);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_92, 2);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_92, 3);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_92, 4);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_134, 0);
lean::inc(x_136);
x_138 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_138, 0, x_90);
lean::cnstr_set(x_138, 1, x_136);
x_139 = lean::cnstr_get(x_134, 1);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_134, 2);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_134, 3);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_134, 4);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_134, 5);
lean::inc(x_147);
x_149 = lean::cnstr_get(x_134, 6);
lean::inc(x_149);
lean::dec(x_134);
x_152 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_152, 0, x_138);
lean::cnstr_set(x_152, 1, x_139);
lean::cnstr_set(x_152, 2, x_141);
lean::cnstr_set(x_152, 3, x_143);
lean::cnstr_set(x_152, 4, x_145);
lean::cnstr_set(x_152, 5, x_147);
lean::cnstr_set(x_152, 6, x_149);
x_153 = lean::cnstr_get(x_92, 5);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_92, 6);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_92, 7);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_92, 8);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_92, 9);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_92, 10);
lean::inc(x_163);
lean::dec(x_92);
x_166 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_166, 0, x_126);
lean::cnstr_set(x_166, 1, x_128);
lean::cnstr_set(x_166, 2, x_130);
lean::cnstr_set(x_166, 3, x_132);
lean::cnstr_set(x_166, 4, x_152);
lean::cnstr_set(x_166, 5, x_153);
lean::cnstr_set(x_166, 6, x_155);
lean::cnstr_set(x_166, 7, x_157);
lean::cnstr_set(x_166, 8, x_159);
lean::cnstr_set(x_166, 9, x_161);
lean::cnstr_set(x_166, 10, x_163);
x_167 = l_lean_elaborator_update__parser__config(x_1, x_166);
return x_167;
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
unsigned char l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
unsigned char x_2; 
lean::dec(x_0);
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_5; unsigned char x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_5);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_9);
x_0 = x_5;
goto _start;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
switch (lean::obj_tag(x_13)) {
case 0:
{
lean::dec(x_13);
x_0 = x_5;
goto _start;
}
case 1:
{
lean::dec(x_13);
x_0 = x_5;
goto _start;
}
default:
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_13, 0);
lean::inc(x_18);
lean::dec(x_13);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
if (lean::obj_tag(x_21) == 0)
{
lean::dec(x_21);
x_0 = x_5;
goto _start;
}
else
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_21, 0);
lean::inc(x_25);
lean::dec(x_21);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
switch (lean::obj_tag(x_28)) {
case 0:
{
lean::dec(x_28);
x_0 = x_5;
goto _start;
}
case 1:
{
lean::dec(x_28);
x_0 = x_5;
goto _start;
}
case 2:
{
lean::dec(x_28);
x_0 = x_5;
goto _start;
}
default:
{
unsigned char x_35; 
lean::dec(x_28);
x_35 = 1;
return x_35;
}
}
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
unsigned char x_1; obj* x_2; 
x_1 = l_list_foldr___main___at_lean_elaborator_notation_elaborate___spec__1(x_0);
x_2 = lean::box(x_1);
return x_2;
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
obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_18);
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
x_30 = lean::cnstr_get(x_12, 0);
lean::inc(x_30);
lean::inc(x_11);
x_33 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_33, 0, x_11);
x_34 = l_lean_elaborator_ordered__rbmap_insert___at_lean_elaborator_elab__def__like___spec__4(x_14, x_11, x_33);
x_35 = lean::cnstr_get(x_12, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_12, 3);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_12, 4);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_12, 5);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_12, 6);
lean::inc(x_43);
lean::dec(x_12);
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
obj* x_67; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_18);
x_67 = l_lean_name_to__string___closed__1;
lean::inc(x_67);
x_69 = l_lean_name_to__string__with__sep___main(x_67, x_11);
x_70 = l_lean_elaborator_universe_elaborate___closed__1;
lean::inc(x_70);
x_72 = lean::string_append(x_70, x_69);
lean::dec(x_69);
x_74 = l_lean_elaborator_universe_elaborate___closed__2;
x_75 = lean::string_append(x_72, x_74);
x_76 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_0, x_75, x_1, x_2);
return x_76;
}
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
}
lean::cnstr_set(x_38, 0, x_35);
return x_38;
}
else
{
obj* x_40; obj* x_43; obj* x_45; obj* x_48; unsigned char x_51; obj* x_52; obj* x_53; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
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
x_60 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_60, 0, x_22);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_61, 0, x_56);
lean::cnstr_set(x_61, 1, x_60);
x_62 = l_lean_elaborator_old__elab__command(x_0, x_61, x_1, x_45);
return x_62;
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
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string("attribute");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
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
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
x_13 = lean::cnstr_get(x_8, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_18; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_31; 
lean::dec(x_13);
lean::inc(x_8);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_8);
x_18 = lean::cnstr_get(x_8, 2);
lean::inc(x_18);
lean::dec(x_8);
x_21 = l_lean_name_to__string___closed__1;
lean::inc(x_21);
x_23 = l_lean_name_to__string__with__sep___main(x_21, x_18);
x_24 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1;
lean::inc(x_24);
x_26 = lean::string_append(x_24, x_23);
lean::dec(x_23);
x_28 = l_char_has__repr___closed__1;
x_29 = lean::string_append(x_26, x_28);
lean::inc(x_1);
x_31 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_17, x_29, x_1, x_2);
if (lean::obj_tag(x_31) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 x_37 = x_31;
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_31, 0);
lean::inc(x_39);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 x_41 = x_31;
}
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
if (lean::is_shared(x_39)) {
 lean::dec(x_39);
 x_46 = lean::box(0);
} else {
 lean::cnstr_release(x_39, 0);
 lean::cnstr_release(x_39, 1);
 x_46 = x_39;
}
x_47 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_10, x_1, x_44);
if (lean::obj_tag(x_47) == 0)
{
obj* x_51; obj* x_54; 
lean::dec(x_12);
lean::dec(x_42);
lean::dec(x_46);
x_51 = lean::cnstr_get(x_47, 0);
lean::inc(x_51);
lean::dec(x_47);
if (lean::is_scalar(x_41)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_41;
}
lean::cnstr_set(x_54, 0, x_51);
return x_54;
}
else
{
obj* x_55; obj* x_58; obj* x_60; obj* x_63; obj* x_64; obj* x_65; 
x_55 = lean::cnstr_get(x_47, 0);
lean::inc(x_55);
lean::dec(x_47);
x_58 = lean::cnstr_get(x_55, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_55, 1);
lean::inc(x_60);
lean::dec(x_55);
if (lean::is_scalar(x_12)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_12;
}
lean::cnstr_set(x_63, 0, x_42);
lean::cnstr_set(x_63, 1, x_58);
if (lean::is_scalar(x_46)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_46;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_60);
if (lean::is_scalar(x_41)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_41;
}
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
obj* x_66; obj* x_68; 
x_66 = lean::cnstr_get(x_13, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_13, 1);
lean::inc(x_68);
lean::dec(x_13);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; 
lean::dec(x_8);
lean::dec(x_68);
x_73 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_10, x_1, x_2);
if (lean::obj_tag(x_73) == 0)
{
obj* x_76; obj* x_78; obj* x_79; 
lean::dec(x_12);
lean::dec(x_66);
x_76 = lean::cnstr_get(x_73, 0);
lean::inc(x_76);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_78 = x_73;
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_76);
return x_79;
}
else
{
obj* x_80; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_80 = lean::cnstr_get(x_73, 0);
lean::inc(x_80);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_82 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_82 = x_73;
}
x_83 = lean::cnstr_get(x_80, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_80, 1);
lean::inc(x_85);
if (lean::is_shared(x_80)) {
 lean::dec(x_80);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_80, 0);
 lean::cnstr_release(x_80, 1);
 x_87 = x_80;
}
x_88 = lean::box(0);
x_89 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_89, 0, x_66);
lean::cnstr_set(x_89, 1, x_88);
if (lean::is_scalar(x_12)) {
 x_90 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_90 = x_12;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_83);
if (lean::is_scalar(x_87)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_87;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_85);
if (lean::is_scalar(x_82)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_82;
}
lean::cnstr_set(x_92, 0, x_91);
return x_92;
}
}
else
{
obj* x_95; obj* x_96; obj* x_99; 
lean::dec(x_68);
lean::dec(x_66);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_8);
x_96 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2;
lean::inc(x_1);
lean::inc(x_96);
x_99 = l_lean_expander_error___at_lean_elaborator_level__get__app__args___main___spec__1___rarg(x_95, x_96, x_1, x_2);
if (lean::obj_tag(x_99) == 0)
{
obj* x_103; obj* x_105; obj* x_106; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_103 = lean::cnstr_get(x_99, 0);
lean::inc(x_103);
if (lean::is_shared(x_99)) {
 lean::dec(x_99);
 x_105 = lean::box(0);
} else {
 lean::cnstr_release(x_99, 0);
 x_105 = x_99;
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_103);
return x_106;
}
else
{
obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_114; obj* x_115; 
x_107 = lean::cnstr_get(x_99, 0);
lean::inc(x_107);
if (lean::is_shared(x_99)) {
 lean::dec(x_99);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_99, 0);
 x_109 = x_99;
}
x_110 = lean::cnstr_get(x_107, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_107, 1);
lean::inc(x_112);
if (lean::is_shared(x_107)) {
 lean::dec(x_107);
 x_114 = lean::box(0);
} else {
 lean::cnstr_release(x_107, 0);
 lean::cnstr_release(x_107, 1);
 x_114 = x_107;
}
x_115 = l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1(x_10, x_1, x_112);
if (lean::obj_tag(x_115) == 0)
{
obj* x_119; obj* x_122; 
lean::dec(x_12);
lean::dec(x_114);
lean::dec(x_110);
x_119 = lean::cnstr_get(x_115, 0);
lean::inc(x_119);
lean::dec(x_115);
if (lean::is_scalar(x_109)) {
 x_122 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_122 = x_109;
}
lean::cnstr_set(x_122, 0, x_119);
return x_122;
}
else
{
obj* x_123; obj* x_126; obj* x_128; obj* x_131; obj* x_132; obj* x_133; 
x_123 = lean::cnstr_get(x_115, 0);
lean::inc(x_123);
lean::dec(x_115);
x_126 = lean::cnstr_get(x_123, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_123, 1);
lean::inc(x_128);
lean::dec(x_123);
if (lean::is_scalar(x_12)) {
 x_131 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_131 = x_12;
}
lean::cnstr_set(x_131, 0, x_110);
lean::cnstr_set(x_131, 1, x_126);
if (lean::is_scalar(x_114)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_114;
}
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_128);
if (lean::is_scalar(x_109)) {
 x_133 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_133 = x_109;
}
lean::cnstr_set(x_133, 0, x_132);
return x_133;
}
}
}
}
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
x_29 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_22);
x_30 = l_lean_elaborator_old__elab__command(x_0, x_29, x_1, x_24);
return x_30;
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
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string("#check");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
return x_7;
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
x_33 = l_list_append___main___rarg(x_28, x_30);
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
x_34 = l_list_append___main___rarg(x_28, x_33);
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
obj* l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_5);
x_12 = l_list_map___main___at_lean_elaborator_export_elaborate___spec__1(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
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
obj* _init_l_lean_elaborator_init__quot_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string("init_quot");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
x_7 = l_lean_kvmap_set__name(x_0, x_3, x_6);
x_8 = l_lean_elaborator_dummy;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(10, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_8);
return x_10;
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
unsigned char x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
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
unsigned char x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
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
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_10);
lean::dec(x_76);
x_79 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_79, 0, x_28);
lean::cnstr_set(x_79, 1, x_30);
lean::cnstr_set(x_79, 2, x_32);
lean::cnstr_set(x_79, 3, x_34);
lean::cnstr_set(x_79, 4, x_36);
lean::cnstr_set(x_79, 5, x_38);
lean::cnstr_set(x_79, 6, x_15);
x_80 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_80, 0, x_20);
lean::cnstr_set(x_80, 1, x_22);
lean::cnstr_set(x_80, 2, x_24);
lean::cnstr_set(x_80, 3, x_26);
lean::cnstr_set(x_80, 4, x_79);
lean::cnstr_set(x_80, 5, x_41);
lean::cnstr_set(x_80, 6, x_43);
lean::cnstr_set(x_80, 7, x_45);
lean::cnstr_set(x_80, 8, x_47);
lean::cnstr_set(x_80, 9, x_49);
lean::cnstr_set(x_80, 10, x_51);
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
x_84 = lean::cnstr_get(x_76, 0);
lean::inc(x_84);
lean::dec(x_76);
x_87 = l_lean_kvmap_set__string(x_15, x_10, x_84);
x_88 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_88, 0, x_28);
lean::cnstr_set(x_88, 1, x_30);
lean::cnstr_set(x_88, 2, x_32);
lean::cnstr_set(x_88, 3, x_34);
lean::cnstr_set(x_88, 4, x_36);
lean::cnstr_set(x_88, 5, x_38);
lean::cnstr_set(x_88, 6, x_87);
x_89 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_89, 0, x_20);
lean::cnstr_set(x_89, 1, x_22);
lean::cnstr_set(x_89, 2, x_24);
lean::cnstr_set(x_89, 3, x_26);
lean::cnstr_set(x_89, 4, x_88);
lean::cnstr_set(x_89, 5, x_41);
lean::cnstr_set(x_89, 6, x_43);
lean::cnstr_set(x_89, 7, x_45);
lean::cnstr_set(x_89, 8, x_47);
lean::cnstr_set(x_89, 9, x_49);
lean::cnstr_set(x_89, 10, x_51);
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
x_93 = lean::cnstr_get(x_17, 0);
lean::inc(x_93);
lean::dec(x_17);
x_96 = l_lean_parser_number_view_to__nat___main(x_93);
x_97 = l_lean_kvmap_set__nat(x_15, x_10, x_96);
x_98 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_98, 0, x_28);
lean::cnstr_set(x_98, 1, x_30);
lean::cnstr_set(x_98, 2, x_32);
lean::cnstr_set(x_98, 3, x_34);
lean::cnstr_set(x_98, 4, x_36);
lean::cnstr_set(x_98, 5, x_38);
lean::cnstr_set(x_98, 6, x_97);
x_99 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_99, 0, x_20);
lean::cnstr_set(x_99, 1, x_22);
lean::cnstr_set(x_99, 2, x_24);
lean::cnstr_set(x_99, 3, x_26);
lean::cnstr_set(x_99, 4, x_98);
lean::cnstr_set(x_99, 5, x_41);
lean::cnstr_set(x_99, 6, x_43);
lean::cnstr_set(x_99, 7, x_45);
lean::cnstr_set(x_99, 8, x_47);
lean::cnstr_set(x_99, 9, x_49);
lean::cnstr_set(x_99, 10, x_51);
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
obj* x_10; obj* x_12; 
lean::dec(x_4);
x_10 = l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1;
lean::inc(x_10);
x_12 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_0, x_10, x_1, x_2, x_6);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_20; 
lean::dec(x_0);
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
lean::dec(x_4);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(x_17, x_1, x_2, x_6);
return x_20;
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
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; unsigned char x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
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
obj* l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_10, 0, x_9);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_16; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_16);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_with__current__command___rarg), 6, 5);
lean::closure_set(x_20, 0, x_11);
lean::closure_set(x_20, 1, x_16);
lean::closure_set(x_20, 2, x_1);
lean::closure_set(x_20, 3, x_2);
lean::closure_set(x_20, 4, x_3);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___lambda__1), 4, 3);
lean::closure_set(x_21, 0, x_13);
lean::closure_set(x_21, 1, x_1);
lean::closure_set(x_21, 2, x_2);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_23, 0, x_20);
lean::closure_set(x_23, 1, x_22);
return x_23;
}
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
obj* l_lean_elaborator_commands_elaborate___main(unsigned char x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_6);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_1, x_9);
lean::dec(x_9);
lean::dec(x_1);
x_13 = l_lean_elaborator_current__command___rarg(x_4);
x_14 = lean::box(x_0);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__4___boxed), 5, 4);
lean::closure_set(x_15, 0, x_2);
lean::closure_set(x_15, 1, x_3);
lean::closure_set(x_15, 2, x_14);
lean::closure_set(x_15, 3, x_10);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_17, 0, x_13);
lean::closure_set(x_17, 1, x_16);
return x_17;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_1);
lean::dec(x_6);
x_20 = l_lean_elaborator_current__command___rarg(x_4);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__5), 3, 2);
lean::closure_set(x_21, 0, x_2);
lean::closure_set(x_21, 1, x_3);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_23, 0, x_20);
lean::closure_set(x_23, 1, x_22);
return x_23;
}
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
obj* l_lean_elaborator_commands_elaborate___main___lambda__2(unsigned char x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_lean_elaborator_commands_elaborate___main___lambda__3(unsigned char x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_lean_elaborator_commands_elaborate___main___lambda__4(obj* x_0, obj* x_1, unsigned char x_2, obj* x_3, obj* x_4) {
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
obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_5);
lean::dec(x_14);
lean::dec(x_9);
x_18 = lean::box(0);
lean::inc(x_1);
lean::inc(x_0);
x_21 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_18, x_0, x_1, x_7);
x_22 = lean::box(x_2);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 5, 4);
lean::closure_set(x_23, 0, x_22);
lean::closure_set(x_23, 1, x_3);
lean::closure_set(x_23, 2, x_0);
lean::closure_set(x_23, 3, x_1);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_24, 0, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_25, 0, x_21);
lean::closure_set(x_25, 1, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_14, 0);
lean::inc(x_26);
lean::dec(x_14);
x_29 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2;
x_30 = lean::name_dec_eq(x_26, x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_32; obj* x_33; 
lean::dec(x_30);
x_32 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3;
x_33 = lean::name_dec_eq(x_26, x_32);
lean::dec(x_26);
if (lean::obj_tag(x_33) == 0)
{
obj* x_38; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_33);
x_38 = lean::box(0);
lean::inc(x_1);
lean::inc(x_0);
x_41 = l_lean_parser_rec__t_recurse___at_lean_elaborator_command_elaborate___spec__1(x_38, x_0, x_1, x_7);
x_42 = lean::box(x_2);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_commands_elaborate___main___lambda__3___boxed), 5, 4);
lean::closure_set(x_43, 0, x_42);
lean::closure_set(x_43, 1, x_3);
lean::closure_set(x_43, 2, x_0);
lean::closure_set(x_43, 3, x_1);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_44, 0, x_43);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_45, 0, x_41);
lean::closure_set(x_45, 1, x_44);
return x_45;
}
else
{
lean::dec(x_3);
lean::dec(x_33);
if (x_2 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_51 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_9;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_7);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_54, 0, x_53);
return x_54;
}
else
{
obj* x_56; obj* x_58; 
lean::dec(x_9);
x_56 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4;
lean::inc(x_56);
x_58 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_5, x_56, x_0, x_1, x_7);
return x_58;
}
}
}
else
{
lean::dec(x_30);
lean::dec(x_3);
lean::dec(x_26);
if (x_2 == 0)
{
obj* x_63; obj* x_65; 
lean::dec(x_9);
x_63 = l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5;
lean::inc(x_63);
x_65 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_5, x_63, x_0, x_1, x_7);
return x_65;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_69 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_9;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_7);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_72, 0, x_71);
return x_72;
}
}
}
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
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("end");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("module");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("eoi");
x_8 = lean::name_mk_string(x_6, x_7);
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
obj* _init_l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("commands.elaborate: out of fuel");
return x_0;
}
}
obj* l_lean_elaborator_commands_elaborate___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate___main(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate___main___lambda__2(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate___main___lambda__3(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate___main___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = l_lean_elaborator_commands_elaborate___main___lambda__4(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_elaborator_commands_elaborate(unsigned char x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_lean_elaborator_commands_elaborate(x_5, x_1, x_2, x_3, x_4);
return x_6;
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
lean::dec(x_16);
if (lean::obj_tag(x_1) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_9;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_7);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_26, 0, x_25);
return x_26;
}
else
{
obj* x_28; 
lean::dec(x_9);
x_28 = lean::box(0);
x_10 = x_28;
goto lbl_11;
}
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_16, 0);
lean::inc(x_29);
lean::dec(x_16);
if (lean::obj_tag(x_1) == 0)
{
obj* x_34; 
lean::dec(x_9);
lean::dec(x_29);
x_34 = lean::box(0);
x_10 = x_34;
goto lbl_11;
}
else
{
obj* x_35; obj* x_37; 
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
x_37 = lean::name_dec_eq(x_29, x_35);
lean::dec(x_35);
lean::dec(x_29);
if (lean::obj_tag(x_37) == 0)
{
obj* x_42; 
lean::dec(x_37);
lean::dec(x_9);
x_42 = lean::box(0);
x_10 = x_42;
goto lbl_11;
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_5);
lean::dec(x_37);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_49 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_9;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_7);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_52, 0, x_51);
return x_52;
}
}
}
lbl_11:
{
obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_10);
x_54 = l_lean_parser_command_end_has__view;
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
x_57 = lean::apply_1(x_55, x_5);
x_58 = l_lean_elaborator_end__scope___lambda__2___closed__1;
lean::inc(x_58);
x_60 = lean::string_append(x_58, x_0);
lean::dec(x_0);
x_62 = l_lean_elaborator_end__scope___lambda__2___closed__2;
x_63 = lean::string_append(x_60, x_62);
x_64 = lean::box(0);
x_65 = l_option_get__or__else___main___rarg(x_1, x_64);
x_66 = l_lean_name_to__string___closed__1;
lean::inc(x_66);
x_68 = l_lean_name_to__string__with__sep___main(x_66, x_65);
x_69 = lean::string_append(x_63, x_68);
lean::dec(x_68);
x_71 = l_char_has__repr___closed__1;
x_72 = lean::string_append(x_69, x_71);
x_73 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_57, x_72, x_2, x_3, x_7);
return x_73;
}
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
obj* _init_l_lean_elaborator_section_elaborate___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("section");
return x_0;
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
obj* l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_5; obj* x_6; obj* x_7; 
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
obj* _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_yield__to__outside), 2, 0);
return x_0;
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
obj* _init_l_lean_elaborator_namespace_elaborate___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("namespace");
return x_0;
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
obj* l_lean_elaborator_locally___at_lean_elaborator_namespace_elaborate___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_6; obj* x_7; obj* x_8; 
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
obj* _init_l_lean_elaborator_elaborators() {
_start:
{
obj* x_0; 
x_0 = l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1;
lean::inc(x_0);
return x_0;
}
}
obj* l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; unsigned char x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; unsigned char x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
unsigned char x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
unsigned char x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_elaborator_elaborators___spec__4(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
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
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_rbnode_insert___at_lean_elaborator_elaborators___spec__3(x_0, x_8, x_10);
x_0 = x_13;
x_1 = x_5;
goto _start;
}
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
unsigned char l_lean_elaborator_is__open__namespace___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = lean::name_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_9; obj* x_12; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 4);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 4);
lean::inc(x_9);
lean::inc(x_1);
x_12 = l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(x_1, x_9);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_17; unsigned char x_18; 
lean::dec(x_12);
x_14 = lean::cnstr_get(x_6, 5);
lean::inc(x_14);
lean::dec(x_6);
x_17 = l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(x_1, x_14);
x_18 = lean::unbox(x_17);
lean::dec(x_17);
if (x_18 == 0)
{
unsigned char x_20; 
x_20 = 0;
return x_20;
}
else
{
unsigned char x_21; 
x_21 = 1;
return x_21;
}
}
else
{
unsigned char x_25; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_12);
x_25 = 1;
return x_25;
}
}
else
{
unsigned char x_29; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_29 = 1;
return x_29;
}
}
}
obj* l_list_decidable__mem___main___at_lean_elaborator_is__open__namespace___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::name_dec_eq(x_0, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_10) == 0)
{
lean::dec(x_10);
x_1 = x_7;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_10);
lean::dec(x_7);
lean::dec(x_0);
x_17 = lean::box(1);
return x_17;
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_is__open__namespace___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
unsigned char x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 0;
x_5 = lean::box(x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_14; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean::cnstr_get(x_11, 2);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::name_dec_eq(x_14, x_0);
lean::dec(x_14);
if (lean::obj_tag(x_17) == 0)
{
lean::dec(x_17);
x_1 = x_8;
goto _start;
}
else
{
unsigned char x_24; obj* x_25; 
lean::dec(x_8);
lean::dec(x_17);
lean::dec(x_0);
x_24 = 1;
x_25 = lean::box(x_24);
return x_25;
}
}
}
}
obj* l_lean_elaborator_is__open__namespace___main___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; 
x_2 = l_lean_elaborator_is__open__namespace___main(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char l_lean_elaborator_is__open__namespace(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; 
x_2 = l_lean_elaborator_is__open__namespace___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_elaborator_is__open__namespace___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; 
x_2 = l_lean_elaborator_is__open__namespace(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
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
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_lean_name_append___main(x_8, x_0);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_21; 
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_15 = x_2;
}
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 2);
lean::inc(x_18);
lean::dec(x_16);
x_21 = lean::name_dec_eq(x_0, x_18);
lean::dec(x_18);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_28; unsigned char x_29; 
lean::dec(x_21);
x_24 = lean::cnstr_get(x_13, 2);
lean::inc(x_24);
lean::dec(x_13);
lean::inc(x_0);
x_28 = l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(x_0, x_24);
x_29 = lean::unbox(x_28);
lean::dec(x_28);
if (x_29 == 0)
{
obj* x_34; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_15);
x_34 = lean::box(0);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_41; obj* x_42; 
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
lean::dec(x_1);
x_38 = lean::cnstr_get(x_35, 2);
lean::inc(x_38);
lean::dec(x_35);
x_41 = l_lean_name_append___main(x_38, x_0);
if (lean::is_scalar(x_15)) {
 x_42 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_42 = x_15;
}
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
}
else
{
obj* x_45; obj* x_48; obj* x_51; obj* x_52; 
lean::dec(x_21);
lean::dec(x_13);
x_45 = lean::cnstr_get(x_1, 0);
lean::inc(x_45);
lean::dec(x_1);
x_48 = lean::cnstr_get(x_45, 2);
lean::inc(x_48);
lean::dec(x_45);
x_51 = l_lean_name_append___main(x_48, x_0);
if (lean::is_scalar(x_15)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_15;
}
lean::cnstr_set(x_52, 0, x_51);
return x_52;
}
}
}
}
obj* l_list_foldr___main___at_lean_elaborator_match__open__spec___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
unsigned char x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 0;
x_5 = lean::box(x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_14; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean::name_dec_eq(x_0, x_11);
lean::dec(x_11);
if (lean::obj_tag(x_14) == 0)
{
lean::dec(x_14);
x_1 = x_8;
goto _start;
}
else
{
unsigned char x_21; obj* x_22; 
lean::dec(x_8);
lean::dec(x_14);
lean::dec(x_0);
x_21 = 1;
x_22 = lean::box(x_21);
return x_22;
}
}
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
obj* x_11; obj* x_15; 
lean::dec(x_9);
x_11 = lean::cnstr_get(x_4, 4);
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_15 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(x_0, x_2, x_11);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_20; obj* x_21; obj* x_24; unsigned char x_25; obj* x_28; obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_38; obj* x_39; obj* x_40; obj* x_42; 
x_16 = l_lean_elaborator_resolve__context___main___closed__1;
x_17 = lean::box(0);
lean::inc(x_16);
lean::inc(x_0);
x_20 = l_lean_name_replace__prefix___main(x_0, x_16, x_17);
x_21 = lean::cnstr_get(x_2, 8);
lean::inc(x_21);
lean::inc(x_20);
x_24 = lean_environment_contains(x_21, x_20);
x_25 = lean::unbox(x_24);
lean::dec(x_24);
lean::inc(x_0);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_match__open__spec), 2, 1);
lean::closure_set(x_28, 0, x_0);
x_29 = lean::cnstr_get(x_4, 5);
lean::inc(x_29);
lean::dec(x_4);
x_32 = l_list_filter__map___main___rarg(x_28, x_29);
lean::inc(x_2);
x_34 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(x_2, x_32);
x_35 = lean::cnstr_get(x_2, 3);
lean::inc(x_35);
lean::inc(x_2);
x_38 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__3(x_2, x_35);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_resolve__context___main___lambda__1), 2, 1);
lean::closure_set(x_39, 0, x_0);
x_40 = l_list_filter__map___main___rarg(x_39, x_38);
lean::inc(x_2);
x_42 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(x_2, x_40);
if (x_25 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_20);
x_44 = l_list_append___main___rarg(x_15, x_34);
x_45 = l_list_append___main___rarg(x_44, x_42);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_2);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_20);
lean::cnstr_set(x_48, 1, x_15);
x_49 = l_list_append___main___rarg(x_48, x_34);
x_50 = l_list_append___main___rarg(x_49, x_42);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_2);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
return x_52;
}
}
else
{
obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_4);
x_54 = lean::cnstr_get(x_15, 0);
lean::inc(x_54);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_56 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_56 = x_15;
}
x_57 = l_lean_name_append___main(x_54, x_0);
x_58 = lean::box(0);
if (lean::is_scalar(x_56)) {
 x_59 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_59 = x_56;
}
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_2);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
return x_61;
}
}
else
{
obj* x_64; obj* x_67; obj* x_69; obj* x_70; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_4);
lean::dec(x_0);
x_64 = lean::cnstr_get(x_9, 0);
lean::inc(x_64);
lean::dec(x_9);
x_67 = lean::cnstr_get(x_64, 1);
lean::inc(x_67);
if (lean::is_shared(x_64)) {
 lean::dec(x_64);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_69 = x_64;
}
x_70 = lean::cnstr_get(x_67, 0);
lean::inc(x_70);
lean::dec(x_67);
x_73 = lean::box(0);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set(x_74, 1, x_73);
if (lean::is_scalar(x_69)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_69;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_2);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
}
}
obj* _init_l_lean_elaborator_resolve__context___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_root_");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_14; obj* x_15; unsigned char x_16; 
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
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_9);
lean::dec(x_5);
x_2 = x_7;
goto _start;
}
else
{
obj* x_21; obj* x_22; 
x_21 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__1(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_5);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; unsigned char x_12; 
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
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
lean::dec(x_7);
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_17; obj* x_18; 
x_17 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__2(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_7;
}
lean::cnstr_set(x_18, 0, x_3);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; unsigned char x_11; 
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; unsigned char x_12; 
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
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
lean::dec(x_7);
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_17; obj* x_18; 
x_17 = l_list_filter___main___at_lean_elaborator_resolve__context___main___spec__4(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_7;
}
lean::cnstr_set(x_18, 0, x_3);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
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
obj* l_lean_elaborator_preresolve___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
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
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_8 = x_0;
}
lean::inc(x_6);
x_10 = l_lean_elaborator_mangle__ident(x_6);
x_11 = l_lean_elaborator_resolve__context___main(x_10, x_1, x_2);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_6);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_16 = x_11;
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
obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_20 = x_11;
}
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_18, 1);
lean::inc(x_23);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 x_25 = x_18;
}
x_26 = lean::cnstr_get(x_6, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_6, 1);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_6, 2);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_6, 3);
lean::inc(x_32);
x_34 = l_list_append___main___rarg(x_21, x_32);
x_35 = lean::cnstr_get(x_6, 4);
lean::inc(x_35);
lean::dec(x_6);
x_38 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_38, 0, x_26);
lean::cnstr_set(x_38, 1, x_28);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 3, x_34);
lean::cnstr_set(x_38, 4, x_35);
if (lean::is_scalar(x_8)) {
 x_39 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_39 = x_8;
}
lean::cnstr_set(x_39, 0, x_38);
if (lean::is_scalar(x_25)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_25;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_23);
if (lean::is_scalar(x_20)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_20;
}
lean::cnstr_set(x_41, 0, x_40);
return x_41;
}
}
case 2:
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; 
x_42 = lean::cnstr_get(x_0, 0);
lean::inc(x_42);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_44 = x_0;
}
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
x_47 = l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(x_45, x_1, x_2);
if (lean::obj_tag(x_47) == 0)
{
obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_44);
lean::dec(x_42);
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_52 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 x_52 = x_47;
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
obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_54 = lean::cnstr_get(x_47, 0);
lean::inc(x_54);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_56 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 x_56 = x_47;
}
x_57 = lean::cnstr_get(x_54, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_54, 1);
lean::inc(x_59);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 lean::cnstr_release(x_54, 1);
 x_61 = x_54;
}
x_62 = lean::cnstr_get(x_42, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_42, 2);
lean::inc(x_64);
lean::dec(x_42);
x_67 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_67, 0, x_62);
lean::cnstr_set(x_67, 1, x_57);
lean::cnstr_set(x_67, 2, x_64);
if (lean::is_scalar(x_44)) {
 x_68 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_68 = x_44;
}
lean::cnstr_set(x_68, 0, x_67);
if (lean::is_scalar(x_61)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_61;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_59);
if (lean::is_scalar(x_56)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_56;
}
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
default:
{
obj* x_72; obj* x_73; 
lean::dec(x_1);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_0);
lean::cnstr_set(x_72, 1, x_2);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
}
}
}
obj* l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_12 = x_0;
}
lean::inc(x_1);
x_14 = l_lean_elaborator_preresolve___main(x_8, x_1, x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_20 = x_14;
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
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_24 = x_14;
}
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_29 = x_22;
}
x_30 = l_list_mmap___main___at_lean_elaborator_preresolve___main___spec__1(x_10, x_1, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_37; 
lean::dec(x_12);
lean::dec(x_25);
lean::dec(x_29);
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
if (lean::is_scalar(x_24)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_24;
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
if (lean::is_scalar(x_12)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_12;
}
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_41);
if (lean::is_scalar(x_29)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_29;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_24)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_24;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
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
obj* _init_l_lean_elaborator_run___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; unsigned char x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_17; 
x_0 = lean::box(0);
x_1 = lean::mk_string("trace");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string("as_messages");
x_5 = lean::name_mk_string(x_3, x_4);
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
obj* x_0; 
x_0 = lean_environment_empty;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_elaborator_run___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_ngen");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("fixme");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_elaborator_run___closed__4() {
_start:
{
unsigned char x_0; obj* x_1; obj* x_2; obj* x_4; 
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
obj* _init_l_lean_elaborator_run___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; unsigned char x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
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
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
lean::dec(x_5);
x_11 = l_lean_name_to__string___closed__1;
lean::inc(x_11);
x_13 = l_lean_name_to__string__with__sep___main(x_11, x_0);
x_14 = l_lean_elaborator_run___lambda__2___closed__1;
lean::inc(x_14);
x_16 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_18 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_1, x_16, x_2, x_3, x_7);
return x_18;
}
else
{
obj* x_21; obj* x_24; 
lean::dec(x_1);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
lean::dec(x_5);
x_24 = lean::apply_3(x_21, x_2, x_3, x_7);
return x_24;
}
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
obj* l_lean_elaborator_run___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
lean::dec(x_1);
lean::inc(x_0);
x_7 = l_lean_parser_syntax_to__format___main(x_0);
x_8 = lean::mk_nat_obj(80u);
x_9 = l_lean_format_pretty(x_7, x_8);
x_10 = l_lean_elaborator_run___lambda__4___closed__1;
lean::inc(x_10);
x_12 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_14 = l_lean_expander_error___at_lean_elaborator_no__kind_elaborate___spec__1___rarg(x_0, x_12, x_2, x_3, x_4);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_lean_elaborator_elaborators;
lean::inc(x_18);
lean::inc(x_21);
x_24 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_21, x_18);
lean::inc(x_4);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_4);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__2), 5, 4);
lean::closure_set(x_29, 0, x_18);
lean::closure_set(x_29, 1, x_0);
lean::closure_set(x_29, 2, x_2);
lean::closure_set(x_29, 3, x_3);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_elaborator_command_elaborate___spec__3___rarg), 2, 1);
lean::closure_set(x_30, 0, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_31, 0, x_28);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_elaborator_run___lambda__3), 2, 1);
lean::closure_set(x_32, 0, x_4);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_32);
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
obj* l___private_3693562977__run__aux___at_lean_elaborator_run___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l___private_3693562977__run__aux___main___rarg(x_0, x_1, x_2, x_3);
x_7 = lean::apply_2(x_6, x_4, x_5);
return x_7;
}
}
obj* l_lean_parser_rec__t_run___at_lean_elaborator_run___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3693562977__run__aux___at_lean_elaborator_run___spec__6), 6, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_2);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::apply_3(x_0, x_6, x_4, x_5);
return x_7;
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
 l_lean_elaborator_mk__eqns___closed__1 = _init_l_lean_elaborator_mk__eqns___closed__1();
 l_lean_elaborator_mk__eqns___closed__2 = _init_l_lean_elaborator_mk__eqns___closed__2();
 l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1 = _init_l_list_map___main___at_lean_elaborator_mk__eqns___spec__1___closed__1();
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
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__4___closed__1();
 l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_to__pexpr___main___spec__8___closed__1();
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
 l_lean_elaborator_command__parser__config_register__notation__parser___closed__1 = _init_l_lean_elaborator_command__parser__config_register__notation__parser___closed__1();
 l_lean_elaborator_command__parser__config_register__notation__parser___closed__2 = _init_l_lean_elaborator_command__parser__config_register__notation__parser___closed__2();
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__1();
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__2();
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__3();
 l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4 = _init_l_list_mmap___main___at_lean_elaborator_command__parser__config_register__notation__parser___spec__2___closed__4();
 l_lean_elaborator_yield__to__outside___rarg___closed__1 = _init_l_lean_elaborator_yield__to__outside___rarg___closed__1();
 l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1 = _init_l_lean_elaborator_yield__to__outside___rarg___lambda__2___closed__1();
 l_lean_elaborator_postprocess__notation__spec___closed__1 = _init_l_lean_elaborator_postprocess__notation__spec___closed__1();
 l_lean_elaborator_match__spec___closed__1 = _init_l_lean_elaborator_match__spec___closed__1();
 l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_match__spec___spec__1___closed__1();
 l_lean_elaborator_notation_elaborate__aux___closed__1 = _init_l_lean_elaborator_notation_elaborate__aux___closed__1();
 l_lean_elaborator_mk__notation__kind___rarg___closed__1 = _init_l_lean_elaborator_mk__notation__kind___rarg___closed__1();
 l_lean_elaborator_notation_elaborate___closed__1 = _init_l_lean_elaborator_notation_elaborate___closed__1();
 l_lean_elaborator_notation_elaborate___closed__2 = _init_l_lean_elaborator_notation_elaborate___closed__2();
 l_lean_elaborator_universe_elaborate___closed__1 = _init_l_lean_elaborator_universe_elaborate___closed__1();
 l_lean_elaborator_universe_elaborate___closed__2 = _init_l_lean_elaborator_universe_elaborate___closed__2();
 l_lean_elaborator_attribute_elaborate___closed__1 = _init_l_lean_elaborator_attribute_elaborate___closed__1();
 l_lean_elaborator_attribute_elaborate___closed__2 = _init_l_lean_elaborator_attribute_elaborate___closed__2();
 l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__1();
 l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2 = _init_l_list_mmap___main___at_lean_elaborator_attribute_elaborate___spec__1___closed__2();
 l_lean_elaborator_check_elaborate___closed__1 = _init_l_lean_elaborator_check_elaborate___closed__1();
 l_lean_elaborator_init__quot_elaborate___closed__1 = _init_l_lean_elaborator_init__quot_elaborate___closed__1();
 l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1 = _init_l_lean_elaborator_no__kind_elaborate___lambda__1___closed__1();
 l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1 = _init_l_list_mmap_x_27___main___at_lean_elaborator_no__kind_elaborate___spec__2___closed__1();
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__1();
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__2();
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__3();
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__4();
 l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5 = _init_l_lean_elaborator_commands_elaborate___main___lambda__4___closed__5();
 l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1 = _init_l_lean_elaborator_commands_elaborate___main___lambda__5___closed__1();
 l_lean_elaborator_end__scope___lambda__2___closed__1 = _init_l_lean_elaborator_end__scope___lambda__2___closed__1();
 l_lean_elaborator_end__scope___lambda__2___closed__2 = _init_l_lean_elaborator_end__scope___lambda__2___closed__2();
 l_lean_elaborator_end__scope___lambda__3___closed__1 = _init_l_lean_elaborator_end__scope___lambda__3___closed__1();
 l_lean_elaborator_section_elaborate___closed__1 = _init_l_lean_elaborator_section_elaborate___closed__1();
 l_lean_elaborator_section_elaborate___lambda__1___closed__1 = _init_l_lean_elaborator_section_elaborate___lambda__1___closed__1();
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__1();
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___closed__2();
 l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1 = _init_l_lean_elaborator_locally___at_lean_elaborator_section_elaborate___spec__2___lambda__4___closed__1();
 l_lean_elaborator_namespace_elaborate___closed__1 = _init_l_lean_elaborator_namespace_elaborate___closed__1();
 l_lean_elaborator_namespace_elaborate___lambda__1___closed__1 = _init_l_lean_elaborator_namespace_elaborate___lambda__1___closed__1();
 l_lean_elaborator_elaborators = _init_l_lean_elaborator_elaborators();
 l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1 = _init_l_rbmap_from__list___at_lean_elaborator_elaborators___spec__1();
 l_lean_elaborator_resolve__context___main___closed__1 = _init_l_lean_elaborator_resolve__context___main___closed__1();
 l_lean_elaborator_max__recursion = _init_l_lean_elaborator_max__recursion();
 l_lean_elaborator_max__commands = _init_l_lean_elaborator_max__commands();
 l_lean_elaborator_run___closed__1 = _init_l_lean_elaborator_run___closed__1();
 l_lean_elaborator_run___closed__2 = _init_l_lean_elaborator_run___closed__2();
 l_lean_elaborator_run___closed__3 = _init_l_lean_elaborator_run___closed__3();
 l_lean_elaborator_run___closed__4 = _init_l_lean_elaborator_run___closed__4();
 l_lean_elaborator_run___closed__5 = _init_l_lean_elaborator_run___closed__5();
 l_lean_elaborator_run___closed__6 = _init_l_lean_elaborator_run___closed__6();
 l_lean_elaborator_run___closed__7 = _init_l_lean_elaborator_run___closed__7();
 l_lean_elaborator_run___lambda__1___closed__1 = _init_l_lean_elaborator_run___lambda__1___closed__1();
 l_lean_elaborator_run___lambda__2___closed__1 = _init_l_lean_elaborator_run___lambda__2___closed__1();
 l_lean_elaborator_run___lambda__4___closed__1 = _init_l_lean_elaborator_run___lambda__4___closed__1();
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__1();
 l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2 = _init_l_lean_elaborator_ordered__rbmap_empty___at_lean_elaborator_run___spec__2();
}
